"""Independent, replayable HIP4 audit ledger. No exchange credentials or order execution.

FIFO costs use actual fills, not order quotes or exchange closedPnl. SQLite keeps
immutable source events; reports are reproducible projections, never legacy state.
All amounts in the public report are decimal strings. An unresolved report cannot
approve execution. The executor integration is deliberately disabled.
"""
import hashlib
import json
import sqlite3
from collections import defaultdict, deque
from itertools import groupby
from decimal import Decimal, InvalidOperation, localcontext
from pathlib import Path

ZERO = Decimal('0')
LIVE_GATE_REASON = ('HIP4 paused: independent audit ledger is not integrated with '
                    'the live state machine; reconciliation and execution review required')


def require_live_integration():
    raise RuntimeError(LIVE_GATE_REASON)


def dec(value):
    try:
        n = Decimal(str(value))
    except (InvalidOperation, ValueError, TypeError) as exc:
        raise ValueError('invalid decimal') from exc
    if not n.is_finite():
        raise ValueError('nonfinite decimal')
    return n


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=False)


V2_IDENTITY_FIELDS = ('experiment_id', 'owner', 'experiment_start_ms',
                      'opening_baseline', 'config_fingerprint')


def fingerprint(value):
    return hashlib.sha256(canonical(value).encode()).hexdigest()


def identity_fingerprint(identity):
    """Stable audit/view identity; v1 retains its full canonical fingerprint."""
    value = identity
    if identity.get('identity_version', 1) == 2:
        value = {key: identity[key] for key in V2_IDENTITY_FIELDS}
        value['identity_version'] = 2
    return fingerprint(value)


def _validate_v2_identity(identity):
    if any(key not in identity for key in V2_IDENTITY_FIELDS):
        raise ValueError('v2 immutable experiment identity required')
    start = identity['experiment_start_ms']
    if type(start) is not int or start < 0:
        raise ValueError('invalid experiment start time')
    if any(not identity[key] for key in ('opening_baseline', 'config_fingerprint')):
        raise ValueError('v2 baseline and config fingerprint required')
    windows = identity.get('authorization_windows')
    if not isinstance(windows, list) or not windows:
        raise ValueError('v2 authorization windows required')
    markets, previous = set(), None
    for window in windows:
        if not isinstance(window, dict):
            raise ValueError('authorization window must be a mapping')
        at, end = window.get('at_ms'), window.get('end_ms')
        if (type(at) is not int or type(end) is not int or at < start
                or end <= at or (previous is not None and at <= previous)):
            raise ValueError('invalid authorization window time / validity')
        scope = window.get('markets')
        if (not isinstance(scope, list)
                or any(not isinstance(m, str) or not m.isascii() or not m.isdigit()
                       or str(int(m)) != m for m in scope)
                or len(set(scope)) != len(scope)):
            raise ValueError('invalid authorization window markets')
        if not isinstance(window.get('authorization_fingerprint'), str) or not window['authorization_fingerprint']:
            raise ValueError('authorization window fingerprint required')
        markets.update(scope)
        previous = at
    if identity.get('markets') != sorted(markets):
        raise ValueError('v2 markets must equal historical authorization union')


def _commitment_matches(identity, fill, evidence):
    submitted = evidence['submitted_at_ms']
    if (fill.get('dir') != 'Buy' or fill.get('side') != 'B'
            or coin_name(fill['coin']) != evidence['coin']
            or type(fill.get('time')) is not int or fill['time'] < submitted):
        return False
    matched = any(fill.get(key) is not None and evidence.get(key) is not None
                  and str(fill[key]) == str(evidence[key]) for key in ('oid', 'cloid'))
    # If both identifiers are present, neither may contradict the evidence.
    if not matched or any(fill.get(key) is not None and evidence.get(key) is not None
                          and str(fill[key]) != str(evidence[key])
                          for key in ('oid', 'cloid')):
        return False
    probe = dict(fill, time=submitted)
    return (dec(fill['px']) <= dec(evidence['limit_px'])
            and any(w['authorization_fingerprint'] == evidence['authorization_fingerprint']
                    and market_of_coin(evidence['coin']) in w['markets']
                    and w['at_ms'] <= submitted < w['end_ms']
                    and (i + 1 == len(identity['authorization_windows'])
                         or submitted < identity['authorization_windows'][i + 1]['at_ms'])
                    for i, w in enumerate(identity['authorization_windows']))
            and _v2_fill_authorized(identity, probe))


def _v2_fill_authorized(identity, fill, commitments=()):
    """Opening windows plus concrete durable commitments; historical exits persist."""
    time = fill.get('time')
    if type(time) is not int or time < identity['experiment_start_ms']:
        return False
    coin = coin_name(fill['coin'])
    if int(coin[1:]) % 10 not in (0, 1):
        return False
    market = str(int(coin[1:]) // 10)
    disposal = (fill.get('dir') in ('Sell', 'Merge Outcome', 'Settlement')
                and fill.get('side') == 'A')
    acquisition = (fill.get('dir') in ('Buy', 'Split Outcome')
                   and fill.get('side') == 'B')
    windows = identity['authorization_windows']
    for index, window in enumerate(windows):
        if market not in window['markets'] or time < window['at_ms']:
            continue
        if disposal:
            return True
        end = window['end_ms']
        if index + 1 < len(windows):
            end = min(end, windows[index + 1]['at_ms'])
        if acquisition and time < end:
            return True
    return any(_commitment_matches(identity, fill, evidence) for evidence in commitments)


def coin_name(value):
    value = str(value)
    if value.startswith(('#', '+')) and value[1:].isdigit():
        return '#' + value[1:]
    raise ValueError('not a HIP4 outcome coin')


def market_of_coin(coin):
    """Outcome coin '#217461' -> market id '21746'."""
    return str(int(coin_name(coin)[1:]) // 10)


def normalized_coins(mapping):
    """Reject aliases of the same inventory entry instead of overwriting it."""
    result = {}
    for raw_coin, value in mapping.items():
        coin = coin_name(raw_coin)
        if coin in result:
            raise ValueError('duplicate inventory coin alias: ' + coin)
        result[coin] = value
    return result


def normalize_fill(raw):
    fill = dict(raw)
    fill['coin'] = coin_name(fill['coin'])
    if str(fill.get('feeToken', '')).startswith(('#', '+')):
        fill['feeToken'] = coin_name(fill['feeToken'])
    return fill


def event_id(owner, fill):
    coin = coin_name(fill['coin'])
    if not fill.get('hash') or fill.get('tid') is None:
        raise ValueError('fill requires exchange hash, tid and coin')
    # A merge's two legs share hash but have distinct tid / coin. Never use oid,
    # timestamps alone, a local round number, or action acknowledgements.
    return canonical([owner.lower(), str(fill['hash']).lower(), str(fill['tid']), coin])


class Ledger:
    def __init__(self, path, owner):
        self.owner = owner.lower()
        self.db = sqlite3.connect(str(path))
        self.db.execute('CREATE TABLE IF NOT EXISTS metadata (name TEXT PRIMARY KEY, value TEXT NOT NULL)')
        self.db.execute('CREATE TABLE IF NOT EXISTS events (id TEXT PRIMARY KEY, payload TEXT NOT NULL)')
        self.db.execute('CREATE TABLE IF NOT EXISTS fill_source_evidence (id TEXT PRIMARY KEY, payload TEXT NOT NULL)')
        self.db.execute('CREATE TABLE IF NOT EXISTS fill_source_responses (id TEXT PRIMARY KEY, payload TEXT NOT NULL)')
        self.db.execute('CREATE TABLE IF NOT EXISTS auxiliary (id TEXT PRIMARY KEY, payload TEXT NOT NULL)')
        self.db.execute('CREATE TABLE IF NOT EXISTS order_commitments (id TEXT PRIMARY KEY, payload TEXT NOT NULL)')
        self.db.execute('CREATE TABLE IF NOT EXISTS order_bindings (id TEXT PRIMARY KEY, oid TEXT UNIQUE NOT NULL)')
        row = self.db.execute("SELECT value FROM metadata WHERE name='owner'").fetchone()
        if row and row[0] != self.owner:
            self.db.close()
            raise ValueError('ledger owner mismatch')
        self.db.execute("INSERT OR IGNORE INTO metadata VALUES ('owner', ?)", (self.owner,))
        self.db.commit()

    def bind_experiment(self, identity):
        """Bind a new experiment or append v2 authorization without rewriting history."""
        if not identity.get('experiment_id') or identity.get('owner') != self.owner:
            raise ValueError('ledger experiment identity required')
        version = identity.get('identity_version', 1)
        if type(version) is not int or version not in (1, 2):
            raise ValueError('unsupported ledger identity version')
        if version == 2:
            _validate_v2_identity(identity)
        payload = canonical(identity)
        with self.db:
            previous = self._stored_identity()
            if previous is not None:
                if previous.get('identity_version', 1) != version:
                    raise ValueError('ledger experiment identity version mismatch; no migration')
                if version == 2:
                    old_windows = previous['authorization_windows']
                    if (any(previous[key] != identity[key] for key in V2_IDENTITY_FIELDS)
                            or identity['authorization_windows'][:len(old_windows)] != old_windows):
                        raise ValueError('ledger experiment identity mismatch; authorization history is append-only')
                elif canonical(previous) != payload:
                    raise ValueError('ledger experiment identity mismatch')
            elif (self.db.execute('SELECT 1 FROM events LIMIT 1').fetchone()
                    or self.db.execute('SELECT 1 FROM auxiliary LIMIT 1').fetchone()):
                raise ValueError('unidentified nonempty ledger refused; preserve original database')
            # Check committed scope too: a new window cannot bless polluted rows.
            for (raw,) in self.db.execute('SELECT payload FROM events'):
                fill = json.loads(raw)
                coin = coin_name(fill['coin'])
                if version == 2:
                    commitments = self._order_commitments()
                    allowed = (_v2_fill_authorized(previous or identity, fill, commitments)
                               and _v2_fill_authorized(identity, fill, commitments))
                else:
                    allowed = (market_of_coin(coin) in identity['markets']
                               and int(fill['time']) >= identity['experiment_start_ms'])
                if not allowed:
                    raise ValueError('existing ledger event outside experiment scope/baseline')
            if version == 2:
                for evidence in self._order_commitments():
                    probe = dict(evidence, time=evidence['submitted_at_ms'], dir='Buy',
                                 side='B', px=evidence['limit_px'])
                    if not _commitment_matches(identity, probe, evidence):
                        raise ValueError('new window invalidates committed order submission')
                self._check_committed_quantities(identity)
            self.db.execute("INSERT OR REPLACE INTO metadata VALUES ('experiment_identity', ?)",
                            (payload,))

    def _order_commitments(self):
        records = []
        for key, raw in self.db.execute('SELECT id, payload FROM order_commitments'):
            evidence = json.loads(raw)
            binding = self.db.execute('SELECT oid FROM order_bindings WHERE id=?', (key,)).fetchone()
            if binding:
                evidence['oid'] = binding[0]
            records.append(evidence)
        return records

    def has_order_commitment(self, order_key):
        """该 cloid 的承诺是否已写入账本（只读，供回填幂等判断）。"""
        row = self.db.execute(
            'SELECT 1 FROM order_commitments WHERE id=?', (str(order_key),)).fetchone()
        return row is not None

    def register_order_commitment(self, evidence, *, source_owner):
        """Persist verified write-ahead Buy evidence before sending or narrowing scope."""
        identity = self._stored_identity()
        if (source_owner.lower() != self.owner or not identity
                or identity.get('identity_version') != 2):
            raise ValueError('matching owner and bound v2 identity required')
        record = dict(evidence)
        key = record.get('order_key')
        at = record.get('submitted_at_ms')
        if (not isinstance(key, str) or not key or type(at) is not int
                or not isinstance(record.get('authorization_fingerprint'), str)
                or not record['authorization_fingerprint']):
            raise ValueError('immutable order key, submission time and window required')
        record['coin'] = coin_name(record['coin'])
        if dec(record['sz']) <= 0 or dec(record['limit_px']) < 0:
            raise ValueError('invalid commitment size / limit price')
        if not record.get('cloid') and record.get('oid') is None:
            raise ValueError('exchange oid or durable cloid required')
        if record.get('cloid') is not None and (not isinstance(record['cloid'], str) or not record['cloid']):
            raise ValueError('invalid cloid')
        if record.get('oid') is not None:
            record['oid'] = self._order_id(record['oid'])
        probe = {'coin': record['coin'], 'time': at, 'dir': 'Buy', 'side': 'B'}
        # 2026-11-08 修复（与 c_runtime.order_commitment 同步）：
        # 原判据只认「当前生效窗口」，空窗口会挡住已授权市场。
        # 这里与 c_runtime 用同一套规则：先按原判据找，找不到再回退到
        # 「最近一个包含该市场且仍覆盖下单时刻」的窗口。时间边界不放宽。
        _ws = identity['authorization_windows']
        _mkt = market_of_coin(record['coin']) if record.get('coin') else None

        def _match(w):
            return (w['authorization_fingerprint'] == record['authorization_fingerprint']
                    and _mkt is not None and _mkt in (w.get('markets') or [])
                    and w['at_ms'] <= at < w['end_ms'])

        _hit = any(_match(w) and (i + 1 == len(_ws) or at < _ws[i + 1]['at_ms'])
                   for i, w in enumerate(_ws))
        if not _hit and _mkt is not None:
            _hit = any(_match(w) for w in reversed(_ws))
        if not _v2_fill_authorized(identity, probe) or not _hit:
            raise ValueError('order submission outside authorized opening window')
        payload = canonical(record)
        with self.db:
            old = self.db.execute('SELECT payload FROM order_commitments WHERE id=?', (key,)).fetchone()
            if old:
                if old[0] != payload:
                    raise ValueError('order commitment is immutable')
                return
            for existing in self._order_commitments():
                if any(record.get(k) is not None and existing.get(k) is not None
                       and str(record[k]) == str(existing[k]) for k in ('oid', 'cloid')):
                    raise ValueError('order identifier already belongs to another commitment')
            self.db.execute('INSERT INTO order_commitments VALUES (?, ?)', (key, payload))
            if record.get('oid') is not None:
                self.db.execute('INSERT INTO order_bindings VALUES (?, ?)', (key, record['oid']))
            self._check_committed_quantities(identity)

    @staticmethod
    def _order_id(oid):
        text = str(oid)
        if not text.isascii() or not text.isdigit() or str(int(text)) != text:
            raise ValueError('invalid exchange order id')
        return text

    def bind_order_id(self, order_key, oid, *, source_owner):
        """Bind an exchange-confirmed oid to an unknown submission's durable cloid."""
        if source_owner.lower() != self.owner:
            raise ValueError('order evidence owner mismatch')
        oid = self._order_id(oid)
        with self.db:
            if not self.db.execute('SELECT 1 FROM order_commitments WHERE id=?', (order_key,)).fetchone():
                raise ValueError('unknown order commitment')
            old = self.db.execute('SELECT oid FROM order_bindings WHERE id=?', (order_key,)).fetchone()
            if old:
                if old[0] != oid:
                    raise ValueError('order binding is immutable')
                return
            for existing in self._order_commitments():
                if existing['order_key'] != order_key and str(existing.get('oid')) == oid:
                    raise ValueError('order id already belongs to another commitment')
            self.db.execute('INSERT INTO order_bindings VALUES (?, ?)', (order_key, oid))
            self._check_committed_quantities(self._stored_identity())

    def _check_committed_quantities(self, identity):
        fills = [json.loads(row[0]) for row in self.db.execute('SELECT payload FROM events')]
        for evidence in self._order_commitments():
            total = ZERO
            for fill in fills:
                identified = any(fill.get(k) is not None and evidence.get(k) is not None
                                 and str(fill[k]) == str(evidence[k]) for k in ('oid', 'cloid'))
                if not identified:
                    continue
                if not _commitment_matches(identity, fill, evidence):
                    raise ValueError('fill contradicts committed order evidence')
                total += dec(fill['sz'])
            if total > dec(evidence['sz']):
                raise ValueError('fills exceed committed order size')

    def _stored_identity(self):
        row = self.db.execute("SELECT value FROM metadata WHERE name='experiment_identity'").fetchone()
        return json.loads(row[0]) if row else None

    def _ingest_scope_check(self, fill):
        identity = self._stored_identity()
        # v1 and unbound ledgers retain their original ingestion behavior.
        if identity and identity.get('identity_version', 1) == 2:
            if not _v2_fill_authorized(identity, fill, self._order_commitments()):
                raise ValueError('fill outside authorized experiment scope/baseline')

    def close(self):
        self.db.close()

    def fill_coverage(self):
        """Return only coverage tied to this durable experiment identity."""
        row = self.db.execute("SELECT value FROM metadata WHERE name='fill_coverage'").fetchone()
        if row is None:
            return None
        proof = json.loads(row[0])
        identity = self._stored_identity()
        if (not identity or proof.get('identity') != identity_fingerprint(identity)
                or proof.get('schema') != 1
                or proof.get('from_ms') != identity['experiment_start_ms']
                or type(proof.get('through_ms')) is not int
                or proof['through_ms'] < proof['from_ms']):
            raise ValueError('invalid ledger fill coverage identity / interval')
        if 'source_id' in proof:
            row = self.db.execute('SELECT payload FROM fill_source_evidence WHERE id=?',
                                  (proof['source_id'],)).fetchone()
            source = json.loads(row[0]) if row else None
            if (source is None or fingerprint(source) != proof['source_id']
                    or source.get('identity') != proof['identity']
                    or source['request']['user'].lower() != self.owner
                    or source['request']['endTime'] != proof['through_ms']):
                raise ValueError('invalid ledger fill source evidence')
            if 'response_blob_sha256' in source:
                self._fill_source_response(source['response_blob_sha256'])
                if (source['response_blob_sha256'] != source.get('response_sha256')
                        or 'response' in source):
                    raise ValueError('invalid ledger fill source response reference')
            elif fingerprint(source['response']) != source.get('response_sha256'):
                raise ValueError('invalid ledger fill source response hash')
        return proof

    def _fill_source_response(self, key):
        row = self.db.execute('SELECT payload FROM fill_source_responses WHERE id=?',
                              (key,)).fetchone()
        response = json.loads(row[0]) if row else None
        if not isinstance(response, list) or fingerprint(response) != key:
            raise ValueError('invalid ledger fill source response blob')
        return response

    def _advance_fill_coverage(self, interval):
        since, until = interval
        identity = self._stored_identity()
        previous = self.fill_coverage()
        frontier = previous['through_ms'] if previous else identity['experiment_start_ms']
        if (type(since) is not int or type(until) is not int
                or since < identity['experiment_start_ms'] or since > frontier
                or until < frontier or until < since):
            raise ValueError('REST fill coverage gap / clock regression')
        proof = {'schema': 1, 'identity': identity_fingerprint(identity),
                 'from_ms': identity['experiment_start_ms'], 'through_ms': until,
                 'last_query': {'start_ms': since, 'end_ms': until}}
        self.db.execute("INSERT OR REPLACE INTO metadata VALUES ('fill_coverage', ?)",
                        (canonical(proof),))

    def _record_fill_source(self, source, interval):
        from fill_history import validate_history
        identity = self._stored_identity()
        start, until = interval
        if start != identity['experiment_start_ms']:
            raise ValueError('source interval / identity mismatch')
        checked = validate_history(source['request'], source['response'], owner=self.owner,
                                   start=start, until=until, cap=source['cap'],
                                   bootstrap=source['mode'] == 'bootstrap')
        if checked != source:
            raise ValueError('source evidence content / hash mismatch')
        remote = {event_id(self.owner, f): canonical(normalize_fill(f))
                  for f in source['response'] if f['time'] >= start
                  and str(f['coin']).startswith(('#', '+'))
                  and market_of_coin(f['coin']) in identity['markets']}
        stored = dict(self.db.execute('SELECT id, payload FROM events'))
        # A self-consistent local ledger alone is never a source proof. Every
        # historical scoped remote row and every durable row must agree exactly.
        if remote != {key: canonical(normalize_fill(json.loads(raw)))
                      for key, raw in stored.items()}:
            raise ValueError('account history / durable experiment events mismatch')
        # Only the canonical response is shared across queries. Each request,
        # mode, identity and coverage endpoint keeps its own immutable evidence.
        response_key = source['response_sha256']
        self.db.execute('INSERT OR IGNORE INTO fill_source_responses VALUES (?, ?)',
                        (response_key, canonical(source['response'])))
        if self._fill_source_response(response_key) != source['response']:
            raise ValueError('conflicting ledger fill source response blob')
        envelope = dict(source, identity=identity_fingerprint(identity))
        envelope.pop('response')
        envelope['response_blob_sha256'] = response_key
        key = fingerprint(envelope)
        payload = canonical(envelope)
        self.db.execute('INSERT OR IGNORE INTO fill_source_evidence VALUES (?, ?)',
                        (key, payload))
        if self.db.execute('SELECT payload FROM fill_source_evidence WHERE id=?',
                           (key,)).fetchone()[0] != payload:
            raise ValueError('conflicting ledger fill source evidence')
        proof = self.fill_coverage()
        proof.update(source_id=key, semantics=source['semantics'])
        self.db.execute("UPDATE metadata SET value=? WHERE name='fill_coverage'",
                        (canonical(proof),))

    def ingest_fills(self, fills, *, dry=False, source_owner=None, coverage_interval=None,
                     coverage_source=None):
        if dry:
            return 0
        if source_owner is None or source_owner.lower() != self.owner:
            raise ValueError('explicit matching source owner required')
        added = 0
        with self.db:
            for raw in fills:
                fill = normalize_fill(raw)
                key = event_id(self.owner, fill)
                # Validate before any transaction is committed.
                if dec(fill['sz']) <= 0 or dec(fill['px']) < 0:
                    raise ValueError('invalid size / price')
                dec(fill['fee'])
                if not fill.get('feeToken') or not isinstance(fill.get('time'), int):
                    raise ValueError('feeToken and millisecond time required')
                payload = canonical(fill)
                self._ingest_scope_check(fill)
                prev = self.db.execute('SELECT payload FROM events WHERE id=?', (key,)).fetchone()
                if prev:
                    if canonical(normalize_fill(json.loads(prev[0]))) != payload:
                        raise ValueError('conflicting payload for stable event identity')
                    continue
                self.db.execute('INSERT INTO events VALUES (?, ?)', (key, payload))
                added += 1
            identity = self._stored_identity()
            if identity and identity.get('identity_version') == 2:
                self._check_committed_quantities(identity)
            if coverage_interval is not None:
                self._advance_fill_coverage(coverage_interval)
                if coverage_source is not None:
                    self._record_fill_source(coverage_source, coverage_interval)
        return added

    def ingest_auxiliary(self, events, *, source_owner, dry=False):
        """Persist separately evidenced rewards/transfers without trading PnL."""
        if dry:
            return 0
        if source_owner.lower() != self.owner:
            raise ValueError('auxiliary owner mismatch')
        added = 0
        with self.db:
            for event in events:
                if event.get('kind') not in ('reward', 'transfer') or not event.get('txhash') or event.get('event_index') is None:
                    raise ValueError('auxiliary event needs kind, txhash and event_index')
                if not event.get('token') or not event.get('evidence') or event.get('scope') != 'owner_hip4':
                    raise ValueError('scoped auxiliary evidence required')
                if event.get('status') not in ('received', 'confirmed_pending', 'unconfirmed'):
                    raise ValueError('explicit receipt status required')
                dec(event['amount'])
                key = canonical([self.owner, event['kind'], event['txhash'], str(event['event_index']), event['token']])
                payload = canonical(event)
                prev = self.db.execute('SELECT payload FROM auxiliary WHERE id=?', (key,)).fetchone()
                if prev:
                    if prev[0] != payload:
                        raise ValueError('conflicting auxiliary event; preserve original evidence')
                    continue
                self.db.execute('INSERT INTO auxiliary VALUES (?, ?)', (key, payload))
                added += 1
        return added

    def record_action(self, response, *, dry=False):
        """Acknowledgements, failed actions and simulations are never fill evidence."""
        return 0

    def report(self, *, opening=None, opening_evidence=None, closing=None,
               coverage=None, cash_evidence=None, rolling_events=200):
        with localcontext() as ctx:
            ctx.prec = 50
            return self._report(opening, opening_evidence, closing, coverage,
                                cash_evidence, rolling_events)

    def _report(self, opening, opening_evidence, closing, coverage,
                cash_evidence, rolling_events):
        issues = []
        coverage = coverage or {}
        if not coverage.get('complete'):
            issues.append('fill coverage not proven complete')
        for flag in ('failed', 'capped', 'retention_uncertain'):
            if coverage.get(flag):
                issues.append('coverage: ' + flag)
        if opening is None or not opening_evidence:
            issues.append('missing verified opening inventory and cost basis')
        lots = defaultdict(deque)
        positions = defaultdict(lambda: ZERO)
        for coin, seed in normalized_coins(opening or {}).items():
            qty, cost = dec(seed['qty']), dec(seed['cost'])
            if qty < 0 or cost < 0 or (qty == 0 and cost != 0):
                raise ValueError('invalid opening lot')
            positions[coin] = qty
            if qty:
                lots[coin].append([qty, cost, True])
        fees = defaultdict(lambda: ZERO)
        market_fees = defaultdict(lambda: defaultdict(lambda: ZERO))
        market_cash = defaultdict(lambda: ZERO)
        flows = defaultdict(lambda: ZERO)
        rows = []
        groups = {}
        fills = [normalize_fill(json.loads(x[0])) for x in self.db.execute('SELECT payload FROM events')]
        fills.sort(key=lambda f: (f['time'], 0 if f['dir'] in ('Buy', 'Split Outcome') else 1,
                                  str(f['tid']), f['coin']))

        def consume(coin, qty):
            remaining, cost, basis_known = qty, ZERO, True
            while remaining > 0 and lots[coin]:
                lot = lots[coin][0]
                take = min(lot[0], remaining)
                part = lot[1] if take == lot[0] else lot[1] * take / lot[0]
                cost += part
                basis_known = basis_known and lot[2]
                lot[0] -= take
                lot[1] -= part
                remaining -= take
                if lot[0] == 0:
                    lots[coin].popleft()
            return qty - remaining, cost, basis_known

        tainted = set()

        def ordered_fills():
            # tid is an identity, not execution ordering. The exchange's actual
            # pre-fill position resolves multiple fills in the same millisecond.
            for _, batch in groupby(fills, key=lambda f: f['time']):
                pending = list(batch)
                while pending:
                    candidates = [f for f in pending if 'startPosition' in f
                                  and dec(f['startPosition']) == positions[f['coin']]]
                    for coin in {f['coin'] for f in candidates}:
                        if sum(f['coin'] == coin for f in candidates) > 1:
                            issues.append('ambiguous same-time event order: ' + coin)
                            tainted.add(coin)
                    chosen = candidates[0] if candidates else pending[0]
                    pending.remove(chosen)
                    yield chosen

        for sequence, f in enumerate(ordered_fills()):
            coin, kind = f['coin'], f['dir']
            qty, px, fee = dec(f['sz']), dec(f['px']), dec(f['fee'])
            token = f['feeToken']
            fees[token] += fee
            market_id = str(int(coin[1:]) // 10)
            market_fees[market_id][token] += fee
            quote_fee = fee if token == 'USDC' else ZERO
            base_fee = fee if token in (coin, '+' + coin[1:]) else ZERO
            valued_fee = token == 'USDC' or token in (coin, '+' + coin[1:]) or fee == 0
            if not valued_fee:
                issues.append('unvalued fee token: ' + token)
            key = event_id(self.owner, f)
            row = {'id': key, 'time': f['time'], 'coin': coin, 'kind': kind,
                   'qty': str(qty), 'price': str(px), 'fee': str(fee), 'fee_token': token}
            if 'startPosition' not in f:
                issues.append('missing startPosition: ' + key)
                tainted.add(coin)
            elif dec(f['startPosition']) != positions[coin]:
                issues.append('startPosition mismatch: ' + key)
                tainted.add(coin)
            if kind in ('Buy', 'Split Outcome') and f['side'] == 'B':
                net_qty = qty - base_fee
                if net_qty < 0:
                    issues.append('negative net acquisition: ' + key)
                    tainted.add(coin)
                elif net_qty == 0:
                    # All purchased tokens were paid as fee. There is no lot to
                    # carry the cash cost: it is an immediate realized expense.
                    cost = qty * px + quote_fee
                    known = valued_fee and coin not in tainted
                    row.update(matched_qty=str(qty), cost=str(cost), proceeds='0',
                               realized_net=str(-cost) if known else None)
                    groups[('Acquisition Fee', key)] = {
                        'kind': 'Acquisition Fee', 'time': f['time'], 'sequence': sequence,
                        'net': -cost, 'known': known, 'market_id': market_id,
                        'legs': {coin: qty}, 'ids': [key]}
                else:
                    lots[coin].append([net_qty, qty * px + quote_fee, valued_fee and coin not in tainted])
                positions[coin] += net_qty
                flows['USDC'] -= qty * px + quote_fee
                market_cash[market_id] -= qty * px + quote_fee
                row.setdefault('realized_net', None)
            elif kind in ('Sell', 'Merge Outcome', 'Settlement') and f['side'] == 'A':
                out_qty = qty + base_fee
                if out_qty <= 0:
                    raise ValueError('nonpositive net disposal quantity')
                matched, cost, basis_known = consume(coin, out_qty)
                positions[coin] -= out_qty
                proceeds = qty * px - quote_fee
                flows['USDC'] += proceeds
                market_cash[market_id] += proceeds
                known = matched == out_qty and valued_fee and basis_known and coin not in tainted
                if matched != out_qty:
                    issues.append('missing acquisition cost: ' + key)
                row.update(matched_qty=str(matched), cost=str(cost),
                           proceeds=str(proceeds), realized_net=str(proceeds - cost) if known else None)
                # Group actual redemption legs for realized loss; a losing .5 leg
                # cannot be counted separately from its profitable partner.
                group_key = (kind, coin[1:-1], f['hash']) if kind in ('Merge Outcome', 'Settlement') else (kind, key)
                group = groups.setdefault(group_key, {'kind': kind, 'time': f['time'],
                    'net': ZERO, 'known': True, 'market_id': market_id, 'legs': defaultdict(lambda: ZERO), 'ids': []})
                group['sequence'] = sequence
                group['time'] = f['time']
                group['net'] += proceeds - cost
                group['known'] = group['known'] and known
                group['legs'][coin] += matched
                group['ids'].append(key)
            else:
                issues.append('unsupported event direction: ' + key + ':' + kind)
                row['realized_net'] = None
            if fee and token != 'USDC' and not base_fee:
                flows[token] -= fee
            rows.append(row)

        realized = []
        # A redemption becomes realized when its last leg is replayed. Keep that
        # execution sequence through rolling-window selection; hashes are identity.
        for g in sorted(groups.values(), key=lambda g: g['sequence']):
            legs = g['legs']
            pair_qty = min(legs.values()) if len(legs) == 2 else ZERO
            if g['kind'] == 'Merge Outcome' and (len(legs) != 2 or len(set(legs.values())) != 1):
                issues.append('incomplete or unequal merge legs: ' + ','.join(g['ids']))
                g['known'] = False
            realized.append({'kind': g['kind'], 'market_id': g['market_id'], 'time': g['time'], 'event_ids': g['ids'],
                             'net': str(g['net']) if g['known'] else None,
                             'matched_shares': str(sum(legs.values(), ZERO)),
                             'paired_qty': str(pair_qty)})
        known = [g for g in realized if g['net'] is not None]
        net = sum((dec(g['net']) for g in known), ZERO)
        loss = sum((-min(dec(g['net']), ZERO) for g in known), ZERO)
        window = realized[-rolling_events:] if rolling_events > 0 else realized
        roll_known = all(g['net'] is not None for g in window)
        roll_net = sum((dec(g['net']) for g in window if g['net'] is not None), ZERO)
        roll_shares = sum((dec(g['matched_shares']) for g in window), ZERO)
        pair_window = [g for g in window if g['kind'] in ('Merge Outcome', 'Settlement') and dec(g['paired_qty']) > 0
                       and dec(g['matched_shares']) == 2 * dec(g['paired_qty'])]
        pair_net = sum((dec(g['net']) for g in pair_window if g['net'] is not None), ZERO)
        pair_qty = sum((dec(g['paired_qty']) for g in pair_window), ZERO)
        auxiliary = [json.loads(x[0]) for x in self.db.execute('SELECT payload FROM auxiliary ORDER BY id')]
        rewards, transfers = [], []
        for item in auxiliary:
            if str(item.get('token', '')).startswith(('#', '+')) and item.get('status') == 'received':
                issues.append('outcome transfer requires independently verified inventory basis')
            if item.get('kind') == 'reward':
                rewards.append(item)
            elif item.get('kind') == 'transfer':
                transfers.append(item)
            else:
                issues.append('unsupported auxiliary evidence')
        # Unified-account USDC is explicitly excluded. Only externally proven,
        # owner+market-scoped cash evidence can reconcile the strategy cash leg.
        cash_reconciled = False
        if cash_evidence and cash_evidence.get('scope') == 'owner_hip4' and cash_evidence.get('evidence'):
            expected = dict(flows)
            for item in auxiliary:
                if item.get('status') != 'received':
                    continue
                if not item.get('evidence') or item.get('scope') != 'owner_hip4':
                    issues.append('unverified auxiliary cash attribution')
                    continue
                token = item['token']
                expected[token] = expected.get(token, ZERO) + dec(item['amount'])
            observed = cash_evidence.get('deltas', {})
            cash_reconciled = all(dec(observed.get(t, '0')) == expected.get(t, ZERO)
                                  for t in set(observed) | set(expected))
            if not cash_reconciled:
                issues.append('scoped cash mismatch')
        else:
            issues.append('missing scoped cash / reward / transfer reconciliation evidence')
        balance_diffs = {}
        if closing is None:
            issues.append('missing closing inventory snapshot')
        else:
            normalized = {c: dec(q) for c, q in normalized_coins(closing).items()}
            for coin in set(positions) | set(normalized):
                diff = normalized.get(coin, ZERO) - positions[coin]
                if diff:
                    balance_diffs[coin] = str(diff)
            if balance_diffs:
                issues.append('closing inventory mismatch')
        by_market = {}
        for market in sorted(set(market_cash) | set(market_fees)):
            settled = [g for g in known if g['market_id'] == market]
            by_market[market] = {
                'matched_realized_net_subtotal': str(sum((dec(g['net']) for g in settled), ZERO)),
                'matched_realized_loss_subtotal': str(sum((-min(dec(g['net']), ZERO) for g in settled), ZERO)),
                'trade_cash_flow_usdc': str(market_cash[market]),
                'fees_by_token': {t: str(v) for t, v in market_fees[market].items()},
                'realization_count': len(settled),
                'paired_qty': str(sum((dec(g['paired_qty']) for g in settled), ZERO))}
        issues = list(dict.fromkeys(issues))
        return {'schema': 1, 'owner': self.owner, 'status': 'unreconciled' if issues else 'reconciled',
                'live_ready': False, 'live_gate': LIVE_GATE_REASON, 'coverage': coverage,
                'opening_evidence': opening_evidence, 'issues': issues,
                'event_count': len(rows), 'first_event_ms': min((f['time'] for f in fills), default=None),
                'last_event_ms': max((f['time'] for f in fills), default=None),
                'fees_by_token': {t: str(v) for t, v in fees.items()}, 'by_market': by_market,
                'trade_cash_flow_by_token': {t: str(v) for t, v in flows.items()},
                'matched_realized_net_subtotal': str(net), 'matched_realized_loss_subtotal': str(loss),
                'realized_net': str(net) if not issues else None,
                'realized_loss': str(loss) if not issues else None,
                'inventory': {c: {'qty': str(positions[c]), 'known_cost': str(sum((l[1] for l in lots[c] if l[2]), ZERO)),
                                   'unvalued_cost_qty': str(sum((l[0] for l in lots[c] if not l[2]), ZERO))}
                              for c in sorted(set(positions) | set(lots))},
                'balance_differences': balance_diffs, 'cash_reconciled': cash_reconciled,
                'rolling': {'event_count': len(window), 'includes_wins_losses_zero': True,
                    'net_all_disposals': str(roll_net) if roll_known else None,
                    'matched_shares_all_disposals': str(roll_shares),
                    'net_per_matched_share': str(roll_net / roll_shares) if roll_known and roll_shares else None,
                    'paired_qty': str(pair_qty),
                    'net_per_pair': str(pair_net / pair_qty) if pair_qty and all(g['net'] is not None for g in pair_window) else None,
                    'note': 'All disposal events in window; paired subset includes only equal two-leg redemptions. No loss sampling.'},
                'rewards': rewards, 'transfers': transfers, 'realizations': realized, 'events': rows}


def load_latest_report(base):
    """Read-only report discovery for daily.py; no migration or state writes."""
    paths = sorted(Path(base).glob('audit_*/report.json'), reverse=True)
    if not paths:
        return None, None
    path = paths[0]
    try:
        return path, json.loads(path.read_text())
    except (ValueError, OSError) as exc:
        return path, {'status': 'unreconciled', 'issues': ['audit report unreadable: ' + str(exc)]}
