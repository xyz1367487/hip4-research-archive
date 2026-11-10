"""Local, side-effect-free dynamic pool planning; runtime owns persistence and orders."""
import copy
import math
from types import FunctionType

SCAN_INTERVAL_SECONDS = 6 * 60 * 60
# 预算延期的重试退避：60 → 120 → 240 → 480 → 900 秒封顶。
# 延期的来源是「这一分钟内额度不够」，额度按 60s 滚动窗口释放，
# 所以几分钟内必然重试成功；绝不像真失败那样等 6 小时。
SCAN_DEFER_BASE_SECONDS = 60
SCAN_DEFER_MAX_SECONDS = 900
# 连续延期到达这个次数（即退避已经顶到 SCAN_DEFER_MAX_SECONDS）就视为「卡住」。
# 审计 F2 的故障模式是「永远延期、scan_ok 恒为 True、外部看不出异常」，
# 所以必须有一个显式可见的标记，而不是等 observed_at 过期后静默停开新仓。
# 60→120→240→480→900，第 5 次起就顶在上限，故阈值为 5。
SCAN_DEFER_STALLED_COUNT = 5
TOTAL_CAP_USDC = 300.0
MARKET_CAP_USDC = 60.0
SCORE_USE = 'reference_capital_ranking_only_not_expected_value'


def _amount(value):
    result = float(value)
    if not math.isfinite(result) or result < 0:
        raise ValueError('amount must be finite and nonnegative')
    return result


def _oid(value):
    if isinstance(value, bool) or str(int(value)) != str(value) or int(value) <= 0:
        raise ValueError('outcome_id must be a positive integer')
    return str(value)


def scan_all_candidates(cfg):
    """Reuse scanner gates without mutating its globals or excluding old holdings.

    Function globals are copied solely to substitute discovery inputs. All safety
    filters, blacklist checks, flattening and reference scoring remain scanner's.
    No candidate file is written and no executor state is read for exclusion.
    """
    import scanner

    def strict_meta():
        meta = scanner.load_outcome_meta()
        if not meta:
            raise ValueError('outcomeMeta unavailable; scan evidence incomplete')
        return meta

    def strict_http(url, *args, **kwargs):
        response = scanner.http_json(url, *args, **kwargs)
        if url == scanner.MONARCH_INC:
            rows = response.get('markets') if isinstance(response, dict) else response
            if (not isinstance(rows, list) or
                    any(not isinstance(row, dict) for row in rows) or
                    (isinstance(response, dict) and
                     (response.get('error') or response.get('__error__')))):
                raise ValueError('incentives response incomplete or unavailable')
        return response

    namespace = dict(vars(scanner))
    namespace.update(load_active_outcomes=lambda: set(), load_outcome_meta=strict_meta,
                     http_json=strict_http)
    scan = FunctionType(scanner.scan.__code__, namespace, scanner.scan.__name__,
                        scanner.scan.__defaults__, scanner.scan.__closure__)
    scan.__kwdefaults__ = dict(scanner.scan.__kwdefaults__ or {})
    result = scan(copy.deepcopy(cfg), persist=False)
    if result.get('rejected_summary', {}).get('盘口查询失败'):
        raise ValueError('book query failed; scan evidence incomplete')
    return result


def _deferral_delay(attempts, retry_at, now):
    """下一次重试的退避间隔：60→120→240→480→900 秒封顶。

    retry_at 是预算真正释放的时刻（通常 ≤60s），作为下界——
    在额度恢复前重试没有意义。但绝不因此超过 900 秒：
    延期必须快速重试，否则等于把发现窗口又烧掉了。
    """
    delay = min(SCAN_DEFER_BASE_SECONDS * 2 ** attempts, SCAN_DEFER_MAX_SECONDS)
    if retry_at is not None:
        try:
            delay = max(delay, float(retry_at) - now)
        except (TypeError, ValueError):
            pass
    return float(min(max(delay, 1.0), SCAN_DEFER_MAX_SECONDS))


def refresh_pool(previous, cfg, *, now, scan_fn=None, management_ids=()):
    """Return a JSON-safe pool; never mutate caller state, clear halts or trade.

    management_ids MUST include runtime holdings/orders/intents/merges/history.
    Failed attempts keep the last pool for management but revoke entry evidence.
    Retry cadence is six hours from each attempt, including failed attempts.

    REST-budget deferral is NOT a failure: the scan never sent a request, so the
    previously approved market list, eligibility and observation time all stay
    valid, and the next attempt backs off 60→120→240→480→900s instead of waiting
    six hours. Genuine failures (network, incomplete response, invalid structure,
    stale timestamp) behave exactly as before: six-hour retry, eligibility revoked.
    Stale discovery still expires on its own, because allocate_capital only
    authorizes entries while now-observed_at < SCAN_INTERVAL_SECONDS.
    """
    now = _amount(now)
    state = copy.deepcopy(previous or {})
    managed = {_oid(x) for x in state.get('management_ids', [])}
    managed.update(_oid(x) for x in management_ids)
    managed.update(_oid(c['outcome_id']) for c in state.get('candidates', []))
    state['management_ids'] = sorted(managed, key=int)
    if state.get('last_attempt_at') is not None and now < state['next_scan_at']:
        return state
    state.update(last_attempt_at=now, next_scan_at=now + SCAN_INTERVAL_SECONDS)
    try:
        result = (scan_fn or scan_all_candidates)(copy.deepcopy(cfg))
        if isinstance(result, dict) and result.get('deferred'):
            # 预算延期：不是失败。保留全部既有发现。
            attempts = int(state.get('scan_deferred_count') or 0)
            due = now + _deferral_delay(attempts, result.get('retry_at'), now)
            state.update(
                next_scan_at=due, scan_deferred=True, scan_deferred_at=now,
                scan_deferred_count=attempts + 1,
                scan_deferred_until=due,
                scan_deferred_reason=str(result.get('reason') or 'BudgetUnavailable'),
                # 审计 F3/F2：如实记录本轮已发请求数与已扣权重，并显式区分
                # 「首个请求即被拒」（requests_sent=0，一个请求都没发出）与
                # 「跑到一半没跑完」（requests_sent>0，已花掉的额度是真实成本）。
                scan_deferred_requests=int(result.get('requests_sent') or 0),
                scan_deferred_spent=float(result.get('spent') or 0.0),
                # 审计 F2：延期本身必须**外部可见**。旧实现里 scan_ok 恒为 True、
                # scan_error 为空，反复延期在外部完全看不出来，只能等到 6 小时后
                # observed_at 自然过期、静默停止开新仓。这里把「连续延期已到退避
                # 上限」显式标出来，看板/审计可直接据此报警。
                scan_deferred_stalled=bool(attempts + 1 >= SCAN_DEFER_STALLED_COUNT))
            # 延期不写 scan_error，也不碰 scan_ok/eligible_ids/observed_at/candidates：
            # 上一轮已批准名单继续有效，管理范围同样保持。
            return state
        if not isinstance(result, dict) or result.get('error'):
            raise ValueError(str(result.get('error')) if isinstance(result, dict)
                             else 'invalid scan response')
        rows = result.get('candidates')
        if not isinstance(rows, list):
            raise ValueError('missing complete candidates list')
        candidates, seen = [], set()
        for raw in rows:
            c = copy.deepcopy(raw)
            oid = _oid(c['outcome_id'])
            if oid in seen:
                raise ValueError('duplicate outcome_id in scan')
            seen.add(oid)
            c['score'] = _amount(c['score'])
            c['outcome_id'] = int(oid)
            candidates.append(c)
        candidates.sort(key=lambda c: (-c['score'], int(c['outcome_id'])))
        observed_at = _amount(result.get('scanned_at_epoch', now))
        if observed_at > now + 60 or now - observed_at >= SCAN_INTERVAL_SECONDS:
            raise ValueError('scan observation timestamp stale or in future')
        managed.update(seen)
        audit = list(state.get('scan_audit', []))
        audit.append({'attempt_at': now, 'observed_at': observed_at,
                      'score_use': SCORE_USE, 'ev_status': 'unknown',
                      'expected_value_usdc': None,
                      'ranking': [{'outcome_id': c['outcome_id'], 'score': c['score']}
                                  for c in candidates]})
        state.update(candidates=candidates, eligible_ids=sorted(seen, key=int),
                     management_ids=sorted(managed, key=int),
                     scan_ok=True, scan_error=None, last_success_at=now,
                     observed_at=observed_at, scan_audit=audit,
                     # 成功一轮：清掉延期痕迹，下一次延期从 60s 重新起算。
                     scan_deferred=False, scan_deferred_count=0,
                     scan_deferred_until=None, scan_deferred_reason=None,
                     scan_deferred_requests=0, scan_deferred_spent=0.0,
                     scan_deferred_stalled=False)
    except Exception as exc:
        state.update(scan_ok=False, scan_error=f'{type(exc).__name__}: {exc}',
                     eligible_ids=[],
                     # 真失败：退避序列重新起算，避免上一次延期把下次失败的重试
                     # 拉到 900s 上限。scan_deferred 只用于标记延期，此处不置真。
                     scan_deferred_count=0, scan_deferred=False,
                     scan_deferred_until=None, scan_deferred_reason=None)
    return state


def allocate_capital(pool, committed_by_outcome, *, available_usdc, now,
                     entry_allowed=True):
    """Plan incremental capital from known, already deduplicated commitments.

    available_usdc is spendable cash AFTER runtime's required cash buffer.
    Unknown accounting must be supplied as entry_allowed=False. This function
    supplies ceilings only; minimum order and all send-time guards still apply.
    """
    now = _amount(now)
    committed = {}
    for key, value in committed_by_outcome.items():
        oid = _oid(key)
        if oid in committed:
            raise ValueError('duplicate normalized commitment identity')
        committed[oid] = _amount(value)
    total = sum(committed.values())
    cash = _amount(available_usdc)
    headroom = min(max(0.0, TOTAL_CAP_USDC - total), cash)
    observed_at = pool.get('observed_at')
    fresh = (observed_at is not None and 0 <= now - observed_at < SCAN_INTERVAL_SECONDS)
    allowed = bool(entry_allowed and pool.get('scan_ok') and fresh)
    eligible = set(pool.get('eligible_ids', []))
    allocations = []
    for c in sorted(pool.get('candidates', []),
                    key=lambda row: (-_amount(row['score']), int(row['outcome_id']))):
        oid = _oid(c['outcome_id'])
        existing = committed.get(oid, 0.0)
        extra = min(headroom, max(0.0, MARKET_CAP_USDC - existing)) if (
            allowed and oid in eligible) else 0.0
        headroom -= extra
        allocations.append({'outcome_id': int(oid), 'score': c['score'],
                            'committed_usdc': existing, 'additional_usdc': extra,
                            'ceiling_usdc': existing + extra})
    managed = set(pool.get('management_ids', [])) | set(committed)
    return {'allocations': allocations, 'management_ids': sorted(managed, key=int),
            'entry_evidence_valid': allowed, 'committed_total_usdc': total,
            'additional_total_usdc': sum(r['additional_usdc'] for r in allocations),
            'total_cap_usdc': TOTAL_CAP_USDC, 'market_cap_usdc': MARKET_CAP_USDC,
            'over_total_cap': total > TOTAL_CAP_USDC,
            'over_market_cap_ids': sorted((k for k, v in committed.items()
                                           if v > MARKET_CAP_USDC), key=int),
            'score_use': SCORE_USE, 'ev_status': 'unknown',
            'expected_value_usdc': None}
