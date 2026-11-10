"""Dynamic discovery integration. Only the runtime thread commits scope and state."""
import copy
import queue
import threading

from dynamic_candidates import refresh_pool, allocate_capital
from v2_protocol import BudgetUnavailable
from v2_safety import candidate_reason, fingerprint, number, scoped_coin, unresolved


def scan_complete(cfg, budget=None):
    from v2_protocol import scan_budget
    with scan_budget(budget):
        return _scan_complete(cfg)


def _scan_complete(cfg):
    """Build independently screened executable candidates with reference scores."""
    from dynamic_candidates import scan_all_candidates
    from switch_candidates import fetch_outcome_meta, fetch_incentive_leaves, build_candidate
    import time
    result = scan_all_candidates(cfg)
    metas = fetch_outcome_meta()
    leaves, error = fetch_incentive_leaves()
    if not metas or error:
        raise ValueError('candidate source unavailable: ' + str(error))
    candidates, rejected = [], []
    for row in result['candidates']:
        c, why = build_candidate(str(row['outcome_id']), metas, leaves, cfg)
        if c is not None:
            why = candidate_reason(c, time.time(), cfg)
        if why:
            rejected.append({'outcome_id': row['outcome_id'], 'reason': why})
            continue
        c.update(score=row['score'], score_use='reference_capital_ranking_only_not_expected_value',
                 score_observed_at=result['scanned_at_epoch'], expected_value_usdc=None)
        candidates.append(c)
    return dict(result, candidates=candidates, execution_rejected=rejected)


def install_scope(runtime, candidates):
    """Keep historical metadata/mappings and subscribe only newly managed markets."""
    ex = runtime.executor
    known = {str(c['outcome_id']): c for c in ex.candidates}
    known.update({str(c['outcome_id']): c for c in candidates})
    ex.candidates = list(known.values())
    ex.state['managed_candidates'] = copy.deepcopy(ex.candidates)
    for c in ex.candidates:
        oid = int(c['outcome_id'])
        limits = c['sdk_limits']
        for side, aid in enumerate(limits['asset_ids']):
            coin = f'#{oid*10+side}'
            runtime.exchange.info.name_to_coin[coin] = coin
            runtime.exchange.info.coin_to_asset[coin] = int(aid)
            runtime.exchange.info.asset_to_sz_decimals[int(aid)] = limits['sz_decimals']
        if oid not in runtime.state.outcome_ids:
            runtime.state.outcome_ids.add(oid)
            # 2026-11-07：订阅失败不得中断后续的准入同步。
            # 实测 11-07 09:32 的 scan_install_error：install_scope 里对新市场
            # subscribe 时 WS 已断开，抛 WebSocketConnectionClosedException，
            # 于是 sync_eligible 根本没执行 —— 9 个市场选出来只有 7 个进准入。
            # 订阅只是盘口加速通道，REST 才是权威；失败就留给下一次
            # ensure_ws() 重连补订（那边已按 outcomeMeta 过滤死市场）。
            for side in (0, 1):
                try:
                    runtime.ws.subscribe({'type': 'l2Book', 'coin': f'#{oid*10+side}'},
                                         runtime.state.handle_book)
                except Exception as exc:
                    _sub_err = '%s: %s' % (type(exc).__name__, exc)
                    _errs = runtime.executor.state.setdefault('ws_subscribe_errors', [])
                    _errs.append({'at_ms': int(runtime.executor.now() * 1000),
                                  'coin': f'#{oid*10+side}', 'detail': _sub_err})
                    runtime.executor.state['ws_subscribe_errors'] = _errs[-20:]
                    from executor_v2 import log as _sub_log
                    _sub_log('[订阅失败] #%d%d %s（不中断准入同步，等重连补订）'
                             % (oid, side, _sub_err))
        if hasattr(runtime.adapter, 'update_outcome_ids'):
            runtime.adapter.update_outcome_ids([oid])


def initialize(runtime, auth):
    ex = runtime.executor
    policy = (auth or {}).get('dynamic_policy') or {}
    if (policy.get('approved') is not True or policy.get('scan_interval_seconds') != 21600
            or policy.get('total_capital_limit_usdc') != 300
            or policy.get('capital_per_market') != 60
            or policy.get('criteria_fingerprint') != fingerprint(ex.cfg)):
        raise ValueError('missing approved dynamic authorization policy')
    carry = auth.get('risk_carryforward') or {}
    if (carry.get('verified') is not True or not carry.get('source_experiment_id')
            or not carry.get('evidence_sha256') or not carry.get('source_ledger_sha256')):
        raise ValueError('verified previous-period risk carryforward required')
    if ex.state.get('risk_carryforward') not in (None, carry):
        raise ValueError('risk carryforward changed on restore')
    ex.state.update(risk_carryforward=copy.deepcopy(carry),
                    risk_carryforward_net=number(carry['net_usdc']))
    install_scope(runtime, ex.state.get('managed_candidates', ex.candidates))
    # An empty initial authorization window is legal: no opening before discovery.
    ex.state.setdefault('authorization_windows', [])
    ex.state.setdefault('eligible_market_ids', [])
    # Complete an interrupted scope commit using its durable scan evidence.
    # Reinstalling subscriptions and adapter IDs is idempotent on every restore.
    pool = ex.state.get('dynamic_pool') or {}
    install_scope(runtime, pool.get('candidates', []))
    if pool:
        fresh = (pool.get('scan_ok') and
                 0 <= ex.now()-number(pool.get('observed_at', 0)) < 21600)
        eligible = list(pool.get('eligible_ids', [])) if fresh else []
        if ex.state['eligible_market_ids'] != eligible:
            ex.state['eligible_market_ids'] = eligible
            append_window(ex, ex.now())
            ex.state['snapshot_dirty'] = True
            runtime._snapshot_at = -1e30
            ex.state_save()
    runtime._candidate_results = queue.Queue(maxsize=1)
    runtime._candidate_running = False


def scan_step(runtime):
    ex = runtime.executor
    now = ex.now()
    pool = ex.state.get('dynamic_pool') or {}
    try:
        # Discovery may finish before the first verified opening snapshot. Keep
        # the result queued until the immutable experiment baseline exists.
        result = (runtime._candidate_results.get_nowait()
                  if 'experiment_start_ms' in ex.state else None)
    except queue.Empty:
        result = None
    if result is not None:
        runtime._candidate_running = False
        previous = pool
        pool = refresh_pool(previous, ex.cfg, now=now,
                            scan_fn=lambda cfg: result, management_ids=management_ids(ex))
        ex.state['dynamic_pool'] = pool
        if pool.get('scan_deferred'):
            # 预算延期：没有任何请求发出，也没有新的发现证据。
            # 上一轮已批准名单与入场资格**原样保留**，只落下退避后的重试时刻。
            # 因此这里刻意不 install_scope、不改 eligible_market_ids、不追加授权窗口、
            # 也不把 snapshot_dirty 置真——延期不应造成任何范围/风控状态迁移。
            ex.state_save()
        else:
            # 2026-11-06 诊断插桩：实测 12:09:24 一轮扫描「pool 更新成功但
            # state.candidates / eligible_market_ids 未同步」，同时日志出现一条
            # 空行 —— 判断是下面三步里某一步抛异常被上层吞掉。
            # 这里逐步打点，把异常类型与消息显式写进日志，不再静默失败。
            from executor_v2 import log as _diag_log
            _steps = ['install_scope', 'sync_eligible', 'append_window', 'snapshot_reset']
            _cur = 'init'
            try:
                _cur = 'install_scope'
                install_scope(runtime, pool.get('candidates', []))
                _cur = 'sync_eligible'
                ex.state['eligible_market_ids'] = list(pool.get('eligible_ids', []))
                _cur = 'append_window'
                append_window(ex, now)
                # A larger scope needs a fresh account snapshot, including zero positions.
                _cur = 'snapshot_reset'
                runtime._snapshot_at = -1e30
                ex.state['snapshot_dirty'] = True
                ex.state_save()
                _diag_log('[扫描入册] 全部完成 candidates=%d eligible=%d' % (
                    len(pool.get('candidates') or []),
                    len(ex.state.get('eligible_market_ids') or [])))
            except Exception as _exc:
                _detail = '%s: %s' % (type(_exc).__name__, _exc)
                ex.state['scan_install_error'] = {
                    'at_ms': int(ex.now() * 1000),
                    'step': _cur,
                    'detail': _detail,
                    'steps_total': _steps,
                    'candidates_count': len(pool.get('candidates') or []),
                    'eligible_count': len(pool.get('eligible_ids') or []),
                }
                _diag_log('[扫描入册失败] step=%s %s（candidates=%d eligible=%d，已记入 state.scan_install_error）'
                          % (_cur, _detail,
                             len(pool.get('candidates') or []),
                             len(pool.get('eligible_ids') or [])))
                ex.state_save()
                raise
    if not runtime._candidate_running and now >= pool.get('next_scan_at', 0):
        runtime._candidate_running = True
        # A failed attempt also advances the durable six-hour schedule.
        cfg = copy.deepcopy(ex.cfg)
        def read():
            try:
                result = scan_complete(cfg, runtime.budget)
            except BudgetUnavailable as exc:
                # 2026-11-04 链路 2：REST 预算延期**不是扫描失败**。
                # 否则一次瞬时额度不足就烧掉整个 6 小时发现窗口，并撤销已批准市场
                # 的入场资格。这里回一个 deferred 标记，由 refresh_pool 走短期退避
                # 重试并保留上一轮名单。
                #
                # 审计 F3：旧注释断言「拒绝时一个请求都没发出」，但扫描是多请求
                # 串行的——中途被拒时前面的请求**已经发出并扣费**。这里如实带上
                # 本轮已发请求数与已扣权重，让延期日志能区分「首个请求即被拒」
                # 与「跑到一半没跑完」，不再把两者混为一谈。
                last = getattr(runtime.budget, 'discovery_last_round', None) or {}
                result = {'deferred': True, 'retry_at': exc.retry_at,
                          'requests_sent': last.get('requested', 0),
                          'spent': last.get('spent', 0),
                          'reason': type(exc).__name__ + ': ' + str(exc)}
            except Exception as exc:
                result = {'error': type(exc).__name__ + ': ' + str(exc)}
            runtime._candidate_results.put(result)
        threading.Thread(target=read, daemon=True, name='candidate-discovery-readonly').start()
    if not ex.state['authorization_windows'] and 'experiment_start_ms' in ex.state:
        append_window(ex, now)


def append_window(ex, now):
    windows = ex.state['authorization_windows']
    at_ms = max(int(now*1000), ex.state.get('experiment_start_ms', 0))
    if windows:
        at_ms = max(at_ms, windows[-1]['at_ms']+1)
    expiry = int(number(ex.state['authorization_expires_at'])*1000)
    if at_ms >= expiry:
        return
    windows.append({'at_ms': at_ms, 'end_ms': expiry,
                    'markets': sorted(ex.state.get('eligible_market_ids', [])),
                    'authorization_fingerprint': fingerprint({
                        'parent': ex.state['authorization_fingerprint'],
                        'pool': ex.state.get('dynamic_pool', {}), 'at_ms': at_ms})})


def order_commitment(ex, intent):
    """Describe one authorized Buy using the journal's write-ahead identity."""
    at = intent['created_ms']
    windows = ex.state.get('authorization_windows', [])
    active = next((w for i, w in enumerate(windows)
                   if w['at_ms'] <= at < w['end_ms']
                   and (i + 1 == len(windows) or at < windows[i + 1]['at_ms'])), None)
    market = str(int(intent['coin'][1:]) // 10)
    if active is not None and market not in active['markets']:
        # 2026-11-08 修复（已授权市场被空窗口剥夺提交权）：
        # 动态扫描在无候选时追加 markets=[] 的窗口，使「当前生效窗口」变空，
        # 把此前已授权的持仓市场挡在提交之外 → 每轮抛异常 → 主循环 freeze。
        # 实测：24976 在 index 12（markets=18）被授权，却被 index 15（空）挡住。
        # 兜底：回退到最近的、包含该市场、且仍覆盖下单时刻的窗口。
        # 时间边界（at_ms <= at < end_ms）不放宽。
        active = next((w for w in reversed(windows)
                       if market in (w.get('markets') or [])
                       and w['at_ms'] <= at < w['end_ms']), None)
    if active is None or market not in active['markets']:
        raise ValueError('order submission outside authorized opening window')
    return {'order_key': intent['client_id'], 'cloid': intent['client_id'],
            'coin': intent['coin'], 'submitted_at_ms': at,
            'sz': str(intent['qty']), 'limit_px': str(intent['px']),
            'authorization_fingerprint': active['authorization_fingerprint']}


def persist_order_commitment(ex, intent):
    """Register immutable evidence; the exchange oid is a separate binding."""
    if not intent.get('buy') or intent.get('sent') is False:
        return
    evidence = intent.get('order_commitment')
    if evidence is None:
        # Restore older journals from their durable creation time and cloid.
        # Never use the fill time or the latest eligible set as submission proof.
        evidence = order_commitment(ex, intent)
        intent['order_commitment'] = evidence
        ex.state_save()
    # 2026-11-08 修复（终态意图被重复回填 → 每轮抛错 → 主循环 freeze）：
    # `sync_order_commitments` 只跳过 (deferred, rejected, absent)，不跳 `final`。
    # 三条终态意图每轮被重新回填，而它们的 commitment 是早期生成的、
    # 对应买入授权窗口已被后续空窗口取代 → register_order_commitment 抛
    # 'order submission outside authorized opening window'。
    # 实测这三条在账本 order_commitments 里**都已存在**（3/3 命中，共 563 条），
    # 属于纯重复回填，跳过不丢证据。
    #
    # 幂等：账本已有同 cloid 承诺 → 只补 oid 绑定（独立幂等），不再校验窗口。
    _cloid = intent.get('client_id')
    _already = False
    if _cloid:
        try:
            _already = ex.ledger.has_order_commitment(_cloid)
        except Exception:
            _already = False
    if not _already:
        ex.ledger.register_order_commitment(evidence, source_owner=ex.owner)
    if intent.get('oid') is not None:
        ex.ledger.bind_order_id(intent['client_id'], intent['oid'], source_owner=ex.owner)


def sync_order_commitments(ex):
    """Import durable submissions before a new scan can narrow opening scope."""
    if ex.ledger._stored_identity() is None:
        return
    for intent in ex.state.get('intents', {}).values():
        if intent.get('status') in ('deferred', 'rejected', 'absent'):
            continue
        persist_order_commitment(ex, intent)


def management_ids(ex):
    result = set(ex.state.get('markets', {}))
    result.update(str(c['outcome_id']) for c in ex.candidates)
    for i in ex.state.get('intents', {}).values():
        result.add(str(int(i['coin'][1:])//10))
    return result


def can_allocate_opening(ex, c):
    """Read-only state/authorization gates; never change managed risk.

    Quotes, minimum orders and send-time limits remain checked by open_market.
    open_market also rechecks state and clears an expired pair block; here an
    expired block is only treated as clear for allocation.
    """
    st, now = ex.state, ex.now()
    oid = str(c['outcome_id'])
    if (not all(st.get(k) for k in ('activation_valid', 'snapshot_known',
                                   'ledger_known', 'reward_baseline_known'))
            or any(st.get(k) for k in ('halted', 'open_blocked',
                                      'rest_budget_blocked', 'snapshot_dirty'))
            or unresolved(ex)):
        return False
    if (oid not in st.get('eligible_market_ids', [])
            or now >= number(st.get('authorization_expires_at', 0))):
        return False
    ms = st.get('markets', {}).get(oid)
    phase = ms.get('phase') if ms is not None else 'closed'
    if ms and ms.get('pair_blocked'):
        if (now < number(ms.get('pair_blocked_until', 0)) or ms.get('pos')
                or any(scoped_coin(o.get('coin'), {oid})
                       for o in st.get('remote_orders', []))):
            return False
        if phase == 'waiting':
            phase = 'closed'
    if phase != 'closed':
        return False
    if (ms is not None and st.get('stopped_markets', {}).get(oid)
            and ex.cfg.get('reopen_after_stop', False) is not True):
        return False
    if candidate_reason(c, now, ex.cfg):
        return False
    max_age = number(ex.cfg.get('snapshot_max_age_seconds',
                               ex.cfg.get('snapshot_refresh_seconds', 15) + 5))
    if now-st.get('snapshot_at', -1e30) > max_age:
        return False
    pending = st.get('budget_deferred', {}).get('open_market:' + oid)
    signature = [repr((c,)), getattr(ex.adapter, '_oo_generation', 0),
                 bool(st.get('activation_valid')), None,
                 (st.get('markets', {}).get(oid) or {}).get('phase')]
    if (pending and now < pending['retry_at']
            and pending.get('signature') == signature):
        return False
    return True


def opening_candidates(runtime):
    ex = runtime.executor
    # Restrict acquisition only. All commitments, including excluded/historical
    # markets, still reduce global headroom in the allocator.
    pool = dict(ex.state.get('dynamic_pool', {}))
    by_id = {str(c['outcome_id']): c for c in ex.candidates}
    pool['eligible_ids'] = [oid for oid in pool.get('eligible_ids', [])
                            if str(oid) in by_id
                            and can_allocate_opening(ex, by_id[str(oid)])]
    plan = allocate_capital(pool,
                            ex.state.get('market_reserved', {}),
                            available_usdc=max(0, ex.state.get('free_cash', 0)-
                                number(ex.cfg['experiment_principal_usdc'])*0.1),
                            now=ex.now(), entry_allowed=bool(ex.state.get('ledger_known')
                                and ex.state.get('activation_valid')
                                and not ex.state.get('halted')
                                and not ex.state.get('open_blocked')))
    ex.state['capital_allocation'] = plan
    amounts = {str(r['outcome_id']): r['additional_usdc'] for r in plan['allocations']}
    ex.state['allocated_additional'] = amounts
    ex.state['dynamic_entry_limits'] = dict(amounts)
    by_id = {str(c['outcome_id']): c for c in ex.candidates}
    return [by_id[str(r['outcome_id'])] for r in plan['allocations']
            if r['additional_usdc'] > 0 and str(r['outcome_id']) in by_id]
