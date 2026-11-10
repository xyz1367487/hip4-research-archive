"""Fail-closed experimental runtime. All financial state belongs to the loop thread.

No credentials are imported here. Authorization is independent of legacy scanners.
Unknown submissions remain durable intents; only remote finality releases them.
"""
import hashlib
import json
import math
import queue
import threading
import time
import uuid
from pathlib import Path
from functools import wraps
from contextlib import nullcontext
from decimal import Decimal, InvalidOperation
from v2_protocol import BudgetedInfo, WeightBudget, BudgetUnavailable, price_wire, minimum_order, sell_proceeds
from v2_events import ev, ev_change

OWNER = 'REDACTED_ACCOUNT_ADDRESS'


def deferred_operation(fn):
    """Boundary for one market operation; IO layers never convert deferral to failure."""
    @wraps(fn)
    def run(ex, *args, **kwargs):
        oid = str(args[0].get('outcome_id')) if fn.__name__ == 'open_market' else str(args[0])
        key = fn.__name__ + ':' + oid
        schedule = ex.state.setdefault('budget_deferred', {})
        budget = getattr(ex.adapter.info, 'budget', None)
        priority = fn.__name__ in ('unwind', 'merge')
        def signature():
            ms = ex.state.get('markets', {}).get(oid, {})
            keep = (maker_exit_keep_side(ex, oid, args[1],
                    number(ex.cfg.get('maker_exit_wait_seconds', 300)))
                    if fn.__name__ == 'unwind' else None)
            return [repr(args), getattr(ex.adapter, '_oo_generation', 0),
                    bool(ex.state.get('activation_valid')), keep, ms.get('phase')]
        def waiting(entry):
            message = f'预算/复核延期至 {entry["retry_at"]:g}；保持未确认，继续管理'
            return (False, message) if fn.__name__ in ('open_market', 'merge') else message
        pending = schedule.get(key)
        if pending and ex.now() < pending['retry_at'] and pending.get('signature') == signature():
            return waiting(pending)
        try:
            with budget.priority() if priority and isinstance(budget, WeightBudget) else nullcontext():
                result = fn(ex, *args, **kwargs)
        except BudgetUnavailable as exc:
            schedule[key] = {'retry_at': exc.retry_at or ex.now() + 1,
                             'reason': str(exc), 'signature': signature()}
            ex.state['rest_budget_blocked'] = True
            ex.state_save()
            return waiting(schedule[key])
        schedule.pop(key, None)
        return result
    return run


def _hold_through_result(c, cfg):
    """体育盘「持有到比赛结束」的开关与前提：必须有可解析开赛时间。"""
    from executor_v2 import sports_schedule
    if not cfg.get('hold_through_result_when_paired', True):
        return False
    return sports_schedule(c.get('meta')) is not None


# 2026-11-05 熔断误触发修复（用户 03:04 拍板 A+C）
# A 连续确认：同一阈值状态连续 N 次采样成立才熔断。1 = 旧的单次判定行为。
FUSE_CONFIRM_SAMPLES = 2
# C 合并豁免：merge 提交后该秒数内的中间态窗口不参与熔断判定。
FUSE_MERGE_GRACE_SEC = 10


# 2026-11-05 估值合理性下限（用户 12:38 拍板：紧一点取 0.9）
# 逐档吃 bid 算出的保守退出均价，若低于 best_bid * 此比例，判为不可执行估值：
# 该估值不参与熔断/单市场止损，只影响风控判定，交易照常。
VALUATION_FLOOR_RATIO = 0.9
# 估值不可执行后的重试间隔（用户：等 5 分钟再处理，薄深度通常秒级恢复）
VALUATION_RETRY_SEC = 300
# 单市场止损连续确认次数（与总熔断同级）
MARKET_STOP_CONFIRM_SAMPLES = 2


def fingerprint(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':'),
                                     ensure_ascii=False).encode()).hexdigest()


def market_id(value):
    raw = str(value)
    raw = raw[1:] if raw.startswith('O') else raw
    if not raw.isdigit():
        raise ValueError('market_id非法')
    return str(int(raw))


def number(value):
    n = float(value)
    if not math.isfinite(n):
        raise ValueError('nonfinite number')
    return n


def total_cap(cfg):
    """Dynamic experiments have an independent, explicitly approved ceiling."""
    if cfg.get('dynamic_candidates_enabled') is True:
        return number(cfg['total_capital_limit_usdc'])
    return number(cfg.get('n_markets', 6)) * number(cfg.get('capital_per_market', 12))


def read_json(path):
    return json.loads(Path(path).read_text())


def load_inputs(base, config_path=None, authorization_path=None, *, allow_expired_recovery=False):
    base = Path(base)
    cfg = read_json(config_path or base / 'config.json')
    # 2026-10-30 用户拍板：本金放大到账户可用（$404.30），同时 6 个市场、
    # 每市场仍 $12、净亏上限改为**本金 10%**（不再写死 $12/$120）。
    # 仍保留硬边界，避免配置被随手改大：
    #   - 每市场固定 $12（单市场风险不变）
    #   - 同时市场数 1..8，且总敞口不得超过本金 25%
    #   - 净亏上限必须等于 本金×10%（±0.01 容差），不接受任意放大
    n = cfg.get('n_markets')
    per = cfg.get('capital_per_market')
    principal = number(cfg.get('experiment_principal_usdc', 0))
    net_limit = number(cfg.get('net_loss_limit_after_reward_usdc', 0))
    # 2026-10-30 方案C：每市场资金可配置（12..30），不再是固定 12。
    # 上限 30 的理由：份数 = 资金/(YES+NO) 约等于资金额；止损距离 = 4/(份数×2)，
    # 资金 30 时距离已缩到 $0.067，再大就接近「止损形同虚设」。
    dynamic = cfg.get('dynamic_candidates_enabled') is True
    if dynamic:
        if per != 60 or number(cfg.get('total_capital_limit_usdc', 0)) != 300:
            raise ValueError('动态候选仅批准总占款300/单市场60')
        if cfg.get('candidate_scan_interval_seconds') != 21600:
            raise ValueError('动态候选扫描间隔必须为6小时')
    else:
        if not isinstance(per, (int, float)) or not 12 <= per <= 30:
            raise ValueError('每市场真实资金须在 12..30 之间')
        if not isinstance(n, int) or not 1 <= n <= 8:
            raise ValueError('同时市场数须为 1..8 的整数')
    if principal <= 0:
        raise ValueError('本金必须为正')
    if not dynamic and n * per > principal * 0.25:
        raise ValueError(f'总敞口 {n*per} 超过本金 25%（{principal*0.25:.2f}）')
    if abs(net_limit - principal * 0.1) > 0.01:
        raise ValueError(f'净亏上限须等于本金 10%（{principal*0.1:.2f}），实际 {net_limit}')
    if cfg.get('v2_exit_policy') != 'merge_confirmed_pairs_then_unwind_residual' or cfg.get('v2_partial_fill_policy') != 'cancel_filled_side_wait_opposite_with_stop':
        raise ValueError('v2退出/部分成交策略不支持，拒绝忽略配置')
    # 2026-10-31 用户拍板开启「对侧超时追价配对」：
    # 单边成交后若对侧 N 分钟不成交，比较「追价补齐净回收」vs「等待的期望损失」，
    # 划算才追（maker 挂中间价或 taker 直接吃）。规则由 hedge_decision 决定。
    # 仍拒绝旧的 v2_legacy_hedge_config_applies（那套是另一套语义，不混用）。
    if cfg.get('v2_legacy_hedge_config_applies') is not False:
        raise ValueError('v2不使用旧hedge配置语义；须明确关闭')
    hedge_on = cfg.get('v2_hedge_buy_enabled') is True
    if hedge_on:
        # 开启时必须给出追价参数，否则拒绝启动（不允许隐式默认值上线）
        for k in ('hedge_trigger_seconds', 'hedge_max_slippage'):
            if k not in cfg:
                raise ValueError(f'开启追价配对必须显式配置 {k}')
    if cfg.get('stop_loss_usd_per_market') != 4 or cfg.get('settle_mode') != 'unwind':
        raise ValueError('本实验要求 stop4 / unwind；其他退出策略尚未批准')
    # 本金/净亏上限已在上方按「本金 10%」校验（2026-10-30 用户拍板），此处不再重复写死。
    path = Path(authorization_path or base / cfg.get('v2_authorization_file', 'v2_authorization.json'))
    if path.resolve().parent != base.resolve() or path.name in ('candidates.json', 'market_screen.json'):
        raise ValueError('须使用独立本地v2候选授权文件')
    auth = read_json(path) if path.exists() else None
    if auth is None:
        return cfg, None, [], ['缺独立v2候选授权文件，等待人工选择']
    if auth.get('schema') != 'hip4-v2-authorization-1' or not auth.get('experiment_id'):
        raise ValueError('候选授权schema/experiment_id缺失')
    if str(auth.get('owner', '')).lower() != OWNER.lower():
        raise ValueError('候选授权owner不匹配')
    if auth.get('config_fingerprint') != fingerprint(cfg):
        raise ValueError('候选授权config指纹不匹配')
    recovery_issues = []
    if number(auth.get('expires_at', 0)) <= time.time():
        if not allow_expired_recovery:
            raise ValueError('候选授权已过期')
        # Existing first-activation identity is still checked by the live caller.
        # An expired scope may restart only to reconcile/unwind; tick's expiry
        # and authorization guards block every new acquisition before trading.
        recovery_issues.append('候选授权已过期：仅恢复对账和收尾，禁止新开仓')
    coverage = auth.get('fill_coverage') or {}
    if (coverage.get('verified') is not True or not coverage.get('evidence')
            or number(coverage.get('retention_seconds', 0)) <= 0
            or not 0 < number(coverage.get('max_results', 0)) <= 2000):
        raise ValueError('REST成交保留窗口/上限覆盖证据未知')
    candidates = auth.get('candidates')
    if not isinstance(candidates, list) or len({str(c['outcome_id']) for c in candidates}) != len(candidates):
        raise ValueError('授权候选列表非法/重复')
    return cfg, auth, candidates, recovery_issues


def activation_valid(path, cfg, auth):
    if not auth or not Path(path).exists():
        return False
    a = read_json(path)
    return (a.get('schema') == 'hip4-v2-first-activation-1'
            and a.get('approved') is True and bool(a.get('approved_at'))
            and bool(a.get('operator_confirmation'))
            and a.get('owner', '').lower() == OWNER.lower()
            and a.get('experiment_id') == auth['experiment_id']
            and a.get('config_fingerprint') == fingerprint(cfg)
            and a.get('authorization_fingerprint') == fingerprint(auth))


def candidate_reason(c, now, cfg):
    '候选是否可入场。时间口径按用户 历史版本 拍板的 B 方案。\n\n    体育盘（sports* 模板）不要求 API 里不存在的「结算时间」，改用**清仓截止**\n    = scheduledStart − pre_game_clear_seconds（默认 1h）：\n      开赛前双边都在 → 持有到比赛结束；开赛前 1h 仍无双边 → 直接清仓。\n    非体育盘仍要求明确 settlement_time（fail-closed 不变）。\n    两者都不把 incentive_end_time / resolutionDeadline 冒充结算。\n    '
    from executor_v2 import settlement_time, safety_mult_ok, sports_schedule
    try:
        settle, _ = settlement_time(c.get('source'), c.get('meta'))
        sports = sports_schedule(c.get('meta'))
        explicit = any((obj or {}).get(k) for obj in (c.get('source'), c.get('meta'))
                       for k in ('settlement_time', 'settlement_at', 'resolution_time'))
        lead = number(cfg.get('pre_game_clear_seconds', 3600))
        if sports:
            # 体育盘：清仓截止 = scheduledStart − lead，是唯一的时间闸门。
            # 不再叠加 withdraw_hours_before_settle（那是给"结算时间"用的，
            # 拿开赛时间当结算会变成开赛前 6h 就停，与用户拍板的 1h 冲突）。
            clear_at = sports['scheduledStart'] - lead
            if clear_at <= now:
                return '已过开赛前清仓截止（体育盘规则）'
            settle = sports['scheduledStart']   # 仅用于下面的时长窗口计算
        else:
            if not explicit or settle is None or settle <= now:
                return '实际结算时间未知/已到期'
            if settle - now <= number(cfg.get('withdraw_hours_before_settle', 6)) * 3600:
                return '进入结算前撤退窗口'
        for field in ('event_end_time', 'incentive_end_time', 'safety_valid_until'):
            from executor_v2 import parse_time
            if parse_time(c.get(field)) is None or parse_time(c[field]) <= now:
                return field + ' 未知/已过期'
        ok, why = safety_mult_ok(c.get('band_width_cents'), c.get('worst_step_cents'))
        if not ok or not c.get('safety_evidence'):
            return '安全数据不足: ' + why
        source = c['source']
        if number(source['reward_amount_usdc']) < number(cfg['min_pool_usdc']):
            return 'pool低于门槛'
        if source['incentive_status'] not in ('active', 'incentivized'):
            return '当前激励非active'
        if str(source['hyperliquid_outcome_id']) != str(c['outcome_id']):
            return '候选来源outcome映射不一致'
        # 时长窗口分两种口径，不能混：
        # - 体育盘：还有多少时间**可以挂单**（到清仓截止）。开赛前 1h 内不该新开，
        #   所以下界用 0 而不是 12；上界仍防"刚上线就锁 3 天"。
        # - 其他盘：沿用「距结算」窗口，双端都用 min/max_hours_left。
        if sports:
            remaining = (sports['scheduledStart'] - lead - now) / 3600
            if not 0 < remaining <= number(cfg['max_hours_left']):
                return '距开赛清仓截止的可挂单时长不在配置窗口'
        else:
            remaining = (settle - now) / 3600
            if not number(cfg['min_hours_left']) <= remaining <= number(cfg['max_hours_left']):
                return '实际到期时间不在配置窗口'
        limits = c.get('sdk_limits') or {}
        if not limits.get('evidence') or limits.get('verified') is not True:
            return 'SDK最小份数/名义及资产映射未核实'
        if not all(number(limits.get(k, default)) >= 0 for k, default in (('min_shares', 0), ('min_notional_per_leg', 1))):
            return 'SDK限制非法'
        if not isinstance(limits.get('sz_decimals'), int) or not 0 <= limits['sz_decimals'] <= 8:
            return 'SDK数量精度未知；开仓仍只使用整数份数'
        asset_ids = limits.get('asset_ids', [])
        expected_assets = [100_000_000 + int(market_id(c['outcome_id'])) * 10 + side
                           for side in (0, 1)]
        if (not isinstance(asset_ids, list) or len(asset_ids) != 2
                or any(type(asset) is not int for asset in asset_ids)
                or asset_ids != expected_assets):
            return 'SDK资产映射与Outcome确定性编码不一致'
    except (KeyError, TypeError, ValueError, OverflowError) as exc:
        return '候选字段非法: ' + str(exc)
    return None


def scoped_coin(coin, ids):
    s = str(coin)
    return s.startswith(('#', '+')) and s[1:].isdigit() and str(int(s[1:]) // 10) in ids


def _get_orders(ex, use_cache=True):
    '统一取全量挂单（历史版本 L1）。\n\n    adapter 实现了 get_open_orders 就带上缓存语义；\n    否则（mock / 旧实现）退回裸 info 调用——保证测试与旧代码兼容。\n    '
    getter = getattr(ex.adapter, 'get_open_orders', None)
    if getter is not None:
        return getter(use_cache=use_cache)
    return ex.adapter.info({'type': 'openOrders', 'user': ex.owner})


def snapshot(info, owner, ids, orders_getter=None):
    # 2026-11-02 L1：走统一入口（若 info 就是 adapter.get_open_orders 则自动带缓存）。
    # 这里保持对普通 callable 的兼容：优先调用 get_open_orders，否则退回裸 info。
    _getter = orders_getter or getattr(info, 'get_open_orders', None)
    orders = _getter(use_cache=True) if _getter else info({'type': 'openOrders', 'user': owner})
    spot = info({'type': 'spotClearinghouseState', 'user': owner})
    if not isinstance(orders, list) or not isinstance(spot, dict) or not isinstance(spot.get('balances'), list):
        raise ValueError('openOrders/spot balances读取失败或未知')
    positions = {str(i): {} for i in ids}
    cash = None
    for b in spot['balances']:
        qty = number(b['total'])
        if qty < 0:
            raise ValueError('负余额')
        coin = b['coin']
        if coin == 'USDC':
            cash = qty - number(b['hold'])
        if scoped_coin(coin, positions):
            enc = int(coin[1:])
            if enc % 10 not in (0, 1):
                raise ValueError('未知 outcome side')
            positions[str(enc // 10)][str(enc % 10)] = qty
    if cash is None or cash < 0:
        raise ValueError('USDC可用余额未知')
    for o in orders:
        if not all(k in o for k in ('coin', 'oid', 'sz', 'limitPx', 'side')):
            raise ValueError('订单快照字段不完整')
        number(o['sz']); number(o['limitPx'])
    return {'orders': orders, 'positions': positions, 'cash': cash, 'at_ms': int(time.time()*1000)}


def journal(ex):
    ex.state.setdefault('intents', {})
    ex.state.setdefault('submitted_oids', [])
    ex.state.setdefault('rewards', {})
    return ex.state['intents']


def authorization_expired(ex):
    expiry = ex.state.get('authorization_expires_at')
    if expiry is not None and number(expiry) <= ex.now():
        ex.state.update(activation_valid=False, halted=True,
                        halt_reason='独立候选授权到期，停止新仓并收尾')
        return True
    return False


def submit(ex, coin, buy, qty, px, tif):
    px = float(price_wire(px, buy=buy, tif=tif))
    # 2026-11-01 修复（小额残仓永远卖不掉，与 unwind / place_limit 口径统一）：
    # 原实现在这里也要求「qty × px ≥ $1」，对**卖出**同样生效，
    # 导致 1 份 @$0.69684 的平仓单直接被 ValueError 拦下（连 intent 都不会写）。
    # 而下单层 executor_v2.place_limit 的门槛是 `if is_buy and ... < 1`，
    # 即只约束开仓买入；其注释明确允许低于 $1 的平仓卖出。
    # 现在：$1 门槛只对买入生效；卖出只要求整数份数且价格为正。
    if number(qty) <= 0 or number(qty) != int(number(qty)):
        raise ValueError('每腿须整数份数')
    if px <= 0:
        raise ValueError('价格必须为正')
    if buy and Decimal(str(qty))*Decimal(str(px)) < 1:
        raise ValueError('开仓买入实际单腿名义至少1美元')
    previous = next((i for i in journal(ex).values() if i.get('status') == 'deferred'
                     and (i['coin'], i['buy'], i['qty'], i['px'], i['tif'])
                     == (coin, buy, qty, px, tif)), None)
    if previous and ex.now() < previous['retry_at']:
        raise BudgetUnavailable(retry_at=previous['retry_at'])
    key = previous['client_id'] if previous else '0x' + uuid.uuid4().hex
    intent = {'client_id': key, 'coin': coin, 'buy': buy, 'qty': qty, 'px': px,
              'tif': tif, 'status': 'unknown', 'created_ms': int(ex.now()*1000)}
    if buy and ex.cfg.get('dynamic_candidates_enabled'):
        from c_runtime import order_commitment
        intent['order_commitment'] = order_commitment(ex, intent)
        if previous and previous.get('order_commitment'):
            intent['created_ms'] = previous['created_ms']
            intent['order_commitment'] = previous['order_commitment']
    journal(ex)[key] = intent
    ex.state_save()  # write-ahead, including a crash before the HTTP request
    if buy and ex.cfg.get('dynamic_candidates_enabled'):
        from c_runtime import persist_order_commitment
        persist_order_commitment(ex, intent)
    try:
        if buy and authorization_expired(ex):
            response = {'rejected': True, 'sent': False, 'reason': 'authorization_expired'}
        else:
            response = ex.adapter.place_limit(coin, buy, qty, px, tif, client_id=key)
    except BudgetUnavailable as exc:
        intent.update(status='deferred', retry_at=exc.retry_at or ex.now()+1, sent=False)
        ex.state_save()
        raise
    except Exception as exc:
        response = {'unknown': True, 'error': type(exc).__name__}
    if isinstance(response, dict) and response.get('rejected'):
        intent.update(status='rejected', reason=response.get('reason'),
                      response=response)
        if response.get('sent') is False:
            intent['sent'] = False
    elif isinstance(response, dict) and response.get('oid') is not None:
        intent.update(oid=response['oid'], status='submitted')
        ex.state['submitted_oids'].append(str(response['oid']))
    else:
        intent.update(status='unknown', response=response)
    ex.state['snapshot_dirty'] = True
    # 2026-11-02 L1：挂单成功/未知都要让 adapter 知道「挂单状态可能已变」，
    # 否则 cancel_all 的缓存预判可能漏掉这张新单。
    _note = getattr(ex.adapter, 'note_submit', None)
    if _note is not None and intent.get('status') in ('submitted', 'unknown'):
        try:
            _note()
        except BudgetUnavailable:
            raise
        except Exception:
            pass
    ex.state_save()
    if buy and ex.cfg.get('dynamic_candidates_enabled') and intent.get('oid') is not None:
        persist_order_commitment(ex, intent)
    # 2026-11-01 业务日志：只在「被拒 / 未知」时记，成功由上层报价/退出事件覆盖，
    # 避免每张挂单写两遍。dedup 键含 cloid，同一张单不会重复报。
    if intent.get('status') in ('rejected', 'unknown'):
        ev('下单异常', key='intent:' + key, dedup=True,
           coin=coin, buy='买' if buy else '卖', qty=qty, px=px, tif=tif,
           status=intent.get('status'), reason=intent.get('reason'),
           error=response.get('error') if isinstance(response, dict) else None)
    return intent


# unknown 意图的自我了结（用户 2026-10-28 22:09 / 22:15 / 22:16 三次纠正）。
#
# cloid 是**发请求之前**就生成并写进 journal 的，HL 收到就立刻有记录，
# `orderStatus` 按 cloid 必能查到（实测：10-26 的历史订单至今仍返回完整
# `{"status":"order", ..., "sz":"0.0"}`）。所以：
#   - 查得到        → 补 oid，按 remote 状态裁决
#   - 返回 unknownOid → 这个请求没到 HL，就是不存在
#
# **不设落地宽限**（用户 22:16：扫市场 + 双边下单只要几秒，没有 60 秒可等）。
# 本就有 15 秒的 submitted 复查间隔，加上每轮 tick 都在查，这个节奏已经够。


def unresolved(ex, oid=None):
    '判断是否仍有未了结的提交。\n\nabsent 已确认不存在，不再阻挡；unknown 等待后续查询裁决。\n未传 oid 时检查全部意图，传入 oid 时仅检查指定市场。'
    rows = journal(ex).values()
    if oid is not None:
        want = str(oid)
        rows = [i for i in rows
                if scoped_coin(i.get('coin'), {want})]
    return any(i['status'] in ('unknown', 'awaiting_fill') for i in rows)


def pair(ex, oid, bids, shares):
    '提交双腿挂买单并区分提交结果。\n\nsubmitted 表示正常提交；unknown 保留意图，由 reconcile_intents\n通过 cloid 查询裁决，本轮返回 None，等待后续重试。\nrejected 触发本市场持久化收尾与预留后撤单。'
    placed = {}
    # 进入 pair() 说明上一次的 pair_blocked 已被解除（由 maintain 在确认
    # 相关 unknown 意图已了结为 absent/submitted 后清除），这里复位标志。
    _ms = ex.state.setdefault('markets', {}).setdefault(str(oid), {})
    _ms.pop('pair_blocked', None)
    for s in (0, 1):
        try:
            intent = submit(ex, f'#{oid*10+s}', True, shares, bids[s], 'Alo')
        except BudgetUnavailable:
            if placed:
                _ms.update(phase='unwinding', orders=placed, sz=shares,
                           notional=shares*sum(bids))
                ex.state['snapshot_dirty'] = True
                ex.state_save()
            else:
                _ms.setdefault('phase', 'closed')  # no leg was sent; allow a fresh authorized attempt
            raise
        if intent['status'] == 'submitted':
            placed[str(s)] = {'oid': intent['oid'], 'px': bids[s], 'sz': shares}
            continue
        if intent['status'] == 'unknown':
            # 结果未知：保留意图等 cloid 裁决，**不 halt、不把市场钉成 unwinding**
            # （这是本次要修的 bug），但**也不能放开重发**——
            # 下单超时没拿到 oid 时重发就是在赌"HL 到底收没收到"，可能重复下单。
            # 这条由 test_timeout_never_resubmits 锁定，不可破。
            #
            # 折中：保留市场原 phase（不改 unwinding），并把该市场标成
            # `pair_blocked`，让 open_market 在意图了结前不再进入本市场；
            # 意图由 reconcile_intents 按 cloid 裁决（补 oid 或判 absent）后，
            # 下一轮再决定是否重新配对。
            if placed:
                # 另一腿已挂上 → 撤掉它，避免单腿裸挂（本实验不允许单边开仓）
                try:
                    ex.adapter.cancel_all(int(oid))
                except BudgetUnavailable:
                    raise
                except Exception:
                    pass
            ms = ex.state.setdefault('markets', {}).setdefault(str(oid), {})
            prev_phase = ms.get('phase')
            if prev_phase in (None, 'closed'):
                ms['phase'] = 'waiting'          # 不钉 unwinding，也不留 closed 放行重开
            ms['pair_blocked'] = ('配对本腿下单结果未知，等待 cloid 裁决；'
                                  '裁决前不重发、不重开')
            # 冷却期：即使 cloid 判成 absent，也不立刻重发（防迟到响应造成重复开仓）。
            # 默认 10 分钟，可通过 config 覆盖；到期且无持仓无挂单才自动解除。
            ms['pair_blocked_until'] = ex.now() + number(
                ex.cfg.get('pair_blocked_cooldown_seconds', 600))
            ex.state['pair_pending_note'] = ms['pair_blocked']
            ex.state_save()
            return None
        if intent.get('reason') == 'authorization_expired':
            if placed:
                cost = shares * sum(bids)
                _ms.update(phase='unwinding', orders=placed, sz=shares,
                           notional=cost, rollback_confirmed=False)
                # Retain the pair's reservation until a fresh remote snapshot
                # accounts for the first leg, including any concurrent fill.
                ex.state['reserved_total'] = ex.state.get('reserved_total', 0) + cost
                ex.state.setdefault('market_reserved', {})[str(oid)] = cost
                ex.state['free_cash'] = ex.state.get('free_cash', 0) - cost
                ex.state['snapshot_dirty'] = True
                ex.state_save()
                _ms['rollback_confirmed'] = ex.adapter.cancel_all(oid)
            else:
                _ms.setdefault('phase', 'closed')
            ex.state_save()
            return None
        # Persist market cleanup and its reservation before attempting cancellation.
        # A definite rejection is local; unknown submissions retain their cloid gate.
        _ms.update(phase='unwinding', orders=placed, sz=_ms.get('sz') or shares,
                   notional=shares*sum(bids), rollback_confirmed=False,
                   pair_rejection={'client_id': intent['client_id'],
                                   'reason': intent.get('reason')})
        cost = shares * sum(bids)
        previous_reserve = ex.state.setdefault('market_reserved', {}).get(str(oid), 0)
        ex.state['market_reserved'][str(oid)] = max(previous_reserve, cost)
        ex.state['reserved_total'] = ex.state.get('reserved_total', 0) + max(0, cost-previous_reserve)
        ex.state['free_cash'] = ex.state.get('free_cash', 0) - max(0, cost-previous_reserve)
        ex.state['snapshot_dirty'] = True
        ex.state_save()
        # Only a verified remote cancellation can confirm rollback.
        _ms['rollback_confirmed'] = ex.adapter.cancel_all(oid)
        ex.state_save()
        return None
    return placed


@deferred_operation
def open_market(ex, c):
    from executor_v2 import shares_for_open
    st = ex.state
    oid = str(c['outcome_id'])
    if not st.get('activation_valid') or not st.get('snapshot_known') or not st.get('ledger_known'):
        return False, '首次激活/实时余额订单/实验成本覆盖尚未确认'
    if not st.get('reward_baseline_known', False):
        return False, '尚未确认7笔历史reward基线'
    # 2026-11-01 halt 重构：L1（open_blocked）与 L2（halted）都拒绝新仓，
    # 但只有 L2 会撤单。L1 期间 maintain 完全照常 → 已有挂单和配对不受影响。
    if st.get('halted'):
        return False, '全局暂停（L2）/未知提交尚未解决'
    if st.get('open_blocked'):
        return False, f'暂停开新仓（L1）：{st.get("open_block_reason") or "未明"}'
    if unresolved(ex):
        return False, '未知提交尚未解决'
    if oid not in {str(x['outcome_id']) for x in ex.candidates}:
        return False, '不在独立授权候选范围'
    if ex.cfg.get('dynamic_candidates_enabled'):
        if oid not in st.get('eligible_market_ids', []):
            return False, '不在当前有效扫描授权窗口'
        if ex.now() >= number(st.get('authorization_expires_at', 0)):
            return False, '动态授权已到期'
    # 2026-11-01：配对下单结果未知（unknown）时不再 halt，改由本标志阻断重开。
    # 原实现靠 halt 阻止重发，去掉 halt 后必须有等效闸门——
    # 否则 intent 被判 absent 后 unresolved 变 False，下一轮会重新下单（重复下单风险）。
    # 该标志只在明确「裁决结果为 absent（确认未到达）」或成功提交后清除。
    # 2026-11-01 修复 P0-2（pair_blocked 自锁）：
    # 原实现无条件返回 False，而唯一的 pop 在 pair() 开头（本函数先 return，
    # pair() 永远进不去）→ 该市场**永久**无法交易，还占用 n_markets 名额。
    #
    # 正确语义：pair_blocked 的作用是「防止结果未知的单被重发」。
    # 这个风险只存在于「该市场仍有未了结意图」期间（unresolved 为真）。
    # 一旦 reconcile_intents 把意图裁决完（absent / final），
    # 就没有重复下单风险了 → 应当自动解除，恢复该市场。
    _ms_om = st['markets'].get(oid) or {}
    if _ms_om.get('pair_blocked'):
        if unresolved(ex):
            return False, str(_ms_om.get('pair_blocked'))
        # 意图已全部了结，但仍需过冷却期才解除。
        #
        # 为什么不能一了结就解除：
        # `test_timeout_never_resubmits` 锁定「超时未拿到 oid 的单绝不重发」——
        # absent 只证明「HL 此刻查不到这个 cloid」，而一笔迟到的响应仍可能到账，
        # 立刻重发就是在赌，可能重复开仓。
        # 因此改为**时间冷却 + 环境已变**双重条件：
        #   冷却期内不重开；到期后仍要求该市场无持仓、无挂单，才允许重新配对。
        ready_at = number(_ms_om.get('pair_blocked_until', 0))
        if ex.now() < ready_at:
            left = int(ready_at - ex.now())
            return False, f'配对阻断冷却中（剩余约 {left}s），不重开'
        if _ms_om.get('pos') or any(
                scoped_coin(o.get('coin'), {oid})
                for o in st.get('remote_orders', [])):
            return False, '配对阻断冷却已到期，但该市场仍有持仓/挂单，暂不重开'
        _ms_om.pop('pair_blocked', None)
        _ms_om.pop('pair_blocked_until', None)
        _ms_om.pop('pair_blocked_has_position', None)
        st.pop('pair_pending_note', None)
        # 阻断期间 phase 被置成 waiting 以占位，解除时必须归位为 closed，
        # 否则下面「prev.phase != 'closed' → 已在管理中」会继续拦住开仓，
        # 等于把自锁换个名目保留。
        if _ms_om.get('phase') == 'waiting' and not _ms_om.get('pos'):
            _ms_om['phase'] = 'closed'
        _ms_om['pair_blocked_cleared'] = (
            '冷却期结束且无持仓无挂单，阻断自动解除')
    # 缺口3修复（2026-10-29）：reopen_after_stop=false 之前只写在 config，
    # 开仓入口从未读取 → 单边止损清仓后可能重开同一市场。
    # 现在由 maintain/unwind 在"止损或故障导致清仓"时写 stopped_markets[oid]，
    # 只有满足 phase==closed（非残留管理）且未停用才允许再次入场。
    prev = st['markets'].get(oid)
    if prev is not None and prev.get('phase') != 'closed':
        return False, '已在管理中'
    if prev is not None:
        stop_info = st.get('stopped_markets', {}).get(oid)
        if stop_info and ex.cfg.get('reopen_after_stop', False) is not True:
            return False, ('该市场止损/故障后已停用：' + str(stop_info.get('reason', ''))
                           + '；reopen_after_stop=false 需人工解除')
    if (not ex.cfg.get('dynamic_candidates_enabled') and
            sum(m.get('phase') != 'closed' for m in st['markets'].values()) >= ex.cfg['n_markets']):
        return False, 'N=2已满'
    reason = candidate_reason(c, ex.now(), ex.cfg)
    if reason:
        return False, reason
    # 2026-10-31 修复（新市场永远开不出来）：
    # 原判据要求快照 age ≤ 5 秒，但快照刷新间隔是 15 秒 →
    # 每 15 秒里只有前 5 秒能开仓，其余 10 秒全是空窗。
    # 实测后果：19637 一直挂不上，每轮都落在空窗里。
    # 现在要求 age ≤ 快照刷新间隔（默认 15s）+ 少量余量，
    # 与快照节奏一致；快照本身仍然必须是「成功过的」（snapshot_known）。
    snap_max_age = number(ex.cfg.get('snapshot_max_age_seconds',
                                     ex.cfg.get('snapshot_refresh_seconds', 15) + 5))
    if (st.get('rest_budget_blocked') or st.get('snapshot_dirty')
            or ex.now()-st.get('snapshot_at', -1e30) > snap_max_age):
        return False, f'预算不足或开仓快照超过{snap_max_age:g}秒，冻结新仓'
    try:
        books = [ex.adapter._book(f'#{int(oid)*10+s}') for s in (0, 1)]
        bids = []
        for book in books:
            if abs(ex.now()-number(book['time'])/1000) > 5:
                return False, '开仓盘口时间未知/过期'
            bid, ask = (number(book['levels'][s][0]['px']) for s in (0, 1))
            if not 0 < bid <= ask < 1:
                return False, '双边盘口非法'
            mid = (bid+ask)/2
            if not ex.cfg['mid_min'] <= mid <= ex.cfg['mid_max']:
                return False, 'mid超出配置范围'
            if (ask-bid)/mid*100 > ex.cfg['max_spread_pct']:
                return False, '价差超过配置门槛'
            bids.append(float(price_wire(bid, buy=True, tif='Alo')))
        if abs(number(books[0]['time'])-number(books[1]['time'])) > 2000:
            return False, '双腿盘口时间差过大'
    except (KeyError, TypeError, ValueError, IndexError):
        return False, '实时双边盘口/预算未知'
    per = number(ex.cfg['capital_per_market'])
    if ex.cfg.get('dynamic_candidates_enabled'):
        per = min(per, max(0, number(st.get('dynamic_entry_limits', {}).get(oid, 0))),
                  max(0, total_cap(ex.cfg)-number(st.get('reserved_total', 0))),
                  max(0, number(st.get('free_cash', 0)) -
                      number(ex.cfg.get('experiment_principal_usdc', 0))*0.1))
        if per <= 0:
            return False, '无可分配资金'
    shares, why = shares_for_open(bids, per, ex.cfg.get('quote_mode', 'off'))
    if shares is None:
        return False, why
    limits = c['sdk_limits']
    if not minimum_order(bids, shares, limits):
        return False, f'{per:g}资金下不满足SDK最小份数/单腿名义；禁止扩大仓位'
    cost = shares*sum(bids)
    # 2026-10-30 方案C：总敞口上限与每市场上限改为按配置计算，不再写死 80/12。
    # 总敞口上限 = n_markets × capital_per_market（每个市场都满仓时的自然上限），
    # 现金缓冲 = 本金的 10%（保证任何时候都留有余量应对滑点与在途费用）。
    principal = number(ex.cfg.get('experiment_principal_usdc', 0))
    exposure_cap = total_cap(ex.cfg)
    cash_buffer = principal * 0.1
    if st.get('reserved_total', 0) + cost > exposure_cap:
        return False, f'总占款 {st.get("reserved_total", 0)+cost:.2f} 超过敞口上限 {exposure_cap:.2f}'
    if st.get('free_cash', 0) < cost + cash_buffer:
        return False, f'可用现金不足：需 {cost:.2f} + 缓冲 {cash_buffer:.2f}'
    if st.get('market_reserved', {}).get(oid, 0) + cost > per:
        return False, f'每市场库存和订单总占款超 {per:g}'
    placed = pair(ex, int(oid), bids, shares)
    if placed is None:
        return False, st.get('halt_reason') or st.get('pair_pending_note', '配对等待确认')
    st['markets'][oid] = {'outcome_id': int(oid), 'phase': 'waiting', 'orders': placed,
                          'sz': shares, 'notional': cost, 'opened': int(ex.now()),
                          'merges': 0}
    # 2026-11-01 业务日志：双边报价挂出一律记（每张单一条，含真实挂出时刻）。
    # 这是今天最缺的证据——判断 maker 挂出延迟时必须倒查 historicalOrders。
    try:
        _q = ' '.join('%s方@%s' % (sd, placed[sd]['px']) for sd in sorted(placed))
        ev('报价', market=oid, sz=shares, quote=_q,
           oids=','.join(str(placed[sd]['oid']) for sd in sorted(placed)),
           cost=round(float(cost), 4))
    except BudgetUnavailable:
        raise
    except Exception:
        pass
    st['reserved_total'] += cost
    st.setdefault('market_reserved', {})[oid] = cost
    st['free_cash'] -= cost
    ex.state_save()
    return True, why


def maintain(ex, positions):
    from executor_v2 import sports_schedule
    if positions is None or not ex.state.get('snapshot_known'):
        return [('all', '快照未知，停止新仓，保留全部残留管理')]
    results = []
    for oid, ms in list(ex.state['markets'].items()):
        if oid not in positions:
            ex.state['halted'] = True
            results.append((oid, '余额覆盖未知'))
            continue
        pos = {s: number(q) for s, q in positions[oid].items() if number(q) > 0}
        c = next((c for c in ex.candidates if str(c['outcome_id']) == oid), None)
        sports = sports_schedule(c.get('meta')) if c is not None else None
        past_clear = bool(sports) and (sports['scheduledStart']
                     - number(ex.cfg.get('pre_game_clear_seconds', 3600)) <= ex.now())
        ms['pos'] = pos
        recovery_active = False
        if ms.get('one_time_recovery'):
            from one_time_recovery import active as recovery_is_active
            recovery_active = recovery_is_active(ex, oid, pos)
        if ex.cfg.get('dynamic_candidates_enabled') and pos and not recovery_active:
            quantity_wait = _partial_fill_quantity(ex, oid, pos)
            if quantity_wait:
                results.append((oid, quantity_wait))
                continue
        # 配对是否成立要**提前**判定：$4 检查在 merge 分支之前，若在此处不知道
        # 已配对，就会把已经锁死 $1 兑付的双腿仓位当亏损单拆掉
        # （用户 2026-10-28 21:43 第 1 条）。
        paired = all(pos.get(s, 0) > 0 for s in ('0', '1'))
        ms['paired'] = paired
        ms['stop_applicable'] = not paired
        if paired:
            ms['stop_skip_reason'] = '配对已成立：该市场止损不适用（持有至 merge）'
        else:
            ms.pop('stop_skip_reason', None)
        # 2026-11-01：配对下单结果未知（pair_blocked）——只阻断该市场自动重开。
        #
        # 原实现把「某腿 submit 返回 unknown」当成配对失败：
        # halt + cancel_all + markets[oid] = {'phase': 'unwinding', ...}，
        # 副作用是把整个市场推成清仓态（20:04 实测 O20030/O20027 被误推）。
        # 但 unknown 的语义是「结果未知，等 cloid 裁决」，本来就有
        # reconcile_intents 的完整了结机制，不需要 halt。
        #
        # 安全约束（test_timeout_never_resubmits 锁定）：**结果未知的单绝不重发**。
        # 原实现靠 halt 实现这条，现在改用本市场级阻断，效果等价但不污染别处。
        # 解除路径：人工确认后清 pair_blocked（或该市场自然收口）。
        if ms.get('pair_blocked'):
            # 2026-11-01 修复 P0-2（pair_blocked 自锁 + 持仓静默）：
            # 原实现无条件 continue，排在 merge / wait_single / unwind **之前**，
            # 于是有持仓时也被跳过 → 不下止损、不挂卖单、不撤对侧、不告警。
            # 而现在只有 pair() 置位（未持仓）这一条路径，所以正常不会这样；
            # 但配对失败分支里 cancel_all 是 try/except: pass，撤单失败仍可能成交，
            # 那时就会出现「pair_blocked + 真实持仓」，仓位静默无人管。
            #
            # 正确语义：pair_blocked 只应阻断**新开仓**，绝不该阻断**已有持仓的管理**。
            if not pos and not past_clear:
                ms['phase'] = 'waiting'
                results.append((oid, '配对下单结果未知：已阻断该市场重开，待确认'))
                continue
            # 有持仓 → 落到后面的 wait_single / unwind 正常管理，不阻断
            ms['pair_blocked_has_position'] = (
                '配对阻断期间出现持仓（撤单竞态），已放行止损/退出管理')
            results.append((oid, '配对阻断但有持仓：放行止损与退出，同时保持不重开'))
        # closed is still reconciled; any unexpected exposure re-enters cleanup.
        # 2026-10-30 修复（closed 反复反跳）：实测事故里 18293/18294 已双双 closed、
        # 链上无仓无单，却因为本段把 phase 改回 unwinding 而无限循环
        # （closed → unwinding → closed → unwinding，每秒写一条状态）。
        # 根因：pos/remote 来自**本轮快照**，但快照可能滞后于刚刚完成的清仓/merge；
        # 且「closed 后出现残留」本身是罕见异常，不该靠改 phase 反复重试。
        # 现在：
        #   - 只有**确认快照新鲜**（snapshot_known 且未被标记 dirty）才据此判定
        #   - 残留存在时保持 closed 并**记录告警字段**，不自动改 phase 重入清仓
        #     （真正的残留由下一轮 openOrders/持仓复核驱动，不靠状态机抖动）
        remote = [o for o in ex.state.get('remote_orders', []) if scoped_coin(o['coin'], {oid})]
        fresh_snapshot = bool(ex.state.get('snapshot_known')) and not ex.state.get('snapshot_dirty')
        if ms.get('phase') == 'closed' and (pos or remote):
            # 2026-11-01 修复（closed 分支抢先 continue，掩盖 merge_pending 收口）：
            # merge_pending 的处理排在 :752，本分支在 :587，而这里 `continue`
            # 会直接跳过它 → 已确认的 merge 残仓永远排不掉。
            # 实测：phase=closed + merge_pending + 持仓 + snapshot_dirty 时，
            # maintain 返回「快照不新鲜」并 continue，merge 相关的卖出/对账全不执行。
            # 修法：有 merge_pending 时不在本分支提前返回，交给后面的 merge 收口逻辑；
            # 只有「纯 closed 残留（无 merge 在途）」才走这里的快照新鲜度保护。
            if ms.get('merge_pending'):
                # 有在途 merge：整个 closed 残留处理都跳过，交给后面 merge 收口
                # （那里会按 decreased + merge_fill_hashes 决定是否释放残仓去卖）。
                # 不能只 pass——否则会继续落入下面的 `if pos:` 把 phase 改成 unwinding，
                # 与 merge 收口抢同一个仓位。
                results.append((oid, 'closed 但有 merge 在途：交给 merge 收口，不做 closed 残留处置'))
                pass
            elif not fresh_snapshot:
                ms['closed_residue_unverified'] = 'closed 后疑似残留，但快照不新鲜，本轮不据此改状态'
                # 关键：本轮直接跳过该市场，不让后续分支用过期 pos 把它改回 waiting/unwinding
                results.append((oid, '快照不新鲜，closed 状态保持不变'))
                continue
            elif pos:
                # 有真实持仓 → 重新进入清仓，这是合理的
                ms['phase'] = 'unwinding'
                ex.state.update(halted=True, halt_reason='closed市场出现实际持仓残留')
            else:
                # 只有挂单残留、无持仓 → 撤单即可，不必把整轮打成 unwinding
                ms['closed_residue_orders'] = len(remote)
                # 2026-11-01 halt 重构：L1。只是有残留挂单，撤掉即可，不必停整台机器。
                block_open(ex, 'closed市场仍有挂单残留，待撤单复核',
                           source='closed_residue')
        if ms.get('merge_pending') and ex.state.get('merge_evidence_known'):
            pending = ms['merge_pending']
            decreased = all(number(pos.get(s, 0)) <= pending['before'][s]-pending['qty']+1e-8 for s in ('0', '1'))
            if decreased and ex.state.get('merge_fill_hashes', {}).get(oid):
                ms.pop('merge_pending')
                ms['merges'] = ms.get('merges', 0)+1
                # halted 不再把「仍有持仓」直接钉成 unwinding：若持仓已配对，
                # 下一轮应继续 merge 收口而不是被拆（用户 21:43 第 1 条）。
                if not pos:
                    ms['phase'] = 'closed'
                elif ms.get('phase') == 'alert':
                    ms['phase'] = 'alert'
                elif all(number(pos.get(s, 0)) > 0 for s in ('0', '1')):
                    ms['phase'] = 'waiting'
                elif ex.state.get('halted') or ms.get('phase') == 'unwinding':
                    ms['phase'] = 'unwinding'
                else:
                    ms['phase'] = 'waiting'
        # Manage only the unpaired remainder before the cutoff branch can re-enter.
        if ms.get('hold_qty', 0) > 0 and past_clear:
            held = number(ms['hold_qty'])
            residual = {s: number(q) - held for s, q in pos.items()
                        if number(q) - held > 1e-8}
            ms['hold_residual'] = residual
            try:
                results.append((oid, wait_single(ex, oid, residual) if residual
                                else '持有到结果中：已无残仓，等待比赛结束结算'))
            finally:
                ms['phase'] = 'holding_to_result'
            continue
        # Sports cutoff must remain reachable even during halt or local cleanup.
        if not past_clear and (ex.state.get('halted') or ms.get('phase') in ('alert', 'unwinding')):
            # 用户 2026-10-28 21:43 第 1 条：已配对的仓位不得因为全局 halted 被拆。
            # 配对腿的兑付已锁定在 $1/对，卖掉只会把确定的兑付换成不确定的现价。
            # 所以 halted 下：配对 → 继续 merge 收口；单边 → unwind 降敞口。
            if paired:
                results.append((oid, merge(ex, oid, pos, allow_when_halted=True)[1]))
                continue
            # 2026-10-31 修复（halt 下单边仍被秒平）：
            # 原实现在 halt 时对单边持仓直接 unwind —— 等于「一次主循环异常
            # 就把正在等配对的仓位清掉」。实测 19638 单边 8 分钟后因看板写入
            # 异常触发 halt，随即被卖。
            #
            # 但要注意区分两种「有持仓」：
            #   - phase 已经是 unwinding：这是**明确的清仓意图**
            #     （closed 后发现残留、或止损已触发），必须继续 unwind
            #   - phase 是 waiting：这是正常等待配对，halt 不应改变它
            # alert 语义是「卖不干净、需要告警」，它本身就是要清仓，必须继续卖；
            # 只有 waiting（正常等配对）才按 wait_single 处理。
            holding = any(number(q) > 0 for q in (pos or {}).values())
            if holding and ms.get('phase') == 'waiting':
                results.append((oid, wait_single(ex, oid, pos)))
                continue
            ms['phase'] = 'unwinding'
            results.append((oid, unwind(ex, oid, pos)))
            continue
        c = next((c for c in ex.candidates if str(c['outcome_id']) == oid), None)

        # ---- 体育盘清仓/持有分流（用户 2026-10-28 20:49 拍板 B 方案）----
        if c is not None:
            paired = all(pos.get(s, 0) > 0 for s in ('0', '1'))
            reason = candidate_reason(c, ex.now(), ex.cfg)
            sports = sports_schedule(c.get('meta'))
            past_clear = bool(sports) and (sports['scheduledStart']
                                           - number(ex.cfg.get('pre_game_clear_seconds', 3600))
                                           <= ex.now())
            if past_clear and _hold_through_result(c, ex.cfg):
                # 缺口1+2修复（2026-10-29）：
                #   ① 旧判断只看"两腿都>0"，YES 12份 + NO 1份 也会整仓进入持有，
                #      剩 11 份仍是单边敞口 → 现在只保护 min(两腿) 的配对数量。
                #   ② 旧分支直接 continue，不撤余单 → 旧买单可能继续成交，
                #      等于"截止后敞口还在增加" → 现在先撤净并确认。
                hold_qty = math.floor(min(number(pos.get('0', 0)), number(pos.get('1', 0))))
                if hold_qty > 0:
                    clean = ex.adapter.cancel_all(int(oid))
                    ms['cancel_confirmed'] = clean
                    ex.state['snapshot_dirty'] = True
                    if not clean:
                        # 撤单未确认时不进入持有：宁可报错也不让挂单继续吃
                        ex.state.update(halted=True,
                                        halt_reason='体育盘进入持有前撤单未确认，冻结敞口')
                        results.append((oid, '持有前撤单未确认：冻结并下轮复核，保留配对仓'))
                        continue
                    ms['phase'] = 'holding_to_result'
                    ms['hold_until'] = sports['scheduledStart']
                    ms['hold_qty'] = hold_qty
                    # 不等量残仓记下来：配对部分持有到结果，残仓仍受单边规则管理
                    residual = {s: number(pos[s]) - hold_qty for s in ('0', '1')
                                if number(pos.get(s, 0)) - hold_qty > 1e-8}
                    ms['hold_residual'] = residual
                    if residual:
                        # 残仓不在本分支处理：下一轮由 maintain 顶部
                        # phase==holding_to_result 的残仓分支统一走单边规则
                        # （这里同时调用会让 wait_single 一轮执行两次、撤单口径打架）。
                        results.append((oid, f'开赛前已配对 {hold_qty} 份 → 持有到结果；'
                                             f'余仓 {sum(residual.values()):g} 份仍属单边，'
                                             f'下一轮起受止损管理'))
                    else:
                        results.append((oid, '开赛前已全配对 → 持有到比赛结束（只监控，不新开不加仓）'))
                    continue
            if past_clear and not paired:
                # 2026-10-30 修复：已经收口（无持仓、merge 完成、无挂单）的市场
                # 不该再被这条规则重判。原实现无条件判「未形成双边 → 清仓」，
                # 于是 O18292 在 merges=1、仓位清零后仍被反复标成「开赛前未形成双边」，
                # 继而 halt() 把 phase 改回 unwinding → unwind() 撤单失败 →
                # 「清仓撤单未确认」自锁，状态每秒写一条但永不前进。
                if not pos and not remote:
                    if fresh_snapshot:
                        ms['phase'] = 'closed'
                        results.append((oid, '市场已收口（无持仓无挂单），跳过体育盘清仓判定'))
                    else:
                        # Other markets can dirty the shared snapshot during this loop.
                        # An empty stale view cannot prove either exposure or closure.
                        # Keep the cutoff entry gate and wait for a fresh reconciliation.
                        results.append((oid, '截止市场暂无仓单，快照待复核，保持状态'))
                    continue
                # 分支 2：开赛前 1h 仍无双边 → 直接清仓，不留到开赛。
                if not ex.cfg.get('dynamic_candidates_enabled'):
                    ex.state.update(halted=True,
                                    halt_reason='体育盘开赛前未形成双边 → 清仓')
                ms['entry_closed_reason'] = '体育盘开赛前未形成双边 → 清仓'
                ms['phase'] = 'unwinding'
                ex.state.setdefault('stopped_markets', {})[oid] = {
                    'reason': '体育盘开赛前未形成双边', 'at': ex.now()}
                results.append((oid, unwind(ex, oid, pos)))
                continue
            if reason:
                # 用户 2026-10-28 21:53 冻结漏洞 1：candidate_reason 是**入场**门槛，
                # 里面混着 incentive_end_time 过期、pool 低于门槛、safety_valid_until
                # 过期、距结算 <6h 等与持仓无关的检查。用它驱动退出，会把已锁 $1/对
                # 的配对仓在结算前 6h 按 bid 卖掉，白吃价差与 taker 费。
                # 配对一律落到 merge 收口；只有单边才按 reason 清仓。
                if paired:
                    results.append((oid, merge(ex, oid, pos, allow_when_halted=True)[1]))
                    continue
                ms['phase'] = 'unwinding'
                results.append((oid, unwind(ex, oid, pos)))
                continue
        elif c is None:
            # 用户 2026-10-28 21:53 冻结漏洞 2：候选列表变化（重启换授权、
            # 候选被剔除）不该拆已配对仓位 —— merge 不需要候选元数据。
            if paired:
                results.append((oid, merge(ex, oid, pos, allow_when_halted=True)[1]))
                continue
            ms['phase'] = 'unwinding'
            results.append((oid, unwind(ex, oid, pos)))
            continue
        # Actual FIFO cost/exit value, never quoted entry, enforces market stop4.
        # 用户 2026-10-28 21:43 第 1 条：**已配对仓位不适用**。
        # 历史亏损已经发生，但配对腿的兑付锁定在 $1/对；此时 unwind 等于用
        # 确定的兑付换不确定的现价，且把「已锁的 $1」变成亏损实现。
        # 缺口1配套（2026-10-29）：体育盘已将配对部分转入 holding_to_result 时，
        # 这里只剩残仓要管。wait_single 收到的必须是**残仓**（减掉已锁定的配对量），
        # 否则它按整仓算止损阈值/撤单口径，与持有部分互相矛盾。
        if ms.get('phase') == 'holding_to_result' and pos:
            held = number(ms.get('hold_qty', 0))
            residual = {s: number(q) - held for s, q in pos.items() if number(q) - held > 1e-8}
            if residual:
                results.append((oid, wait_single(ex, oid, residual)))
            else:
                results.append((oid, '持有到结果中：已无残仓，等待比赛结束结算'))
            continue
        # 2026-11-05 修复单市场止损误触发（事故 12:12:21）：
        #   薄盘口把 #242581 的保守退出均价算成 0.0523（真实 bid 0.3408），
        #   market_exit_net 瞬间跌破 -4，单次采样即 halt 全站；12 秒后估值自己
        #   回到正常。原实现与总熔断不对称：总熔断有连续确认+合并豁免，这里没有。
        # 现在补齐三层保护（用户 12:38/12:40 拍板）：
        #   L1 估值不可执行 → 该市场本轮不做止损判定（见 collect_fills 的
        #      valuation_unreliable），等 VALUATION_RETRY_SEC 后重试；
        #   L2 连续确认 → 需 MARKET_STOP_CONFIRM_SAMPLES 次采样成立才真止损；
        #   L3 正在退出/合并中的市场不触发全站 halt（它自己就在收口）。
        _mk_unreliable = (ex.state.get('valuation_unreliable') or {})
        _mk_key = f'#{int(oid)*10+0}'
        _mk_key1 = f'#{int(oid)*10+1}'
        # 2026-11-05：估值不可执行只暂停风控判定 VALUATION_RETRY_SEC 秒。
        # 到期自动失效，让该市场重新参与止损判断（薄深度通常秒级恢复，
        # 若 5 分钟后仍不可执行，下一轮会重新标记并再次计时）。
        _mk_now_ms = int(ex.now()*1000)
        _mk_blocked = False
        for _k in (_mk_key, _mk_key1):
            _rec = _mk_unreliable.get(_k)
            if _rec and _mk_now_ms - int(_rec.get('at_ms') or 0) <= VALUATION_RETRY_SEC*1000:
                _mk_blocked = True
                break
        _stop_net = ex.state.get('market_exit_net', {}).get(oid, 0)
        _mk_streak = ex.state.setdefault('market_stop_streak', {})
        _already_closing = (ms.get('phase') in ('unwinding', 'holding_to_result')
                            or bool(ms.get('merge_pending')))
        if (not paired) and _stop_net <= -4 and not _mk_blocked and not _already_closing:
            _mk_streak[oid] = int(_mk_streak.get(oid, 0)) + 1
            if _mk_streak[oid] >= MARKET_STOP_CONFIRM_SAMPLES:
                ex.state.update(halted=True,
                                halt_reason=f'每市场实际成本保守退出净亏达到4'
                                            f'（连续{_mk_streak[oid]}次确认）')
                ms['phase'] = 'unwinding'
                # 缺口3：$4 硬退出后该市场停用（reopen_after_stop=false 时不再入场）
                ex.state.setdefault('stopped_markets', {})[oid] = {
                    'reason': '每市场累计亏损达 $4 硬退出', 'at': ex.now()}
                results.append((oid, unwind(ex, oid, pos)))
                continue
        elif _mk_blocked or _already_closing or _stop_net > -4:
            # 未达确认/估值不可信/已在收口 → 计数归零，避免陈旧计数累积后误触发
            if _mk_streak.get(oid):
                _mk_streak.pop(oid, None)
        if recovery_active:
            from one_time_recovery import maintain as maintain_recovery
            results.append((oid, maintain_recovery(ex, oid)))
            continue
        if ms.get('merge_pending'):
            pending = ms['merge_pending']
            decreased = all(number(pos.get(s, 0)) <= pending['before'][s]-pending['qty']+1e-8 for s in ('0', '1'))
            # 2026-11-01：ack=False 的 pending 不再需要在这里清理或阻塞——
            # 它只是「成交归属凭据」，merge() 已经允许在其存在时重试。
            # 若这次 merge 其实成功，成交回来时正需要它来归属；
            # 若没成功，下一次 merge 会用新的 pending 覆盖它。
            # 因此这里只处理 ack!=False 的「真正在途」情形。
            if pending.get('ack') is False:
                if decreased:
                    # 持仓确实减少了 → 说明 merge 其实成功，pending 使命完成
                    ms.pop('merge_pending')
                    ex.state_save()
                    results.append((oid, 'ack=False 但持仓已减少，merge 实际成功'))
                    try:
                        ev('merge-假拒实成功', oid=oid,
                           pending_qty=pending.get('qty'),
                           note='ack=False 但持仓已减少')
                    except BudgetUnavailable:
                        raise
                    except Exception:
                        pass
                    continue
                # 持仓没减少：ack=False 表示「请求未被接受」，
                # pending 仅作成交归属凭据，必须**主动重新提交 merge**，
                # 否则会退化成修复前那种「永不重试」的死锁。
                # （这个 if 块在 elif 链之外，不会自动落到下面的 merge() 分支，
                #   所以必须在这里显式调用。）
                results.append((oid, merge(ex, oid, pos)[1]))
                continue
            if decreased and ex.state.get('ledger_known') and ex.state.get('merge_fill_hashes', {}).get(oid):
                ms.pop('merge_pending')
                # halted 不再把「仍有持仓」直接钉成 unwinding：若持仓已配对，
                # 下一轮应继续 merge 收口而不是被拆（用户 21:43 第 1 条）。
                if not pos:
                    ms['phase'] = 'closed'
                elif ms.get('phase') == 'alert':
                    ms['phase'] = 'alert'
                elif all(number(pos.get(s, 0)) > 0 for s in ('0', '1')):
                    ms['phase'] = 'waiting'
                elif ex.state.get('halted') or ms.get('phase') == 'unwinding':
                    ms['phase'] = 'unwinding'
                else:
                    ms['phase'] = 'waiting'
                ms['merges'] = ms.get('merges', 0)+1
            results.append((oid, '等待真实merge双腿成交及持仓变化；不重发/不重挂'))
        elif all(pos.get(s, 0) > 0 for s in ('0', '1')):
            # 正常路径：此处已在 halted/alert 门之后，不需要放宽 flag
            results.append((oid, merge(ex, oid, pos)[1]))
        elif pos:
            results.append((oid, wait_single(ex, oid, pos)))
        elif fresh_snapshot and not remote and not unresolved(ex):
            ms['phase'] = 'closed'
            results.append((oid, '余额清零且订单撤净确认；下一轮允许授权范围补位'))
        else:
            results.append((oid, '持续维护双边挂单'))
    ex.state_save()
    # 2026-11-01 业务日志：每轮一行汇总，**只在内容变化时写**（用户 23:52 指定）。
    # 内容 = 各市场 phase/持仓/挂单数 + 预算用量 + halt 状态。
    # 系统稳定时这一段几乎不产生日志；一旦有任何状态迁移就留痕。
    try:
        _parts = []
        for _oid in sorted(ex.state.get('markets', {})):
            _m = ex.state['markets'][_oid]
            _np = sum(number(q) for q in (_m.get('pos') or {}).values())
            _no = len(_m.get('orders') or {})
            _parts.append('%s:%s/%s份/%s单' % (
                _oid, _m.get('phase', '?'), ('%g' % _np), _no))
        _bs = ex.state.get('rest_budget_stats') or {}
        ev_change('汇总', key='round-summary',
                  markets=' '.join(_parts) or 'none',
                  charged=_bs.get('total_charged'), denied=_bs.get('denied'),
                  halted=bool(ex.state.get('halted')),
                  blocked=ex.state.get('open_blocked'),
                  cash=(round(float(ex.state['free_cash']), 2)
                        if ex.state.get('free_cash') is not None else None))
    except BudgetUnavailable:
        raise
    except Exception:
        pass
    return results


def _estimate_exit_value(ex, oid, side, qty):
    '按当前盘口 bid 逐档模拟卖出，返回可得金额（USD）。拿不到盘口返回 None。\n\n    历史版本 新增，用于 P0-1 修复：止损判断需要「此刻卖出能拿回多少」。\n    算法与 collect_fills 里 inventory_exit 的估值保持一致（同样按 bid 逐档、\n    同样打 0.998 折），保证两处口径统一，不会出现「账本说亏、止损说没亏」。\n\n    保守方向：取 bid 且打折，宁可低估回收 → 更容易触发止损（安全侧）。\n    '
    coin = f'#{int(oid)*10+int(side)}'
    try:
        book = ex.adapter._book(coin, force=True)
    except TypeError:
        try:
            book = ex.adapter._book(coin)
        except BudgetUnavailable:
            raise
        except Exception:
            return None
    except BudgetUnavailable:
        raise
    except Exception:
        return None
    if not book or not book.get('levels') or not book['levels'][0]:
        return None
    left = number(qty)
    proceeds = 0.0
    for level in book['levels'][0]:
        if left <= 1e-8:
            break
        take = min(left, number(level['sz']))
        try:
            execution_px = float(price_wire(Decimal(str(level['px']))*Decimal('.998'),
                                            tif='Ioc'))
        except (ValueError, TypeError, KeyError):
            return None
        proceeds += float(sell_proceeds(take, execution_px))
        left -= take
    if left > 1e-8:
        # 深度不足：已有部分按盘口算，剩余按最后一档保守估
        try:
            last_px = float(price_wire(Decimal(str(book['levels'][0][-1]['px'])),
                                       tif='Ioc'))
        except (ValueError, TypeError, KeyError, IndexError):
            return None
        proceeds += float(sell_proceeds(left, last_px))
    return proceeds


@deferred_operation
def _partial_fill_quantity(ex, oid, pos, replenish=False, original_path=False,
                           return_reason=None):
    """Cap C buys at the inventory gap; repair excess orders at their maker quote.

    Unaffected single legs may continue through the existing hedge decision.
    Cancel and replace are separate snapshot generations. Journal commitments absent
    from openOrders remain blocking until the existing cloid/fill reconciliation ends.
    """
    ms = ex.state['markets'][oid]
    st = ex.state
    if not st.get('snapshot_known') or st.get('snapshot_dirty'):
        return '部分成交数量待新鲜余额/订单快照复核' if replenish else None
    gap = number(pos.get('0', 0)) - number(pos.get('1', 0))
    missing = '1' if gap > 0 else '0'
    allowance = {missing: abs(gap), str(1-int(missing)): 0.0}
    orders = [o for o in st.get('remote_orders', [])
              if scoped_coin(o.get('coin'), {oid}) and o.get('side') == 'B']
    live_ids = {str(o['oid']) for o in orders}
    live_cloids = {str(o.get('cloid')) for o in orders if o.get('cloid')}
    pending = [i for i in journal(ex).values()
               if i.get('buy') and scoped_coin(i.get('coin'), {oid})
               and i.get('status') in ('unknown', 'submitted', 'awaiting_fill')
               and (i.get('status') != 'submitted'
                    or (str(i.get('oid')) not in live_ids
                        and str(i.get('client_id')) not in live_cloids))]
    # Stop adding to the filled/net-long side before shrinking its paired buy.
    # Each cancellation returns for a fresh snapshot, so its ordering matters.
    for side in (str(1-int(missing)), missing):
        side_coin = f'#{int(oid)*10+int(side)}'
        buys = [o for o in orders if o['coin'] == side_coin]
        unobserved = sum(number(i['qty']) for i in pending
                         if i.get('coin') == side_coin
                         and str(i.get('oid')) not in live_ids
                         and str(i.get('client_id')) not in live_cloids)
        if sum(number(o['sz']) for o in buys) <= max(0, allowance[side]-unobserved) + 1e-8:
            continue
        # Keep cancellation evidence in the adapter; never mutate cached orders or
        # mark intents final here. Any fill during cancellation changes the next gap.
        ms['quantity_repair_pending'] = True
        ms['quantity_recheck'] = '超额买单撤单中，等待终态及新余额/成交对账'
        st['snapshot_dirty'] = True
        clean = _single_leg_cancel(ex, oid, str(1-int(side)), ms,
                                   keep_side=1-int(side))
        ms['quantity_cancel_confirmed'] = clean
        ex.state_save()
        return ('超额买单已撤，等待新余额/成交对账' if clean
                else '超额买单撤单未确认，禁止补单并继续复核')
    if not replenish:
        return None
    if abs(gap) <= 1e-8:
        return '净缺口为0，不新增配对买单'
    coin = f'#{int(oid)*10+int(missing)}'
    if pending:
        ms['quantity_recheck'] = '存在未决买入承诺，等待原cloid/成交对账，不重发'
        return ms['quantity_recheck']
    covered = sum(number(o['sz']) for o in orders if o['coin'] == coin)
    qty = abs(gap) - covered
    ms['quantity_gap'] = {'side': missing, 'net': abs(gap), 'resting': covered,
                          'additional': max(0, qty)}
    ms.pop('quantity_recheck', None)
    if qty <= 1e-8:
        # 2026-11-07 修复（对冲永不触发）：原来这里直接 return 字符串，
        # 于是 wait_single 提前返回，后面的 hedge 评估整段被跳过。
        # 「对侧 maker 挂满净缺口」是配对策略的正常状态，不该关掉对冲评估。
        #
        # 现在：把原因记进 state，通过 return_reason 出参交给调用方，
        # 返回值仍为 None 表示「补单这一步无需动作」，但**不阻断后续评估**。
        reason = '对侧已有买单覆盖真实净缺口，保留原单等待配对'
        ms['quantity_covered'] = reason
        if return_reason is not None:
            return_reason.append(reason)
        return None
    ms.pop('quantity_covered', None)
    c = next((c for c in ex.candidates if str(c['outcome_id']) == oid), None)
    if (not st.get('activation_valid') or st.get('halted') or st.get('open_blocked')
            or not st.get('ledger_known') or st.get('rest_budget_blocked')
            or ex.now() >= number(st.get('authorization_expires_at', 0))
            or ms.get('phase') != 'waiting' or ms.get('pair_blocked')
            or ms.get('merge_pending') or ms.get('hold_qty', 0)
            or c is None or candidate_reason(c, ex.now(), ex.cfg)):
        return '净缺口待配对：当前授权/风险状态不允许新增买单，继续原单腿管理'
    windows = st.get('authorization_windows', [])
    at_ms = int(ex.now()*1000)
    active = next((w for index, w in enumerate(windows)
                   if w['at_ms'] <= at_ms < w['end_ms']
                   and (index+1 == len(windows) or at_ms < windows[index+1]['at_ms'])), None)
    if active is not None and oid not in active['markets']:
        # 与 c_runtime.order_commitment / ledger.register_order_commitment
        # 完全同步的兜底（2026-11-08）：空窗口不该剥夺已授权市场的补单权。
        active = next((w for w in reversed(windows)
                       if oid in (w.get('markets') or [])
                       and w['at_ms'] <= at_ms < w['end_ms']), None)
    if active is None or oid not in active['markets']:
        return '净缺口不在当前买入授权窗口，继续管理已有残仓及跨窗口成交'
    from executor_v2 import sports_schedule
    sports = sports_schedule(c.get('meta'))
    if sports and sports['scheduledStart'] - number(
            ex.cfg.get('pre_game_clear_seconds', 3600)) <= ex.now():
        return '体育盘已到清仓截止，禁止补买'
    max_age = number(ex.cfg.get('snapshot_max_age_seconds',
                                ex.cfg.get('snapshot_refresh_seconds', 15)+5))
    if ex.now()-st.get('snapshot_at', -1e30) > max_age:
        return '净缺口待新鲜快照，禁止补买'
    if (original_path and not ms.get('quantity_repair_pending')
            and number(ms.get('merges', 0)) <= 0):
        return None
    # Excess-order replacements and confirmed-merge residuals use the original
    # maker quote. Keep the original timeout path for other single-leg waits.
    # Never round up to a minimum order; keep the target/stop denominator intact.
    quote = ms.get('orders', {}).get(missing, {}).get('px')
    if quote is None:
        return '缺少原始maker报价，保留残仓按原止损/截止管理'
    px = float(price_wire(quote, buy=True, tif='Alo'))
    limits = c.get('sdk_limits') or {}
    minimum = max(Decimal('1'), Decimal(str(limits.get('min_notional_per_leg', 0))))
    if (not limits.get('verified') or not limits.get('evidence')
            or not isinstance(limits.get('sz_decimals'), int)
            or not 0 <= limits['sz_decimals'] <= 8 or qty != int(qty)
            or qty < number(limits.get('min_shares', 1))
            or Decimal(str(qty))*Decimal(str(px)) < minimum):
        ms['quantity_skip_reason'] = '真实净缺口不足最小买入量/名义：不扩大、不强卖，继续原止损/截止管理'
        return ms['quantity_skip_reason']
    cost = qty*px
    if (number(st.get('reserved_total', 0)) + cost > total_cap(ex.cfg)
            or number(st.get('market_reserved', {}).get(oid, 0)) + cost
                > number(ex.cfg['capital_per_market'])
            or number(st.get('free_cash', 0)) < cost
                + number(ex.cfg.get('experiment_principal_usdc', 0))*.1):
        return '净缺口补单预算不足，保留预留及原单腿管理，不扩大仓位'
    ms.pop('quantity_skip_reason', None)
    intent = submit(ex, coin, True, int(qty), px, 'Alo')
    # Until the next remote snapshot accounts for it, reserve the full possible
    # commitment, including a timeout or deferred request. Do not reset old risk.
    if intent.get('status') in ('submitted', 'unknown'):
        ms.pop('quantity_repair_pending', None)
        st['reserved_total'] = number(st.get('reserved_total', 0)) + cost
        st.setdefault('market_reserved', {})[oid] = number(
            st.get('market_reserved', {}).get(oid, 0)) + cost
        st['free_cash'] = number(st.get('free_cash', 0)) - cost
        ex.state_save()
    return f'按原maker报价补真实净缺口 {qty:g} 份；状态={intent.get("status")}'


def _single_leg_cancel(ex, oid, side, ms, keep_side='opposite'):
    """Real cancellation evidence lives in the adapter, never inferred from empty state."""
    other = 1 - int(side) if keep_side == 'opposite' else keep_side
    leg_key = f'{int(oid)}:{side}:{other}'
    if ms.get('cancel_retry_key') != leg_key:
        ms.pop('cancel_retry_at', None)
        ms.pop('cancel_attempts_leg', None)
    ms['cancel_retry_key'] = leg_key
    if ex.now() < ms.get('cancel_retry_at', 0):
        raise BudgetUnavailable('撤单重试等待调度', retry_at=ms['cancel_retry_at'])
    clean = ex.adapter.cancel_all(int(oid), keep_side=other)
    if clean:
        ms['cancel_confirmed_leg'] = leg_key
        ms.pop('cancel_attempts_leg', None)
        ms.pop('cancel_retry_at', None)
        ms.pop('cancel_gave_up', None)
    else:
        attempts = int(ms.get('cancel_attempts_leg', 0)) + 1
        ms['cancel_attempts_leg'] = attempts
        ms['cancel_retry_at'] = ex.now() + min(60, 2**min(attempts, 6))
    return clean


@deferred_operation
def wait_single(ex, oid, pos):
    """Keep the original opposite maker; never create an unapproved hedge buy."""
    from executor_v2 import sports_schedule
    ms = ex.state['markets'][oid]
    c = next((c for c in ex.candidates if str(c['outcome_id']) == oid), None)
    sports = sports_schedule(c.get('meta')) if c is not None else None
    if sports and (sports['scheduledStart']
                   - number(ex.cfg.get('pre_game_clear_seconds', 3600)) <= ex.now()):
        # Holding residuals also reach this entry point. Apply the existing cutoff
        # exit before ledger waits or hedge buys; unwind preserves hold_qty pairs.
        ms['hedge_skip_reason'] = '体育盘已到清仓截止：禁止新增买入，按既有单腿规则退出'
        return unwind(ex, oid, pos)
    side = next(iter(pos))
    lot = ex.state.get('inventory_exit', {}).get(f'#{int(oid)*10+int(side)}')
    target = number(ms.get('sz', 0))
    # 2026-10-30 修复（成交/账本时序竞争）：
    # 实测事故——O18294 的 NO 边在 10:52:43 成交，账本尚未写入该笔成交，
    # 10:52:47（3.3 秒后）wait_single 看到 lot is None 就判「成本未知」并清仓，
    # 把本该等 YES 边配对、赚 maker-fill 分的仓位直接卖掉，白付手续费。
    #
    # 账本滞后是**正常时序**，不是故障。因此：
    #   - 账本尚未记录该腿成本 → 给一个短暂的「等账本」宽限（按轮计数），
    #     期间只保持现状、不卖、不判止损，让 collect_fills 把成交写进来
    #   - 宽限期用尽仍无成本 → 才按原逻辑 fail-closed 清仓
    #   - ledger_known 整体为假（不是单腿缺失）仍立即 fail-closed，不等待
    GRACE = int(ex.cfg.get('ledger_lag_grace_rounds', 6))
    # 2026-11-01 业务日志：单边持有起点。dedup 键含 oid+side，
    # 同一腿本轮只记一次（single_since 复位后新腿会再记一次）。
    try:
        import v2_events
        _c = f'#{int(oid)*10+int(side)}'
        _sz = (number(pos.get(side)) if isinstance(pos, dict) else number(pos))
        v2_events.ev_change('单边开始', key='single:%s:%s' % (oid, side),
                            coin=_c, market=oid, side=str(side),
                            sz=('%g' % _sz),
                            ledger_known=bool(ex.state.get('ledger_known')))
    except BudgetUnavailable:
        raise
    except Exception:
        pass
    # 2026-10-31 修复（一次数据异常就清仓）：
    # 原实现只要 ledger_known 为假就强制清仓。但 ledger_known 会被**任何一次**
    # collect_fills 异常打成 False（实测：看板写入异常也会连带），
    # 于是「账本暂时读不到」= 「立刻卖掉正在等配对的仓位」。
    # 现在：账本未知时**不卖**，保持持有，用链上盘口做保守止损估值
    # （成本未知则不下止损结论，只等账本恢复或对侧成交）。
    if not ex.state.get('ledger_known'):
        ms['ledger_unknown_rounds'] = int(ms.get('ledger_unknown_rounds', 0)) + 1
        ms['phase'] = 'waiting'
        ms['stop_applicable'] = False
        ms['stop_skip_reason'] = '账本暂不可读：不做止损判断，保持持有等账本恢复'
        other = 1-int(side)
        clean = _single_leg_cancel(ex, oid, side, ms)
        ms['cancel_confirmed'] = clean
        return (f'账本暂不可读（第 {ms["ledger_unknown_rounds"]} 轮）：'
                f'保持持有、不判止损，等账本恢复或对侧成交')
    ms.pop('ledger_unknown_rounds', None)
    # 2026-10-31 修复（单边即清仓，永远配不上对）：
    # 实测——今日 6 笔 Buy 全部在数秒内被 Sell，0 笔 Merge。
    # 根因就是下面这个判断：账本还没写入本笔成交时 lot['qty'] 为 0，
    # 与链上 pos[side] 不等 → 判「成本未知」→ 强制清仓。
    # 而历史能成功 merge 的 O17347/O18292，恰恰是旧逻辑「单边就继续等」。
    #
    # 现在改为：账本滞后**不再是卖出的理由**。
    #   - 账本有成本 → 用它算止损（原路径）
    #   - 账本没有/数量对不上 → 用**成交价兜底**估成本，照常判止损，
    #     但绝不因为「查不到成本」就清仓
    # 真正的卖出理由只剩两个：价格止损、清仓截止（截止由 maintain 上游处理）。
    lagging = (lot is None or target <= 0
               or abs(number(lot['qty'])-number(pos[side])) > 1e-8)
    if lagging:
        # 兜底成本：用本轮该腿的成交均价（state 里由 collect_fills 记录），
        # 再不行就用当前 best bid 反推——宁可保守（成本估高→止损更早触发），
        # 也不要凭空假设成本为 0（那会让止损永不触发）。
        fallback_cost = None
        # 从账本 events 取该腿最近一笔 Buy 的实际成交价（真实数据，不是估算）
        try:
            coin = f'#{int(oid)*10+int(side)}'
            ledger = (getattr(ex, 'ledger', None)
                      or getattr(getattr(ex, 'acct', None), 'ledger', None))
            if ledger is None:
                raise ValueError('no ledger')
            row = ledger.db.execute(
                'SELECT payload FROM events ORDER BY rowid DESC LIMIT 200').fetchall()
            for (raw,) in row:
                ev = json.loads(raw)
                if str(ev.get('coin')) == coin and ev.get('dir') == 'Buy':
                    px = number(ev.get('px'))
                    if px > 0:
                        fallback_cost = px * number(pos[side])
                        ms['cost_fallback_from'] = f"账本最近Buy成交价 {px}"
                        break
        except BudgetUnavailable:
            raise
        except Exception:
            fallback_cost = None
        ms['ledger_lag_note'] = ('账本成本缺失，改用成交均价兜底'
                                 if fallback_cost is not None
                                 else '账本成本缺失且无成交均价，暂不判止损、只等配对')
        if fallback_cost is None:
            # 连兜底价都没有：保持持有、不卖、不判止损，等账本或对侧成交
            ms['phase'] = 'waiting'
            ms['stop_applicable'] = True
            other = 1-int(side)
            clean = _single_leg_cancel(ex, oid, side, ms)
            ms['cancel_confirmed'] = clean
            return '单边持有中：账本成本缺失，暂不判止损；保留对侧挂单等配对'
        # 2026-11-01 修复 P0-1（价格止损是死代码）——断链二：
        # 原实现：
        #   'exit_value': str(number(ms.get('last_exit_value') or fallback_cost))
        # 而 `last_exit_value` 在全代码库**从未被写入**（grep 确认只有这一处读取），
        # 于是 exit_value == fallback_cost == cost →
        # `exit_value - cost` 恒为 0 → 止损条件永不成立（实测确认）。
        #
        # 正确语义：exit_value 必须是「此刻卖出这腿能拿回多少」，
        # 即按当前盘口 bid 逐档模拟的可得金额。这里用 _book 真实现价计算。
        # 若盘口拿不到，退回成本价（等价于「不判止损」，与原来的兜底一致，
        # 不会误伤），但会把原因写进 state 供排查。
        exit_val = _estimate_exit_value(ex, oid, side, pos[side])
        if exit_val is None:
            exit_val = fallback_cost
            ms['exit_value_unavailable'] = '盘口不可用，暂按成本价估值（不判止损）'
        else:
            ms.pop('exit_value_unavailable', None)
        lot = {'qty': str(pos[side]), 'cost': str(fallback_cost),
               'exit_value': str(exit_val)}
        ms['cost_fallback'] = True
    else:
        ms.pop('ledger_lag_rounds', None)
        ms.pop('ledger_lag_note', None)
        ms.pop('cost_fallback', None)
    # 2026-11-01 修复 P1-1 配套：target 缺失/为 0 时不得做除法。
    # pair() 的失败分支曾建出不带 sz 的市场字典，一旦有持仓就 ZeroDivisionError
    # → tick 崩 → halt，且当轮 maintain 后续市场全部跳过。
    # 这里用「当前持仓量」作为 target 的兜底（满仓时 target==持仓，等价语义），
    # 并在 state 里留痕，便于排查为何走了兜底。
    if target <= 0:
        target = max(number(pos[side]), 1.0)
        ms['sz_missing_fallback'] = (
            f'市场 sz 缺失，按当前持仓 {target:g} 兜底计算止损阈值')
    threshold = number(pos[side])*number(ex.cfg['stop_loss_usd_per_market'])/(target*2)
    ms['single_stop_threshold'] = threshold
    # 显式记录「止损此刻是否适用」（用户 2026-10-28 21:43 第 2 条）。
    # 走到 wait_single 说明当前是单边，故此处止损适用；一旦两腿齐备，
    # maintain 会在 merge 之前把 stop_applicable 置 False 并写 stop_skip_reason。
    ms['stop_applicable'] = True
    ms.pop('stop_skip_reason', None)
    if number(lot['exit_value'])-number(lot['cost']) <= -threshold:
        ms.update(phase='unwinding', stop_triggered=True)
        # 缺口3：真止损后该市场停用，避免清完立刻在同一市场重开
        ex.state.setdefault('stopped_markets', {})[oid] = {
            'reason': '单边触发价格止损', 'at': ex.now()}
        return unwind(ex, oid, pos)
    other = 1-int(side)
    # Cancellation confirmation and invalidation are owned by LiveAdapter.
    clean = _single_leg_cancel(ex, oid, side, ms)
    ms['cancel_confirmed'] = clean
    # Real failures retry with bounded backoff; budget deferrals propagate separately.
    if not clean:
        # 2026-11-01 修复 P1-3（撤单退避被误判为「真撤不掉」→ 强平 + 永久 halt）：
        # unwind() 早就区分了「查询没成功（预算退避）」和「确实还有单撤不掉」，
        # 这里却一刀切。实测后果：持仓只浮亏 $0.05（阈值 $2），
        # 仅因 cancel_all 撞上 _oo_backoff_until 返回 False →
        # 立刻 halt + phase=unwinding → 下一轮直接挂卖单强平。
        # 这正是 10-31 修过的「单边被秒平」事故重演。
        # 而且这个 halt_reason 不在 AUTO_RESUMABLE 里 → 永久 halt 需人工。
        backoff_until = getattr(ex.adapter, '_oo_backoff_until', 0)
        if ex.now() < backoff_until:
            # 退避中：本轮不作结论，保持持有，不改 phase、不 halt
            ms['cancel_recheck'] = '查挂单落空（预算退避中），本轮不作结论，不据此 halt'
            ex.state_save()
            return ('单边持有中：撤单复核退避中（剩余约 '
                    f'{int(backoff_until - ex.now())}s），本轮不判止损、不强制清仓')
        # 真撤不掉（查询成功但仍有单）
        # 2026-11-01 halt 重构：这是 L1，不是 L2。
        # 单边持仓 + 对侧撤不掉 ≠ 要清仓。清仓会把仓位以更差价格卖出。
        # 改为只冻结新仓，**不动 phase**（保持 waiting 继续等配对/止损逻辑）。
        block_open(ex, '单边持有侧撤单未确认，冻结新仓（保留持仓与配对）',
                   source='cancel_unconfirmed')
        return '撤单失败/未知；已冻结新仓，继续管理持仓与配对'
    hedge_qty = number(pos[side])
    # 2026-11-07 修复（对冲永不触发）：原实现在 _partial_fill_quantity 返回
    # 非 None 时直接 return，而对侧 maker 挂满净缺口是正常状态 → 每次都返回
    # 「对侧已有买单覆盖」→ 下面的 hedge 评估永远执行不到（实测单边 37 分钟
    # 仍无 single_since / hedge_eval）。
    #
    # 现在区分两类返回：
    #   - 真阻塞（快照待复核 / 未决承诺 / 预算不足等）→ 仍然早退，保持原行为
    #   - 「对侧已覆盖」→ 只记录，继续往下评估对冲（是否追价由 hedge_decision 定）
    quantity_covered = None
    if ex.cfg.get('dynamic_candidates_enabled'):
        _covered_reason = []
        quantity_wait = _partial_fill_quantity(ex, oid, pos, replenish=True,
                                               original_path=True,
                                               return_reason=_covered_reason)
        if quantity_wait is not None:
            return quantity_wait
        if _covered_reason:
            quantity_covered = _covered_reason[0]
            ms['hedge_blocked_by_quantity'] = quantity_covered
        hedge_qty = ms['quantity_gap']['additional']
    # 对侧仍有覆盖挂单时，若要 taker 补齐必须先撤掉它，否则会重复买入
    # 形成反向裸敞口（hedge_taker 只取 ask，不会自动撤单）。
    hedge_needs_cancel = bool(quantity_covered)
    # ---- 对侧超时追价配对（2026-10-31 用户拍板开启）----
    # 单边成交后若对侧超过 hedge_trigger_seconds 仍不成交，比较
    # 「追价补齐的净回收」vs「等待的期望损失」，划算才追。
    # 判定用 executor_v2.hedge_decision（决策 1 的公式），不另造标准。
    if (ex.cfg.get('v2_hedge_buy_enabled') is True
            and ex.state.get('activation_valid') is True
            and ex.now() < ex.state.get('authorization_expires_at', float('inf'))):
        single_since = ms.get('single_since')
        if single_since is None:
            ms['single_since'] = ex.now()
            single_since = ex.now()
        waited = ex.now() - number(single_since)
        trigger = number(ex.cfg.get('hedge_trigger_seconds', 900))
        # 2026-11-01 修复 P1-2（追价对冲无去重 → 每轮重复 taker 买入）：
        # 原实现只在成功提交后写 ms['hedge_submitted']，但**全代码库没有任何地方读它**，
        # 于是只要条件满足，每轮 tick 都会再发一笔 taker 买单。
        # 实测：单边 20 份连跑 5 轮 → 5 笔独立 place，qty 都是 20。
        # 对侧一旦成交，实际买入量可能是持仓的数倍 → 反向裸敞口（资金风险）。
        #
        # 去重条件：
        #   - 已有在途 hedge 意图且尚未了结 → 不重复提交
        #   - 已提交过的 hedge 若总份数已覆盖当前持仓 → 不再追加
        prev_hedge = ms.get('hedge_submitted') or {}
        if prev_hedge or any(
                i.get('status') in ('unknown', 'awaiting_fill', 'submitted')
                and i.get('buy') and str(i.get('coin')) == f'#{int(oid)*10+int(other)}'
                for i in journal(ex).values()):
            coin_other_pending = f'#{int(oid)*10+int(other)}'
            in_flight = any(
                i.get('status') in ('unknown', 'awaiting_fill', 'submitted')
                and str(i.get('coin')) == coin_other_pending
                for i in journal(ex).values())
            covered = number(prev_hedge.get('qty', 0)) >= number(pos[side])
            if in_flight or covered:
                ms['hedge_skip_reason'] = (
                    '已有在途/已覆盖的对冲，跳过重复提交'
                    f'（in_flight={in_flight} covered={covered}）')
                return f'单边超时但已有对冲在途或已覆盖；不重复追价（waited={waited:.0f}s）'
        if waited >= trigger:
            from executor_v2 import hedge_decision
            coin_held = f'#{int(oid)*10+int(side)}'
            coin_other = f'#{int(oid)*10+int(other)}'
            try:
                held_bid = ex.adapter.best_bid(coin_held, force=True)
                ob = ex.adapter._book(coin_other, force=True)
                other_ask = (number(ob['levels'][1][0]['px'])
                             if ob and ob.get('levels') and ob['levels'][1] else None)
            except BudgetUnavailable:
                raise
            except Exception:
                held_bid = other_ask = None
            if other_ask is not None and held_bid is not None:
                entry = number(lot['cost']) / max(number(pos[side]), 1e-9)
                stop_px = number(ms.get('stop_px') or 0) or None
                # 止损价未知时用「入场价 − 阈值/份数」反推，供比较使用
                if stop_px is None:
                    stop_px = entry - threshold / max(number(pos[side]), 1e-9)
                do_hedge, why = hedge_decision(entry, held_bid, other_ask, stop_px)
                ms['hedge_eval'] = {'at': ex.now(), 'waited': round(waited, 1),
                                    'entry': entry, 'held_bid': held_bid,
                                    'other_ask': other_ask, 'stop_px': stop_px,
                                    'decision': bool(do_hedge), 'reason': why}
                if do_hedge:
                    # 2026-11-07：对侧已有覆盖挂单 → 先撤净再买，避免重复买入。
                    # 撤单未确认时本轮不买，等下一轮重试（不赌「大概撤掉了」）。
                    if hedge_needs_cancel:
                        cancel_clean = _single_leg_cancel(ex, oid, side, ms,
                                                          keep_side=side)
                        if not cancel_clean:
                            ms['hedge_skip_reason'] = (
                                '追价前撤对侧挂单未确认，本轮不买入（避免重复买入）')
                            return ms['hedge_skip_reason']
                        # 对侧已撤净 → 必须自己补满整个净缺口
                        hedge_qty = number(pos[side])
                        ms['hedge_cancelled_opposite'] = True
                    max_px = other_ask + number(ex.cfg.get('hedge_max_slippage', 0.005))
                    # Budget waits are not hedge attempts.
                    try:
                        # 通过 adapter 取实际可成交价（带保护价），再由 submit 落 journal。
                        # 绝不直接调 ex.order —— 安全测试锁定「taker 必须走持久化意图」。
                        limit_px = ex.adapter.hedge_taker(
                            int(oid), other, hedge_qty, max_px=max_px)
                    except BudgetUnavailable:
                        raise
                    except Exception as exc:
                        ms['hedge_error'] = f'{type(exc).__name__}: {exc}'
                        return f'对侧超时但 taker 补齐未成功：{ms["hedge_error"]}'
                    if ex.cfg.get('dynamic_candidates_enabled'):
                        limits = c.get('sdk_limits') or {}
                        minimum = max(Decimal('1'), Decimal(str(
                            limits.get('min_notional_per_leg', 0))))
                        cost = hedge_qty*limit_px
                        if (not limits.get('verified') or not limits.get('evidence')
                                or not isinstance(limits.get('sz_decimals'), int)
                                or not 0 <= limits['sz_decimals'] <= 8
                                or hedge_qty != int(hedge_qty)
                                or hedge_qty < number(limits.get('min_shares', 1))
                                or Decimal(str(hedge_qty))*Decimal(str(limit_px)) < minimum):
                            ms['quantity_skip_reason'] = '真实净缺口不足最小买入量/名义：不扩大、不强卖，继续原止损/截止管理'
                            return ms['quantity_skip_reason']
                        if (number(ex.state.get('reserved_total', 0)) + cost > total_cap(ex.cfg)
                                or number(ex.state.get('market_reserved', {}).get(oid, 0)) + cost
                                    > number(ex.cfg['capital_per_market'])
                                or number(ex.state.get('free_cash', 0)) < cost
                                    + number(ex.cfg.get('experiment_principal_usdc', 0))*.1):
                            return '净缺口追价预算不足，继续原单腿管理'
                        ms.pop('quantity_skip_reason', None)
                    intent = submit(ex, f'#{int(oid)*10+int(other)}', True,
                                    int(hedge_qty), limit_px, 'Ioc')
                    ms['hedge_attempts'] = int(ms.get('hedge_attempts', 0)) + 1
                    if (ex.cfg.get('dynamic_candidates_enabled')
                            and intent.get('status') in ('submitted', 'unknown')):
                        ex.state['reserved_total'] = number(ex.state.get('reserved_total', 0)) + cost
                        ex.state.setdefault('market_reserved', {})[oid] = number(
                            ex.state.get('market_reserved', {}).get(oid, 0)) + cost
                        ex.state['free_cash'] = number(ex.state.get('free_cash', 0)) - cost
                        ex.state_save()
                    if intent.get('status') == 'submitted':
                        ms['hedge_submitted'] = {'at': ex.now(), 'qty': hedge_qty,
                                                 'limit_px': limit_px, 'reason': why,
                                                 'oid': intent.get('oid')}
                        return f'对侧超时 {waited:.0f}s → taker 补齐 {hedge_qty:g} 份（{why}）'
                    ms['hedge_error'] = f'intent status={intent.get("status")}'
                    return f'对侧超时但 taker 补齐未成功：{ms["hedge_error"]}'
                return (f'对侧超时 {waited:.0f}s，但补齐不划算（{why}）；继续持有等配对')
    else:
        ms.pop('single_since', None)
        # 2026-11-02 L3：单边结束 → 本腿的撤单确认标记必须一起清，
        # 否则下一次单边会误以为「已经确认过」而跳过首次真实撤单。
        # Disabling hedging is not the end of a single-sided position.

    ms['phase'] = 'waiting'
    return '持有侧余单撤净；等待原对侧maker，若无挂单则等待人工授权及预算核对，不自动补位'


@deferred_operation
def merge(ex, oid, pos, allow_when_halted=False):
    '双腿配对 → merge 锁定 $1/对兑付。\n\n    allow_when_halted：全局 halted 时仍允许把**已配对**的仓位 merge 收口\n    （用户 历史版本 第 1 条：已配对仓位不得被拆）。未配对仍一律 unwind。\n    '
    ms = ex.state['markets'][oid]
    # 用户 2026-10-28 21:53 冻结漏洞 3：alert / unwinding 下若两腿齐备，
    # 仍应 merge 收口而不是继续卖——alert 的原意是「卖掉清不干净」，
    # 而配对仓根本不需要卖。
    paired = all(number(pos.get(s, 0)) > 0 for s in ('0', '1'))
    if ms.get('phase') == 'alert' and not (paired and allow_when_halted):
        return False, unwind(ex, oid, pos)
    if (ex.state.get('halted') or ms.get('phase') == 'unwinding') and not allow_when_halted:
        return False, unwind(ex, oid, pos)
    # 2026-11-01：ack=False 的 pending 只作为「成交归属凭据」保留，不再阻挡重试。
    # 只有 ack=True（交易所已接受，存在真正在途动作）才必须等持仓减少。
    pending = ms.get('merge_pending')
    if pending and pending.get('ack') is not False:
        # 2026-11-02 方案 D4：ack=True 超时降级。
        # 交易所对 merge 返回 `{"status":"ok","response":{"type":"default"}}` ——
        # 官方文档把它放在成功响应示例区（与 usdClassTransfer / sendAsset 并列），
        # 但**不携带任何执行细节**（无 statuses / oid / error）。于是「已受理」这个
        # 结论只有我们自己记账，没有可复核的回执字段。一旦在途动作其实早就结束
        # （或压根没落地），pending 会永远挡住重试 —— 与 2026-11-01 那次死锁同构。
        # 兜底：ack=True 且超过 merge_unacked_retry_seconds 仍未见持仓减少，就降级成
        # ack=False（= 不存在在途动作）并开一个短重试窗口，允许下一轮重新提交。
        # 若 merge 其实成功，持仓减少后 :912 的 decreased 分支会先清掉 pending，
        # 走不到这里，因此降级不会误伤真正的在途动作。
        # ack=None（回执未知）不降级：那表示「可能已到交易所」，没有时间基准可判。
        downgraded = False
        if pending.get('ack') is True:
            retry_s = number(ex.cfg.get('merge_unacked_retry_seconds', 60))
            # acked_at 是 D4 新增字段；老 state 从旧版本恢复时没有它，用 submitted_ms
            # 兜底；两者都没有则不降级（保守：宁可多等一轮，也不把在途动作当失败）。
            acked_at = pending.get('acked_at')
            if acked_at is None and pending.get('submitted_ms') is not None:
                acked_at = number(pending['submitted_ms'])/1000.0
            waited = None if acked_at is None else ex.now() - number(acked_at)
            if waited is not None and waited > retry_s:
                ms['merge_pending'] = {**pending, 'ack': False,
                                       'unacked_retry_at': ex.now() + retry_s}
                ms['merge_unacked_until'] = ex.now() + retry_s
                ms['merge_retry_note'] = (
                    f'ack=True 超时 {waited:.0f}s 未减少，降级允许重试'
                    f'（回执 default 无细节，按在途不确定性兜底）；{retry_s:g} 秒后重试')
                ex.state_save()
                # 日志走 ex.log（ExecutorV2 没有 self.log，故回落到模块级 log）。
                _log = getattr(ex, 'log', None)
                if _log is None:
                    from executor_v2 import log as _log
                try:
                    _log(f'  merge O{oid} ack=True 超时 {waited:.0f}s 未减少 '
                         f'→ 降级允许重试（回执 default 无细节兜底）')
                except Exception:
                    pass
                downgraded = True
        if not downgraded:
            return False, 'merge/订单状态未确认'
    if not pending and unresolved(ex):
        return False, 'merge/订单状态未确认'
    # ack=False 后的短重试窗口：防止「请求其实已到、只是回执丢了」时重复提交。
    if ex.now() < number(ms.get('merge_unacked_until', 0)):
        return False, '上次 merge 未被接受，等待重试窗口（防在途重复提交）'
    ms.pop('merge_unacked_until', None)
    ms.pop('merge_retry_note', None)
    if not ex.adapter.cancel_all(int(oid)):
        # 2026-11-01 修复 P1-3（同 wait_single）：区分「退避中查不到」与「真撤不掉」。
        # 原实现一律 halt + 钉 unwinding，而 'merge前撤单未确认' 不在
        # AUTO_RESUMABLE 里 → 永久 halt 需人工（实测能卡住整台机器）。
        backoff_until = getattr(ex.adapter, '_oo_backoff_until', 0)
        if ex.now() < backoff_until:
            ms['cancel_recheck'] = 'merge 前查挂单落空（预算退避中），本轮不作结论'
            ex.state_save()
            return False, (f'merge 前置撤单复核退避中（剩余约 '
                           f'{int(backoff_until - ex.now())}s），本轮不合并、不 halt')
        # 2026-11-01 halt 重构：L1。配对仓等 merge，撤不掉残单不该清仓。
        block_open(ex, 'merge前撤单未确认，冻结新仓（保留配对等 merge）',
                   source='cancel_unconfirmed')
        ex.state_save()
        return False, 'merge前残单未撤净，禁止合并和重挂'
    # Must refresh after cancellation to account for races/partial fills.
    try:
        snap = snapshot(ex.adapter.info, ex.owner, {oid}, getattr(ex.adapter, 'get_open_orders', None))
        fresh = snap['positions'][oid]
    except BudgetUnavailable:
        raise
    except Exception:
        # 2026-11-01 halt 重构：L1。
        ex.state['snapshot_known'] = False
        block_open(ex, 'merge撤单后余额未知，冻结新仓（下轮重试）', source='snapshot_stale')
        ex.state_save()
        return False, '撤单后余额刷新失败'
    n = math.floor(min(fresh.get('0', 0), fresh.get('1', 0)))
    if n <= 0:
        ms['phase'] = 'waiting'
        ex.state_save()
        return False, '无可合并整数配对，保留残仓受控等待；不自动补单'
    ms['merge_pending'] = {'qty': n, 'before': {s: fresh.get(s, 0) for s in ('0', '1')},
                           'submitted_ms': int(ex.now()*1000)}
    ex.state_save()
    try:
        accepted = ex.adapter.merge(int(oid), n)
    except BudgetUnavailable:
        if pending:
            ms['merge_pending'] = pending  # retain attribution for an earlier attempt
        else:
            ms.pop('merge_pending', None)  # this merge was never sent
        ex.state_save()
        raise
    except Exception:
        accepted = None
    if accepted is None:
        ms['merge_pending']['ack'] = None
        ex.state_save()
        return False, 'merge 已尝试发送但回执未知；保留在途凭据，等待成交及余额证据，不重发'
    ms['merge_pending']['ack'] = bool(accepted)
    # 2026-11-01 修复（merge 永久死锁 → 配对仓卡死 2h43m）：
    #
    # 原实现无论 merge 是否被接受，都留下 merge_pending 等「持仓减少」。
    # 但 ack=False 意味着**交易所根本没接受这个请求**
    # （实测 16:37:10 `merge O20032 异常: BudgetUnavailable`，
    #  预算 charge 在发请求前就抛异常，动作压根没发出去），
    # 于是持仓永远不会减少 →
    #   - :616 的 decreased 永远 False，merge_pending 永远清不掉
    #   - :847 的 `if ms.get('merge_pending')` 又拒绝再次提交
    # → **再也不会重试**。实测 O20032 配对 27 份从 16:37 卡到 17:20+，
    #   日志里没有第二条 merge 记录。
    #
    # 正确语义：
    #   ack=True  → 交易所已接受，存在「在途 merge」，必须留着 pending
    #               等真实成交流水与持仓减少来确认（这是原设计，保留不动）
    #   ack=False → 请求没被接受，**不存在在途动作**，
    #               应立即清除 pending 让下一轮重试，而不是挂一个
    #               永远无法满足的期望。
    if accepted:
        ms['merge_pending']['ack'] = True
        # 2026-11-02 方案 D4：记录受理时刻，供「ack=True 超时未减少」降级判定使用。
        # 起因：交易所对 merge 返回 `{"type":"default"}`（成功示例区形态，但无执行细节），
        # 上层只能按「已受理（在途）」处理；一旦在途回执本身不可靠，就必须有超时兜底，
        # 否则 pending 会永远挡住重试（与 2026-11-01 那次死锁同构）。
        ms['merge_pending']['acked_at'] = ex.now()
        ex.state_save()
        # 2026-11-01 业务日志：merge 已受理（回执≠完成，等 fills 确认）
        try:
            ev('merge-受理', oid=oid, pairs=ms['merge_pending'].get('qty'),
               before=json.dumps(ms['merge_pending'].get('before'), ensure_ascii=False))
        except BudgetUnavailable:
            raise
        except Exception:
            pass
        return False, 'merge意图已持久化，回执不是完成；等待双腿fills及余额减少'

    # ack=False 有两种成因，必须区别对待：
    #   ① 预算不足 / 签名失败 —— 请求**明确没发出**（budget.charge 在
    #      _post_action 之前抛异常，实测 16:37:10 就是这种）
    #   ② 网络异常 / 回执丢失 —— 请求**可能已到交易所**，只是没拿到回执
    # 两种情况都不该挂着一个永远无法满足的 pending，但②不能立刻重试，
    # 否则可能在途 merge 还没结算就重复提交。
    # 处理：清除 pending，并设一个短重试窗口；窗口内不提交，
    # 让任何在途 merge 有机会结算。重试时会重新快照持仓并重算 n，
    # 若第一次其实成功了，那时 n 已经是 0，会安全返回「无可合并」。
    # 2026-11-01 修正（本修复引入的回归）：
    # 第一版直接把 merge_pending 清掉，导致 merge 成交回来时**无从归属**——
    # collect_fills 里 Merge Outcome 的准入条件是
    #   `pending and f['time'] >= pending['submitted_ms'] and f['sz'] == pending['qty']`
    # 没有 pending 就落进 else → `ownership_unknown = True`
    # + raise『实验市场发现无法归属本实验的成交』→ ledger_known=False →
    # 永久 halt（实测 17:24 merge 成功后即进入此状态，并每 70 秒空转一次）。
    #
    # 正确做法：pending 不能丢，但要把它从「阻挡重试的门」改成
    # 「仅用于归属的凭据」。做法：
    #   - 保留 merge_pending（供成交归属匹配），同时打上 ack=False 标记
    #   - 另设 merge_unacked_until 作为重试闸门（acked=False 时不再被 pending 挡）
    # 这样成交能归属、又不影响重试。
    retry_s = number(ex.cfg.get('merge_unacked_retry_seconds', 60))
    ms['merge_pending'] = {**ms['merge_pending'], 'ack': False,
                           'unacked_retry_at': ex.now() + retry_s}
    ms['merge_unacked_until'] = ex.now() + retry_s
    ms['merge_retry_note'] = ('merge 未被交易所接受（ack=False）；保留 pending 供成交归属，'
                              f'{retry_s:g} 秒后允许重试')
    ex.state_save()
    return False, f'merge提交未被接受；保留pending供归属，{retry_s:g}秒后重试'


def maker_exit_resting(ex, oid, side):
    """该腿此刻是否**真有一张自己的卖单挂在盘上**。

    必须查 openOrders，不能只看 journal：journal 里的 `unknown/submitted`
    也可能是「早已成交或早已被撤」的历史意图，据此跳过补挂会变成永远不卖。
    """
    try:
        # 2026-11-02 L1：这里只判断「maker 卖单还在不在」，10 秒陈旧可接受
        # （误判只影响本轮挂不挂新卖单，下一轮会纠正）。
        oo = _get_orders(ex, use_cache=True)
    except BudgetUnavailable:
        raise
    except Exception:
        return None                      # Unknown is not evidence that a sell is absent.
    if not isinstance(oo, list):
        return None
    coin = f'#{int(oid)*10+int(side)}'
    mine = {str(x) for x in ex.state.get('submitted_oids', [])}
    return any(o.get('coin') == coin and str(o.get('oid')) in mine for o in oo)


def maker_exit_keep_side(ex, oid, pos, wait_s):
    '返回 maker 等待期内应保留卖单的持仓腿，否则返回 None。\n\n仅在恰好一条腿有持仓且该腿仍处于 maker 等待期时保留卖单；\n对侧不需要的买单照常撤销，等待期结束后不再保留。'
    held = [s for s in ('0', '1') if number((pos or {}).get(s, 0)) > 0]
    if len(held) != 1:
        return None                      # 无持仓或已配对：不保留任何单
    side = held[0]
    coin = f'#{int(oid)*10+int(side)}'
    st = (ex.state['markets'].get(oid) or {}).get('maker_exit', {}).get(coin) or {}
    if st.get('mode') != 'maker':
        return None                      # 已在 taker 阶段：不再保留
    first_at = st.get('first_at')
    if first_at is None:
        return None
    if ex.now() - number(first_at) >= number(wait_s):
        return None                      # 等待期已过：撤掉它，下一轮转 taker
    return side



def block_open(ex, reason, source='unknown'):
    '冻结新仓并保留已有挂单及配对流程。\n\n解除条件按 source 区分，并使用超时升级机制处理持续异常；\n有实际敞口需要撤单收尾的情况由 halt 处理。'
    # 2026-11-06 修复计时污染（实测事故）：
    #   11-05 12:59:47 一次 ledger_unknown 冻结，理应 900s 后超时放行，
    #   但 open_block_since 沿用了更早的时间戳，到 15:50:52 才超时，
    #   elapsed=10265s（2.85 小时）——中间 2 小时 40 分无法开新仓。
    # 原实现只在 since 为空时记录，导致：
    #   ① 同一 source 反复冻结/解除后，旧 since 可能残留被复用；
    #   ② 不同 source 交替时，后来的 source 继承了前一个的起点。
    # 现在：since 为空，或 source 发生变化时，都重新计时。
    _prev_src = ex.state.get('open_block_source')
    ex.state['open_blocked'] = True
    ex.state['open_block_reason'] = str(reason)
    ex.state['open_block_source'] = str(source)
    if (ex.state.get('open_block_since') is None
            or _prev_src != str(source)):
        ex.state['open_block_since'] = ex.now()
        ex.state['open_block_since_source'] = str(source)
        ex.state.pop('open_block_timeout_alert', None)
    return reason


def clear_open_block(ex, source=None):
    """解除 L1 冻结。source 不为 None 时只在来源匹配时解除（精确解除）。"""
    if source is not None and ex.state.get('open_block_source') != source:
        return False
    ex.state['open_blocked'] = False
    ex.state.pop('open_block_reason', None)
    ex.state.pop('open_block_source', None)
    ex.state.pop('open_block_since', None)
    return True



def is_normal_quoting(ex, oid, pos):
    '判断市场是否仍处于正常双腿做市，供异常处理保留配对机会。\n\n要求 phase 为 waiting、无持仓、链上仍有本市场自己的挂单，\n且没有 stop_triggered 或 merge_pending 等明确清仓意图。\n满足条件时保留挂单并等待成交。'
    ms = ex.state['markets'].get(oid) or {}
    if ms.get('phase') != 'waiting':
        return False
    if any(number(q) > 0 for q in (pos or {}).values()):
        return False
    if ms.get('stop_triggered') or ms.get('merge_pending'):
        return False
    # 必须真的有挂单：查 state 里的 remote_orders（每轮快照刷新）
    try:
        has_order = any(scoped_coin(o.get('coin'), {str(oid)})
                        for o in ex.state.get('remote_orders', []))
    except BudgetUnavailable:
        raise
    except Exception:
        has_order = False
    return has_order


@deferred_operation
def unwind(ex, oid, pos):
    ms = ex.state['markets'][oid]
    prev_phase = ms.get('phase')
    # 2026-11-01 halt 重构：正常做市的挂单不撤。
    # 只有 L2（halted / 明确止损 / 已在 unwinding）才允许走到下面撤单。
    if not ex.state.get('halted') and prev_phase != 'unwinding' and is_normal_quoting(ex, oid, pos):
        ms['quote_protected'] = '正常做市挂单中，本轮不撤（L1 不破坏配对）'
        return '正常做市挂单中，本轮不撤单；等成交或超时'
    ms['phase'] = 'unwinding'
    # 2026-10-31 修复（halt 反复复发）：
    # 实测今日 19:18-19:44 期间 halt 原因在「清仓撤单未确认」与「账本未知」之间
    # 来回切了 26 分钟，根因是 cancel_all 因**预算退避**返回 False，
    # 而 unwind 把 False 当成「真有单没撤掉」→ 写死 halt → maintain 又重试 →
    # 又退避 → 又 halt，自我维持。
    #
    # 关键区分：cancel_all 的 False 有两种完全不同含义
    #   ① 查询成功、但确实还有单撤不掉  → 危险，必须 halt 等人工
    #   ② 这一轮根本没查成（预算退避 / 网络失败）→ 只是暂时不知道，不该 halt
    # 现在用「退避中」标记区分它们。退避中：不改 phase、不 halt、只记一笔，下轮再说。
    #
    # 2026-11-01 修复（maker 卖单被自己撤掉）：等待期内必须保留持仓腿的 maker 卖单，
    # 否则每轮都是「撤掉→重挂→再撤掉」，永远等不到成交。详见 maker_exit_keep_side。
    keep_side = maker_exit_keep_side(ex, oid, pos, number(ex.cfg.get('maker_exit_wait_seconds', 300)))
    # Keep-side changes use a different verification key in the adapter.
    if keep_side is not None:
        clean = ex.adapter.cancel_all(int(oid), keep_side=keep_side)
        ms['maker_exit_kept_side'] = keep_side
    else:
        ms.pop('maker_exit_kept_side', None)
        clean = ex.adapter.cancel_all(int(oid))
    # 调用后再看退避状态：这次调用本身也可能刚把退避设上
    if not clean and ex.now() < getattr(ex.adapter, '_oo_backoff_until', 0):
        ms['cancel_recheck'] = '查挂单落空（预算退避中），本轮不作结论，不据此 halt'
        # 恢复原 phase：本轮什么都没做成，不该把市场留在 unwinding
        if prev_phase:
            ms['phase'] = prev_phase
        ex.state_save()
        return '撤单复核退避中：本轮不作结论，保持持有等下一轮'
    # 2026-10-30 修复（halted 卡死）：cancel_all 返回 False 有两种含义——
    #   ① 真有挂单没撤掉（危险）
    #   ② 查询本身失败/快照未知（链上其实早已干净）
    # 实测事故：清仓已实际完成、链上无仓无单，但 cancel_all 因查询失败返回 False，
    # 于是写死 halt_reason='清仓撤单未确认'，而该原因**没有解除路径**，永久卡住。
    # 现在：False 时先独立复核一次链上挂单；确认无单则视为已撤净，继续正常收口。
    if not clean:
        still_open = _market_orders_still_open(ex)
        if still_open is False:
            clean = True
            ms['cancel_recheck'] = 'cancel_all 返回失败，但独立复核确认链上无挂单 → 视为已撤净'
        else:
            ms['cancel_recheck'] = ('复核仍有挂单' if still_open
                                    else '复核无法判断（查询失败），保持暂停')
    ms['cancel_confirmed'] = clean
    if not clean:
        # 2026-11-01 halt 重构：L1。撤单未确认只说明「不知道有没有撤掉」，
        # 不等于有危险敞口。冻结新仓，继续复核即可。
        block_open(ex, '清仓撤单未确认，冻结新仓（继续复核）', source='cancel_unconfirmed')
        ex.state_save()
        return '撤单未确认，持续管理；禁止买入/重挂'
    if ex.state.get('ownership_unknown'):
        ex.state_save()
        return '实验市场归属混杂，仅撤本实验订单；暂停自动卖出待核对，持续读取状态'
    if not pos and not unresolved(ex) and not ms.get('merge_pending'):
        fresh = snapshot(ex.adapter.info, ex.owner, {oid}, getattr(ex.adapter, 'get_open_orders', None))['positions'][oid]
        if not fresh:
            ms['phase'] = 'closed'
            ms['orders'] = {}
            if 'rollback_confirmed' in ms:
                ms['rollback_confirmed'] = True
            ex.state_save()
            return '撤净与清零均确认'
        pos = fresh
    if unresolved(ex) or ms.get('merge_pending'):
        return '未知订单/merge待复核；不重复提交卖出'
    # 2026-11-01 修复（maker 单重复挂）：上面刚用 keep_side 保住了等待期的 maker 卖单，
    # 这一轮就不能再补一张新的，否则同一腿叠两张卖单（撤单时口径也会打架）。
    # 等它成交、或等待期到了被撤掉，下一轮自然重新走「挂 maker / 转 taker」。
    if keep_side is not None:
        coin_kept = f'#{int(oid)*10+int(keep_side)}'
        resting = maker_exit_resting(ex, oid, keep_side)
        if resting is None:
            return 'maker 挂单查询未确认；不重复挂卖单'
        if resting:
            return 'maker 卖单已在盘上等待成交；不重复挂、不砸盘'
    if ex.now() < ms.get('retry_after', 0):
        return '受控退避中，仍逐轮读取余额和订单'
    try:
        fresh = snapshot(ex.adapter.info, ex.owner, {oid}, getattr(ex.adapter, 'get_open_orders', None))['positions'][oid]
    except BudgetUnavailable:
        raise
    except Exception:
        # 2026-11-01 halt 重构：L1。余额读不到是暂时状态，下轮重试即可。
        ex.state['snapshot_known'] = False
        block_open(ex, '清仓余额刷新失败，冻结新仓（下轮重试）', source='snapshot_stale')
        ex.state_save()
        return '清仓余额未知'
    # 2026-10-31 用户拍板（maker-fill 路线）：**先挂 maker 卖，不砸盘**。
    #
    # 实测今日 14 次买卖循环，净亏 $1.2434 中：
    #   价差损失 -$1.101（89%），手续费 -$0.142（11%）
    # 其中「贴着买价卖出」的 3 次只亏 5~13 厘（纯手续费），
    # 「等久了被迫砸盘」的 4 次亏 $0.21~0.23/次，贡献了七成亏损。
    # 根因是卖出用 `bid × 0.998` 的 IOC **主动砸穿盘口**。
    #
    # 现在改为两段：
    #   ① 先在 ask 侧挂 maker 卖单等成交（吃掉价差，付 0 手续费）
    #   ② 超过 maker_exit_wait_seconds 仍未成交，才退回 IOC 砸盘
    wait_s = number(ex.cfg.get('maker_exit_wait_seconds', 300))
    # 2026-11-01（P2-3 配套）：记录本轮是否**真的发过**卖出单。
    # 原实现无条件递增 unwind_attempts，连「一张单都没发」的轮次也算一次失败，
    # 于是告警说「清仓多次失败」，实际是「从未尝试」——告警原因失真。
    held = number(ms.get('hold_qty', 0))
    if held > 0:
        fresh = {s: max(0, number(q) - held) for s, q in fresh.items()}
    attempted = 0
    for side in ('0', '1'):
        raw_qty = number(fresh.get(side, 0))
        qty = math.floor(raw_qty)
        coin = f'#{int(oid)*10+int(side)}'
        # 2026-11-01 修复 P2-1（maker_exit.first_at 永不复位 → 新仓第一轮就砸盘）：
        # 原实现只在 first_at 为 None 时写入，之后**从不清除**（整个 maker_exit
        # 也没有任何 pop）。而它按 coin 存在 ms['maker_exit'] 里，市场级、跨轮存活。
        # 实测后果：同一市场第二次进入 unwind 时（成交后重开、pair_blocked 解除后
        # 重开、或部分成交后补挂），会沿用上一次的 first_at →
        # `waited_exit >= wait_s` 立刻成立 → 直接 taker 砸盘，**跳过 maker**。
        # 这把今天早些时候修的「先挂 maker」整个绕过去了，磨损率直接劣化到砸盘水平。
        #
        # 现在：该腿持仓已归零 → 视为一个完整退出周期结束，清除它的 maker_exit；
        # 并顺带清理已无持仓的腿（不分轮次），避免残留状态污染下一轮开仓。
        if raw_qty <= 1e-8:
            _me = ms.get('maker_exit') or {}
            if coin in _me:
                _me.pop(coin, None)
                ms['maker_exit_cleared'] = f'{coin} 持仓归零，maker_exit 已复位'
            if not _me:
                ms.pop('maker_exit', None)
            continue
        if qty <= 0:
            # 2026-11-01 修复 P2-3（非整数残仓 floor 归零 → 永不卖 + 假 alert）：
            # 残仓 <1 份时 floor 为 0，原实现直接 continue，一张卖单都不挂；
            # 但 unwind_attempts 照样 +1，7 轮后 alert=True + '清仓多次失败' ——
            # 告警原因是假的（实际是「从未尝试」）。且仓位永远挂着。
            ms['fractional_residual'] = (
                f'{coin} 残仓 {raw_qty:g} 份不足 1 份整数，无法下单退出；'
                '请人工处理')
            ms['alert'] = True
            # 不计入 unwind_attempts（避免把「无法尝试」报成「多次失败」）
            continue
        try:
            book = ex.adapter._book(coin, force=True)
        except TypeError:
            # 兼容不接受 force 的 adapter（mock / 旧实现）
            book = ex.adapter._book(coin)
        if not book or not book.get('levels') or not book['levels'][0]:
            continue
        bid = number(book['levels'][0][0]['px'])
        ask = (number(book['levels'][1][0]['px'])
               if book['levels'][1] else None)
        # 2026-11-01 修复（小额残仓永远卖不掉 → 敞口卡死）：
        # 原实现要求「qty × bid ≥ $1」才允许卖出，否则 alert 并 continue，
        # 于是**永远走不到挂单那一行**。
        #
        # 实测事故：O20032 下单 20 份但只成交 1 份，剩 1 份 × 0.69684 = $0.6968 < $1
        #   → maker_exit 从头到尾为 None（卖单一次没挂出去）
        #   → unwind_attempts 累计 52 次，alert=True
        #   → 那 1 份持仓卡了 1 小时以上，无人管理。
        #
        # 而且这道门槛与下单层自相矛盾：executor_v2.place_limit 的门槛是
        #   `if is_buy and dec(sz)*dec(px) < 1`  —— **只约束开仓买入**
        # 其注释明确写明「Position-closing sells may be below $1
        # (documented Outcome SDK close-flow exception); rejecting them locally
        # would turn a known tiny residual into an unsent unknown intent」。
        # 也就是说下单层本来就允许低于 $1 的平仓卖出，是 unwind 层把它拦住了。
        #
        # 现在：卖出不再设 $1 下限，只要 qty>0 且价格为正就挂出去。
        # 仍然保留「价格为 0 / 比例异常」的防护（避免把仓位以 0 价送掉）。
        if Decimal(str(bid)) <= 0 or Decimal(str(qty)) <= 0:
            ms['alert'] = True
            continue
        # 该腿的 maker 卖单何时挂出（用于判断是否超时改砸盘）
        exit_state = ms.setdefault('maker_exit', {}).setdefault(coin, {})
        first_at = exit_state.get('first_at')
        if first_at is None:
            first_at = ex.now()
        waited_exit = ex.now() - number(first_at)
        use_taker = (ask is None) or (waited_exit >= wait_s)
        # 2026-11-01 修复 P3-3（price_wire 的 ValueError 未捕获 → 整轮停摆）：
        # 价格 < 0.00001 时 price_wire 抛 ValueError('price outside outcome range
        # after tick rounding')，原本直接穿透 maintain → tick →
        # halt_reason='主循环异常'，当轮该市场与其它市场全部不执行。
        # 极低价市场才会触发，但一旦触发就是整轮停摆。
        try:
            if not use_taker:
                # ① maker 卖：挂在该腿 best ask（与对手并列，吃价差、免手续费）
                px = price_wire(Decimal(str(ask)), tif='Alo')
                tif = 'Alo'
                exit_state['mode'] = 'maker'
                # 2026-11-01 业务日志：maker 卖单挂出。
                # 记绝对时间 + 相对开仓/单边起点的延迟，这是区分
                # 「halt 拖延」与「逆向选择」的关键证据（今天靠链上倒查才拿到）。
                try:
                    _t0 = ms.get('single_since') or ms.get('opened')
                    ev('退出-挂maker', coin=coin, oid=oid,
                       sz=qty, px=float(px), ask=ask, bid=bid,
                       waited_s=int(waited_exit),
                       since_s=(int((ex.now() - number(_t0)) / 1000)
                                if _t0 else None))
                except BudgetUnavailable:
                    raise
                except Exception:
                    pass
            else:
                # ② 超时兜底：仍然只能 IOC 砸盘，但至少等过了 wait_s
                px = price_wire(Decimal(str(bid))*Decimal('.998'), tif='Ioc')
                tif = 'Ioc'
                exit_state['mode'] = 'taker'
                # 2026-11-01 业务日志：maker 超时转 IOC（这条能直接算出 maker 窗口失败率）
                try:
                    ev('退出-转IOC', coin=coin, oid=oid, sz=qty, px=float(px),
                       bid=bid, ask=ask, waited_s=int(waited_exit),
                       timeout_s=int(wait_s),
                       why=('无ask' if ask is None else 'maker超时'))
                except BudgetUnavailable:
                    raise
                except Exception:
                    pass
        except (ValueError, TypeError, ArithmeticError) as exc:
            ms['price_wire_error'] = (
                f'{coin} 报价无法规整（bid={bid} ask={ask}）：{type(exc).__name__}: {exc}'
                '；本轮跳过该腿，不中断其它市场')
            ms['alert'] = True
            continue
        # 同上修复：卖出侧不再设 $1 下限（下单层只对买入设该门槛）。
        # 只保留「价格必须为正」的防护。
        if Decimal(str(px)) <= 0:
            ms['alert'] = True
            continue
        intent = submit(ex, coin, False, qty, px, tif)
        if intent['status'] in ('submitted', 'unknown'):
            exit_state.setdefault('first_at', ex.now())
        attempted += 1
        if intent['status'] == 'submitted':
            intent['status'] = 'unknown'
            ex.state_save()
    if attempted == 0:
        # 本轮一张卖单都没发出（例如只有小数残仓、盘口不可用）：
        # 不递增 unwind_attempts，避免把「无法尝试」误报成「多次失败」。
        ms['unwind_idle_note'] = '本轮无可下单价（小数残仓/盘口不可用），不计入失败次数'
        ex.state_save()
        return '清仓本轮无可下单价（见 fractional_residual / alert），不计失败次数'
    attempts = ms.get('unwind_attempts', 0)+1
    ms.update(unwind_attempts=attempts, retry_after=ex.now()+min(60, 2**min(attempts, 6)))
    if attempts >= ex.cfg.get('unwind_max_attempts', 5):
        ms['alert'] = True
        ex.state.update(halted=True, halt_reason='清仓多次失败，告警并持续受控管理')
    ex.state_save()
    return '清仓提交后等待远程终态及余额复核；不增加敞口'


def halt(ex, live_positions=None):
    '全局暂停，并依据本轮链上 live_positions 快照处理市场。\n\n无法取得实时持仓时不依据缓存将市场转入 unwinding。\n仅单边市场转入 unwinding，已配对市场保持原 phase；\nmaintain 的暂停分支负责配对收口与单边清仓，\n体育盘持有意图由 hold_qty 和 hold_until 字段保留。'
    # 2026-11-01 业务日志：halt（L2）进入时记录原因与当时持仓快照。
    # dedup 键含 halt_reason，同一原因持续 halt 不会刷屏。
    try:
        _hw = ex.state.get('halt_reason') or ''
        _lp = ('none' if live_positions is None
               else ','.join('%s:%s' % (k, v) for k, v in sorted(live_positions.items()))
               if isinstance(live_positions, dict) else str(live_positions)[:120])
        ev_change('halt', key='halt:' + _hw, reason=_hw, live_pos=_lp,
                  halted=bool(ex.state.get('halted')))
    except BudgetUnavailable:
        raise
    except Exception:
        pass
    # 2026-10-31 修复（单边仍被秒平）：
    # 上一次只保护了 paired 仓，**正在等配对的单边仓**仍被钉成 unwinding，
    # 于是 maintain 立刻走 unwind 卖出。实测：19638 单边持仓 8 分钟后因一次
    # 「主循环异常」触发 halt → phase 被改成 unwinding → 直接清仓。
    # 现在：有持仓（无论单边还是配对）都不改 phase，保持 waiting，
    # 由 maintain 的 halted 分支按「配对→merge、单边→按止损/追价规则处理」。
    # 只有**无持仓的残留订单市场**才标 unwinding（撤单收口）。
    ex.state['halted'] = True
    for oid, ms in ex.state['markets'].items():
        if ms.get('phase') == 'closed':
            continue
        # 2026-11-01 halt 重构（方案 v2 根因 A）：
        # 原来 `pos = ms.get('pos') or {}` 用的是 **state 缓存**，可能过期。
        # 缓存为空但链上真有仓 → 误判 holding=False → 推 unwinding → 撤单清仓。
        #
        # 现在：有实时持仓就用实时；没有则退回缓存，但**只在缓存明确有仓时**
        # 才允许保护（缓存说有仓→按有仓处理，宁可不动）；
        # 缓存也说没仓时才推 unwinding（与旧行为一致，保证「该清仓还是会清」）。
        # paired 标记不依赖持仓数据，优先保护（用户 2026-10-28 21:43 第 1 条：
        # 已配对仓位不得被拆，兑付已锁定 $1/对）。
        if ms.get('paired'):
            ms['halted_while_paired'] = True
            continue
        if live_positions is not None:
            pos = live_positions.get(oid) or live_positions.get(str(oid)) or {}
            pos_source = 'live'
        else:
            pos = ms.get('pos')
            pos_source = 'cache'
        if pos is None:
            # 既无实时持仓、缓存里也没有 pos 字段 → 数据不可信，不据此推清仓。
            # （撤单是破坏性动作，宁可不动也不能基于缺失数据做）
            ms['halt_skipped_no_live_pos'] = (
                'halt 时既无实时持仓、缓存也无 pos 字段，不推 unwinding（数据不可信）')
            continue
        holding = any(number(q) > 0 for q in pos.values())
        # 已在 unwinding 的（如 closed 后新发现残留、或止损已触发）保持不动，
        # 那是明确要清仓的意图，不能因为 halt 就改回等待。
        if ms.get('phase') == 'unwinding':
            continue
        if holding:
            # 正常等待中的单边持仓：保留等待语义，不因 halt 就清仓
            ms['halted_while_holding'] = True
            ms['phase'] = 'waiting'
            continue
        ms['phase'] = 'unwinding'
    ex.state_save()


# ---- 暂停的自动解除（2026-10-30 用户要求）----
#
# 事故背景：执行器因 journal 写满进入崩溃循环 → 重启后 REST 权重配额耗尽 →
# ledger_known=False → halted=True。配额两分钟后自愈、账本也恢复正常，
# **但 halted 没有任何解除路径**，一直卡着。恢复后第一轮 tick 直接落进
# 「halted 分支 → 配对 → merge」，把本该「持有到比赛结束」的体育盘仓位提前合并了。
#
# 设计原则：只有**确实能自愈、且不涉及钱/授权/归属**的原因才自动放开。
# 下面任何一个条件不满足，一律保持暂停，等人处理。

# 可自动解除的原因（精确前缀匹配；不在此列的永不自动解除）
AUTO_RESUMABLE = (
    'REST权重预算不足',                      # 配额会自己恢复
    '实验覆盖/实际成本/库存退出估值未知',      # 账本/快照重读成功即恢复
    'reward基线/轮询失败',                   # 轮询成功即恢复
    '余额订单快照过期',                      # 下一轮快照刷新即恢复
    '预算不足，冻结未知风险',                 # 同上
    '快照未知，停止新仓',                     # 同上
    # 2026-11-02 新增：占款超限可能因重复计入而误报（见 collect_fills 里
    # held_coins 去重）。真正的判定条件是「当前占款是否仍超限」，
    # 由 resume_blockers 独立校验，不能仅凭原因文案放行。
    '真实总占款/每市场占款超过上限',
)

# 即使原因看似可恢复，出现这些标志也一律锁死（涉及钱、授权、归属）
LOCKED_FLAGS = (
    'ownership_unknown',      # 有无法归属的成交/挂单
    'rest_budget_blocked',    # 本轮预算仍不足
)


def _market_orders_still_open(ex):
    """复核链上是否仍有本实验市场的挂单。

    返回 True（仍有单）/ False（已无单）/ None（查不到，不能判断）。
    """
    # 2026-10-30 修复死锁：原实现在 budget.denied 为真时直接返回 None，
    # 但 denied 一旦置真就不会自己复位（只在 tick 开头清），而 audit/cancel
    # 复核恰好发生在 tick 中段 → 复核永远失败 → halt 永远无法解除。
    # 实测：13:35 与 14:52 两次 halt 自锁，日志每秒刷「查挂单失败 BudgetUnavailable」。
    #
    # 正确做法：**不要因为 denied 就跳过复核**。openOrders 是状态必需的读，
    # 服务器版 BudgetedInfo 已把它归入 essential（可用全池 limit），
    # 预算不足时 charge() 会抛 BudgetUnavailable，由下面的 except 处理。
    # 这里只做「最近刚失败过就退避」，避免每轮重撞。
    backoff_until = getattr(ex, '_recheck_backoff_until', 0)
    if ex.now() < backoff_until:
        return None
    try:
        # 2026-11-02 L1：强制实时——本函数存在的意义就是「不信别处的结论」，
        # 读缓存等于没复核（它正是用来兜 cancel_all 的底）。
        oo = _get_orders(ex, use_cache=False)
    except BudgetUnavailable:
        raise
    except Exception:
        # 失败才退避：10s 起，翻倍到最多 60s，避免每轮重撞预算
        fails = getattr(ex, '_recheck_fails', 0) + 1
        ex._recheck_fails = fails
        ex._recheck_backoff_until = ex.now() + min(60, 10 * (2 ** (fails - 1)))
        return None
    if not isinstance(oo, list):
        ex._recheck_backoff_until = ex.now() + 10
        return None
    ex._recheck_fails = 0
    ex._recheck_backoff_until = 0
    ids = {str(c['outcome_id']) for c in ex.candidates} | set(ex.state.get('markets') or {})
    return any(scoped_coin(o.get('coin'), ids) for o in oo)


PAIR_REJECTION_HALT = '配对下单被交易所拒绝，保留意图及预留，禁止重发'


def pair_rejection_blockers(ex):
    """Recover the legacy halt only after terminal intents and fresh remote cleanup."""
    st = ex.state
    rejected = [i for i in journal(ex).values()
                if i.get('buy') and i.get('status') == 'rejected']
    ids = {str(int(i['coin'][1:]) // 10) for i in rejected}
    if not ids:
        return ['拒单恢复缺少失败市场证据']
    blockers = []
    pair_intents = []
    if not st.get('snapshot_known') or st.get('snapshot_dirty'):
        blockers.append('拒单恢复等待新鲜快照')
    if st.get('ledger_issues'):
        blockers.append('拒单恢复账本仍有异常')
    for oid in ids:
        ms = st.get('markets', {}).get(oid, {})
        if ms.get('phase') != 'closed' or not ms.get('rollback_confirmed'):
            blockers.append('拒单市场尚未确认收尾：' + oid)
        if number(st.get('market_reserved', {}).get(oid, 0)) != 0:
            blockers.append('拒单市场占款尚未释放：' + oid)
        intents = [i for i in journal(ex).values() if scoped_coin(i.get('coin'), {oid})]
        latest_buys = sorted((i for i in intents if i.get('buy')),
                             key=lambda i: i.get('created_ms', 0))[-2:]
        if len(latest_buys) != 2 or {i['coin'][-1] for i in latest_buys} != {'0', '1'}:
            blockers.append('拒单恢复缺少配对两腿证据：' + oid)
        pair_intents.extend(latest_buys)
        if any(i.get('status') not in ('final', 'absent', 'rejected') for i in intents):
            blockers.append('拒单市场两腿尚未终态：' + oid)
    if blockers:
        return blockers
    try:
        # Bypass the order cache and independently check balances and both legs.
        fresh = snapshot(ex.adapter.info, ex.owner, ids,
                         orders_getter=lambda **_: _get_orders(ex, use_cache=False))
        if any(scoped_coin(o.get('coin'), ids) for o in fresh['orders']):
            blockers.append('拒单市场链上仍有残单')
        if any(number(q) > 0 for pos in fresh['positions'].values() for q in pos.values()):
            blockers.append('拒单市场链上仍有残仓')
        checks = {i['client_id']: i for i in pair_intents + rejected}
        for intent in checks.values():
            remote = ex.adapter.info({'type': 'orderStatus', 'user': ex.owner,
                                      'oid': intent['client_id']})
            if isinstance(remote, dict) and remote.get('status') == 'unknownOid' and intent.get('oid'):
                blockers.append('已知订单远端状态矛盾')
            elif not isinstance(remote, dict) or remote.get('status') not in ('unknownOid', 'order'):
                blockers.append('拒单意图远端状态未知')
            elif remote.get('status') == 'order' and remote.get('order', {}).get('status') not in (
                    'filled', 'canceled', 'rejected', 'marginCanceled', 'reduceOnlyCanceled'):
                blockers.append('拒单意图远端尚未终态')
    except BudgetUnavailable:
        raise
    except Exception:
        blockers.append('拒单恢复实时复核失败')
    return blockers


def resume_blockers(ex):
    """返回阻止自动解除的具体原因列表；空列表表示可以解除。"""
    st = ex.state
    blockers = []
    reason = str(st.get('halt_reason') or '')
    if not reason:
        return ['无暂停原因，无需解除']
    # 「撤单未确认」特殊处理：它可能只是快照读不到导致的误判（链上其实已干净），
    # 也可能是真的撤不掉。因此不按原因放行，而是**要求链上复核确实无挂单**。
    # 这条放行条件比其它项更严：必须重新查一次 openOrders 且确认该市场无单。
    #
    # 2026-10-31 修复（halt 复发）：这类原因**豁免 snapshot_known 检查**。
    # 原因链：预算耗尽 → 快照读不到 → snapshot_known=None → 挡住解除 →
    # maintain 继续撤单 → 置 dirty → 更是耗尽预算。是自锁。
    # 而「撤单未确认」真正要确认的是**链上有没有挂单**，
    # 这件事已经由 _market_orders_still_open() 独立查过一次（不依赖快照），
    # 用一次独立查询替代对整体快照的依赖是充分且更准确的。
    order_reason = reason.startswith('清仓撤单未确认')
    if order_reason:
        still_open = _market_orders_still_open(ex)
        if still_open is None:
            blockers.append('撤单未确认：无法复核链上挂单')
        elif still_open:
            blockers.append('撤单未确认：链上仍有挂单未撤净')
        # still_open is False → 不追加 blocker，允许解除
    elif reason == PAIR_REJECTION_HALT:
        blockers.extend(pair_rejection_blockers(ex))
    elif not any(reason.startswith(p) for p in AUTO_RESUMABLE):
        blockers.append('原因不属于可自愈类别：' + reason[:80])
    # 2026-11-02：占款类原因不能只看文案放行，必须用**当前**占款重新校验。
    # 条件来自 collect_fills() 每次刷新的 market_reserved（不是 halt 瞬间的快照）。
    #
    # 为什么这里读 market_reserved 是安全的（不必重算快照）：
    # 全代码库把 ledger_known 置 True 的地方**只有** collect_fills 里那一次
    # `ex.state.update(..., ledger_known=True, market_reserved=reserved, ...)`，
    # 两者是同一次 dict.update 原子写入；其它所有路径只会把它置 False
    # （bind_ledger 异常 :2328、tick 的 BudgetUnavailable/Exception 分支）。
    # 唯一的另一个写入点 checkpoint() 要求 net 是 {'scope':'experiment_all'} 的
    # dict，而生产唯一调用者 executor_v2:1193 传的是 None → 走不到那一行。
    # 因此本函数执行到这里（下面的 ledger_known 检查尚未拦住）时，
    # market_reserved 必然是最近一次成功 collect_fills 写下的新鲜值。
    # 反过来若 collect_fills 失败，ledger_known 立刻变 False，
    # 本检查根本到不了，会由「账本仍未知」拦住 —— 不会出现拿旧值判定的窗口。
    if reason.startswith('真实总占款') or reason == PAIR_REJECTION_HALT:
        per = number(ex.cfg.get('capital_per_market', 20))
        cap = total_cap(ex.cfg)
        res = {k: number(v) for k, v in (st.get('market_reserved') or {}).items()}
        total = sum(res.values())
        peak = max(res.values()) if res else 0.0
        if total > cap + 1e-8 or peak > per + 1e-8:
            blockers.append(f'占款仍超限：总 {total:.2f}/{cap:.2f}，单 {peak:.2f}/{per:g}')
    for flag in LOCKED_FLAGS:
        if st.get(flag):
            blockers.append('锁定标志仍成立：' + flag)
    if not st.get('activation_valid'):
        blockers.append('授权无效')
    # 挂单类原因已独立复核过链上挂单，不再要求整体快照已知（否则自锁）
    if not st.get('snapshot_known') and not order_reason:
        blockers.append('余额/订单快照仍未知')
    if not st.get('ledger_known'):
        blockers.append('账本仍未知（成本/库存估值不可信）')
    if not st.get('reward_baseline_known', False):
        blockers.append('reward基线仍未确认')
    if unresolved(ex):
        blockers.append('仍有未了结的提交')
    net = (st.get('trading_net', -1e9) + st.get('received_attributed_rewards', 0)
           + number(st.get('risk_carryforward_net', 0)))
    if net <= -number(ex.cfg.get('fuse_net_limit_abs', 10)):
        blockers.append(f'净额 {net:.4f} 已达暂停线，不可自动恢复')
    return blockers


# L1 冻结的各来源解除条件：(判断函数, 超时秒数)
# 超时后不再坚持「必须解除条件满足」，改为升级告警但继续管理 ——
# 今天实测账本读不到持续 2h40m，若死等 ledger_known 就是新的长期停摆源。
def _open_block_clears(ex, source):
    """返回 True 表示该来源的冻结条件已消失。"""
    st = ex.state
    if source == 'cancel_unconfirmed':
        pending = getattr(ex.adapter, '_cancel_unconfirmed', None)
        if isinstance(pending, set):
            # Success includes the requested keep_side, not a demand to cancel all makers.
            return not pending and bool(ex.adapter._cancel_verified)
        return _market_orders_still_open(ex) is False
    if source == 'closed_residue':
        return (bool(st.get('snapshot_known')) and not st.get('snapshot_dirty')
                and not any(scoped_coin(o.get('coin'), set(st.get('markets', {})))
                            for o in st.get('remote_orders', [])))
    if source == 'snapshot_stale':
        return bool(st.get('snapshot_known')) and not st.get('snapshot_dirty')
    if source == 'ledger_unknown':
        return st.get('ledger_known') is True
    if source == 'reward_baseline':
        return bool(st.get('reward_baseline_known', False))
    if source == 'loop_error':
        # 下一轮正常完成 tick 即视为恢复：由 tick 末尾主动清
        return True
    return False


def maybe_clear_open_block(ex):
    """尝试解除 L1 冻结。带超时兜底，避免变成新的长期停摆源。"""
    if not ex.state.get('open_blocked'):
        return False
    source = ex.state.get('open_block_source') or 'unknown'
    since = number(ex.state.get('open_block_since') or ex.now())
    elapsed = ex.now() - since
    # 各来源的超时阈值（秒）：到点即升级告警但放行，不再死等
    timeout = {
        'cancel_unconfirmed': 600,     # 10 分钟
        'closed_residue': 600,
        'snapshot_stale': 180,         # 3 分钟
        'ledger_unknown': 900,         # 15 分钟
        'reward_baseline': 1800,       # 30 分钟
        'loop_error': 60,
    }.get(source, 900)

    if _open_block_clears(ex, source):
        clear_open_block(ex)
        ex.state['open_block_cleared_note'] = f'{source} 条件已消失，解除 L1'
        return True
    if elapsed >= timeout and source not in ('cancel_unconfirmed', 'closed_residue', 'snapshot_stale'):
        # 超时兜底：不再冻结新仓，但留下告警供排查
        clear_open_block(ex)
        ex.state['open_block_timeout_alert'] = {
            'source': source, 'elapsed': int(elapsed),
            'note': '冻结条件超时仍未消失，已放行新仓（继续管理，请排查）',
        }
        return True
    return False


def maybe_resume(ex):
    """在 tick 末尾尝试解除「可自愈类」暂停；不满足则保持并记录阻塞原因。"""
    if not ex.state.get('halted'):
        return False
    blockers = resume_blockers(ex)
    ex.state['resume_blockers'] = blockers
    if blockers:
        return False
    previous = ex.state.get('halt_reason', '')
    ex.state.update(halted=False, halt_reason='', data_pause_reason=None,
                    halt_actions_applied=False,
                    last_auto_resume={'at': ex.now(), 'from': previous})
    ex.state_save()
    log_fn = getattr(ex, 'log', None)
    if callable(log_fn):
        log_fn(f'  ▶️ 自动解除暂停（原原因：{previous[:60]}）')
    return True


def checkpoint(ex, reward, net, period=None):
    meta = dict(period or {})
    pid = meta.get('payout_id')
    if not pid:
        ex.state.update(halted=True, ledger_known=False, halt_reason='检查点缺稳定payout身份')
        ex.state_save()
        return 0.0, ex.state['halt_reason'], {'ledger_known': False}
    journal(ex)
    previous = ex.state['rewards'].get(pid)
    record = previous or {**meta, 'reward': float(reward), 'ledger_known': False,
                          'attributed': meta.get('attribution_confirmed') is True}
    if previous and previous['reward'] != float(reward):
        raise ValueError('同一payout金额冲突')
    ex.state['rewards'][pid] = record
    # Legacy callers can supply full-experiment totals explicitly, never slices.
    if isinstance(net, dict) and net.get('scope') == 'experiment_all':
        ex.state['trading_net'] = net.get('net_float', float(net.get('net', 0)))
        ex.state['ledger_known'] = net.get('known') is True
    recompute_net(ex)
    ex.state['settled_periods'] = len(ex.state['rewards'])
    ex.state_save()
    return ex.state.get('cum_net'), ex.state.get('halt_reason', ''), record


def recompute_net(ex):
    known = ex.state.get('ledger_known') is True
    reward = sum(r['reward'] for r in ex.state.get('rewards', {}).values() if r.get('attributed'))
    ex.state['received_attributed_rewards'] = reward
    if not known:
        if 'budget_data_retry_at' in ex.state:
            ex.state.update(cum_net=None, net_confidence='deferred', rest_budget_blocked=True)
            return
        ex.state.update(cum_net=None, net_confidence='unknown', halted=True,
                        halt_reason='实验覆盖/实际成本/库存退出估值未知，停止新仓并继续管理')
        return
    period_net = number(ex.state.get('trading_net', 0)) + reward
    net = period_net + number(ex.state.get('risk_carryforward_net', 0))
    ex.state.update(period_net=period_net, cum_net=net, net_confidence='observed_experiment')
    # 阈值从配置读（2026-10-30 改为本金 10%）：硬约束 = net_loss_limit，
    # 提前暂停 = fuse_net_limit_abs（默认取硬约束的 83%，留缓冲）。
    hard = -number(ex.cfg.get('net_loss_limit_after_reward_usdc', 12))
    early = -number(ex.cfg.get('fuse_net_limit_abs', 10))
    # 2026-11-05 修复熔断误触发（实测事故 02:31:26）：
    #   trading_net 从 -2.34 骤降到 -36.02，5 秒后回到 -2.53，却触发了
    #   「净亏达到33.56提前暂停」并清仓离场；实际全程只亏 $1.87。
    #   根因：净值按账本事件累加，merge 两腿/成交入账存在瞬时中间态
    #   （一腿已写入、另一腿未写入），该窗口内累加值会瞬间放大；
    #   原实现拿单次采样直接判定，正好命中就误熔断。
    #
    # 修法（用户 2026-11-05 03:04 拍板 A+C）：
    #   A 连续确认：同一阈值状态连续 FUSE_CONFIRM_SAMPLES 次采样成立才熔断，
    #     瞬时毛刺被过滤；真实亏损持续则第 2 次即触发，延迟仅一个 tick。
    #   C 合并豁免：任一市场有 merge_pending 时本 tick 不判定（净值处于中间态），
    #     保留计数不清零，避免合并窗口内的抖动被当成持续亏损。
    _fuse = ex.state.get('fuse_streak') or {}
    # merge_pending 在请求发出后仍保留（供成交归属匹配），不能无条件视为"正在合并"。
    # 只认提交后 FUSE_MERGE_GRACE_SEC 秒内的窗口——那才是净值处于中间态的时段。
    _now_ms = int(ex.now() * 1000)
    _grace_ms = int(FUSE_MERGE_GRACE_SEC * 1000)
    _merging = any(
        (ms.get('merge_pending') or {}).get('submitted_ms') is not None
        and _now_ms - int(ms['merge_pending']['submitted_ms']) <= _grace_ms
        for ms in (ex.state.get('markets') or {}).values())
    if _merging:
        ex.state['fuse_skipped_merging'] = int(ex.state.get('fuse_skipped_merging', 0)) + 1
    else:
        _hit = 'hard' if net <= hard else ('early' if net <= early else None)
        if _hit is None:
            ex.state['fuse_streak'] = {}
        else:
            _fuse[_hit] = int(_fuse.get(_hit, 0)) + 1
            ex.state['fuse_streak'] = _fuse
            if _fuse[_hit] >= FUSE_CONFIRM_SAMPLES:
                ex.state.update(halted=True, halt_reason=(
                    f'净亏达到{abs(hard):.2f}硬约束，立即收尾' if _hit == 'hard'
                    else f'净亏达到{abs(early):.2f}提前暂停，收尾'
                ) + f'（连续{_fuse[_hit]}次确认）')


def _order_filled_qty(order, remote=None):
    '从 orderStatus 的 order 字段计算实际成交量。\n\nsz 表示剩余未成交量，成交量为 origSz 减 sz。\n字段缺失或含义不明时返回 None；调用方必须按未知处理，\n不能将 None 视为零成交。'
    src = order or {}
    if not isinstance(src, dict):
        return None
    try:
        orig = src.get('origSz')
        left = src.get('sz')
        if orig is None or left is None:
            return None
        orig = Decimal(str(orig))
        left = Decimal(str(left))
        if orig < 0 or left < 0:
            return None
        filled = orig - left
        return float(filled) if filled >= 0 else None
    except (InvalidOperation, TypeError, ValueError):
        return None


class RuntimeLoop:
    """Mixin used by LiveRuntime, injected mocks use the exact production tick."""
    def cache_book(self, data):
        if not isinstance(data, dict) or not data.get('levels') or data.get('time') is None:
            return
        now = self.executor.now()
        if not 0 <= now-number(data['time'])/1000 <= 5:
            return
        if hasattr(self.adapter, '_books'):
            self.adapter._books[data['coin']] = (data, now)
        self.state.bids[data['coin']] = number(data['levels'][0][0]['px'])

    def drain_events(self):
        while True:
            try:
                kind, data = self.state.events.get_nowait()
            except queue.Empty:
                break
            if kind == 'book':
                self.cache_book(data)
            elif kind == 'fills':
                self._incoming_fills = getattr(self, '_incoming_fills', [])+data
                # Balance/order cache must not bless a state before this fill.
                self._snapshot_at = -1e30
                invalidate = getattr(self.executor.adapter, 'invalidate_open_orders_cache', None)
                if invalidate is not None:
                    invalidate()
                self.executor.state['snapshot_dirty'] = True

    def reconcile_intents(self):
        ex = self.executor
        for intent in journal(ex).values():
            if intent['status'] not in ('unknown', 'submitted', 'awaiting_fill'):
                continue
            if ex.now()-intent.get('checked_at', -1e30) < 15:
                continue
            result = self.info_fn({'type': 'orderStatus', 'user': self.owner,
                                   'oid': intent.get('oid', intent['client_id'])})
            intent['checked_at'] = ex.now()
            if not isinstance(result, dict) or result.get('status') != 'order':
                # 用户 2026-10-28 22:16：扫市场 + 双边下单只要几秒，没有 60 秒可等。
                # cloid 在发请求前就写进 journal，HL 收到就必有记录：
                #   返回 unknownOid = HL 没收到这个请求 = 不存在，**当轮即定性**。
                # 查询本身失败（拿不到 dict）不算数，保持 unknown 下轮再试。
                hit_unknown_oid = (isinstance(result, dict)
                                   and str(result.get('status') or '').lower() == 'unknownoid')
                # 只在「还没拿到 oid、只能用 cloid 查」时才判 absent：
                #   - 没 oid：cloid 是我们自己生成并先写 journal 的，HL 查不到 = 没收到
                #   - 已有 oid：那这个订单客观上存在过（响应里返回了 oid），
                #     此时 unknownOid 与之矛盾，属于查询异常，不能据此解除锁定
                if hit_unknown_oid and not intent.get('oid'):
                    intent['status'] = 'absent'
                    intent['absent_reason'] = (
                        'HL 返回 unknownOid：cloid 在发请求前已生成，'
                        '查不到即该请求未到达 HL → 判定不存在')
                    logger = getattr(ex, 'log', None) or getattr(self.executor, 'log', None)
                    if callable(logger):
                        logger(f"  ⚪ {intent['client_id']} 判 absent：{intent['absent_reason']}；不重发")
                else:
                    intent['status'] = 'unknown'
                continue
            remote = result.get('order') or {}
            order = remote.get('order') or {}
            if order.get('oid') is not None:
                intent['oid'] = order['oid']
                if str(order['oid']) not in ex.state['submitted_oids']:
                    ex.state['submitted_oids'].append(str(order['oid']))
            status = remote.get('status')
            if status in ('filled', 'canceled', 'rejected', 'marginCanceled', 'reduceOnlyCanceled'):
                if intent.get('remote_final') != status:
                    invalidate = getattr(getattr(ex, 'adapter', None), 'invalidate_open_orders_cache', None)
                    if invalidate is not None:
                        invalidate()
                intent['remote_final'] = status
                # 2026-11-01 修复（零成交撤单永久卡死）：
                # 原写法把「卖出 + 任何非 rejected 状态」一律记成 awaiting_fill，
                # 包括 canceled。而清除 awaiting_fill 的唯一条件要求「有对应成交记录」
                # （见 bind_ledger 里的 evidenced），零成交的撤单永远没有成交记录，
                # 于是 unresolved() 恒为真 → unwind 永久返回「不重复提交卖出」，
                # 单边仓位既卖不掉也没有挂单在等（实测 11 个 tick 复现）。
                #
                # awaiting_fill 的本意是「已有成交，等账本把成交写进来」。
                # 判据用 orderStatus 自带的 sz/origSz（2026-11-01 实测确认真实语义）：
                #   全成交   filled  sz=0.0    origSz=20.0  → 已成交 20
                #   零成交撤 canceled sz=20.0  origSz=20.0  → 已成交 0
                # 即 sz = 剩余未成交量，成交量 = origSz − sz。
                # 成交量为 0 的单没有任何账本记录可等 → 立即 final，解除阻塞。
                filled_qty = _order_filled_qty(order, remote)
                if status == 'rejected':
                    intent['status'] = 'final'
                elif filled_qty is not None and filled_qty <= 0:
                    intent['status'] = 'final'      # 零成交（含零成交撤单）：没东西可等
                elif status == 'filled' or (filled_qty is not None and filled_qty > 0):
                    intent['status'] = 'awaiting_fill'
                elif not intent['buy']:
                    # 卖出拿不到 sz/origSz（字段缺失）→ 无法证明零成交，
                    # 保守留在 awaiting_fill，由 bind_ledger 用成交证据裁决
                    intent['status'] = 'awaiting_fill'
                else:
                    intent['status'] = 'final'
            elif status == 'open' and intent.get('tif') == 'Alo':
                # 2026-11-01 修复（挂着的卖单被误判 unknown → 永久阻塞清仓）：
                # 原条件只对**买入** Alo 单判 open，卖出单即便好好挂在盘上
                # 也一律落到 else 分支记成 unknown，而 unknown 在 unresolved()
                # 里算「未了结」，于是 maker 卖单一挂出去就把清仓流程锁死：
                # 既不再补挂、也不会转 taker（实测 11 个 tick 复现）。
                #
                # open 的语义就是「还在盘上等成交」，买卖两侧相同。
                # 卖出单由 orderStatus 直接确认在盘 → 记 submitted（不阻塞），
                # 是否重复挂由 maker_exit_resting 用 openOrders 实测，不靠这里挡。
                # 买入侧维持原口径（未见快照时留 unknown），避免改动报价路径。
                if intent['buy']:
                    visible = any(str(o['oid']) == str(intent.get('oid'))
                                  for o in ex.state.get('remote_orders', []))
                    intent['status'] = 'submitted' if visible else 'unknown'
                else:
                    intent['status'] = 'submitted'
            else:
                # 2026-11-08 修复（僵尸 intent 卡死全系统 9 小时）：
                # 原实现是 `intent['status'] = 'unknown'`，而上面的终态判定是
                # **正向枚举**（filled/canceled/rejected/marginCanceled/
                # reduceOnlyCanceled）。HL 只要回一个新状态名就掉进这里，
                # 每轮重新确认成 unknown，永远出不来。
                #
                # 实测：orderStatus 回 `badAloPxRejected`（Alo 限价越界被拒，
                # sz=33.0 origSz=33.0 成交 0），该状态全代码库 0 命中。
                # 后果：unresolved() 恒为 True → merge / unwind / 新开仓全被掐死。
                #
                # 改为负向判定：**只要 not open，就是终态**，
                # 用 _order_filled_qty 区分有没有成交：
                #   成交 0     → final（没东西可等）
                #   有成交     → awaiting_fill（等账本把成交写进来）
                #   拿不到数据 → 保守留 unknown（fail-closed，不赌）
                if status == 'open':
                    intent['status'] = 'submitted'
                else:
                    _fq = _order_filled_qty(order, remote)
                    if _fq is not None and _fq <= 0:
                        intent['status'] = 'final'
                    elif _fq is not None and _fq > 0:
                        intent['status'] = 'awaiting_fill'
                    else:
                        intent['status'] = 'unknown'
                    intent.setdefault('remote_final', status)
                    try:
                        logger = getattr(ex, 'log', None)
                        if callable(logger):
                            logger('  ⚪ %s 判终态：HL 状态 %r，成交 %s'
                                   % (intent.get('client_id'), status,
                                      ('%g' % _fq) if _fq is not None else '未知'))
                    except Exception:
                        pass
        ex.state_save()

    def bind_ledger(self):
        ex = self.executor
        identity = {'experiment_id': ex.state.get('experiment_id'), 'owner': self.owner.lower(),
                    'markets': sorted(str(c['outcome_id']) for c in ex.candidates),
                    'experiment_start_ms': ex.state['experiment_start_ms'],
                    'opening_baseline': fingerprint(ex.state['opening_evidence']),
                    'authorization_fingerprint': ex.state.get('authorization_fingerprint'),
                    'config_fingerprint': ex.state.get('config_fingerprint')}
        if ex.cfg.get('dynamic_candidates_enabled'):
            identity.update(identity_version=2,
                            authorization_windows=ex.state.get('authorization_windows', []))
            identity['markets'] = sorted({str(m) for w in identity['authorization_windows']
                                          for m in w['markets']})
        try:
            dynamic = ex.cfg.get('dynamic_candidates_enabled')
            if dynamic:
                from c_runtime import sync_order_commitments
                unbound = self.ledger._stored_identity() is None
                if not unbound:
                    sync_order_commitments(ex)
            self.ledger.bind_experiment(identity)
            if dynamic and unbound:
                sync_order_commitments(ex)
        except ValueError:
            ex.state.update(ownership_unknown=True, ledger_known=False)
            raise
        self.experiment_identity = identity
        return identity

    def _settlement_authorized(self, fill, oid):
        '结算成交是否属于本实验。\n\n        历史版本 新增。复用账本的 _v2_fill_authorized 作为权威判据，\n        保证「运行层放行的 ⊆ 账本能入账的」，不另造一套标准。\n\n        fail-closed：判据不可用 / 抛异常 / 返回非 True，一律不放行。\n        '
        try:
            ident = self.experiment_identity
        except AttributeError:
            ident = None
        if not ident:
            return False
        # 注意：`_v2_fill_authorized` 是 **ledger.py 的模块级函数**
        # （ledger.py:113 `def _v2_fill_authorized(identity, fill, commitments=())`），
        # 不是 Ledger 的方法。写 `self.ledger._v2_fill_authorized` 会取不到，
        # 让整个判据恒为 False，等于 Settlement 永远被拦 —— 那是假的修复。
        try:
            from ledger import _v2_fill_authorized as fn
        except Exception:
            return False
        try:
            # 签名 (identity, fill, commitments=())，identity 在前。
            return fn(ident, fill) is True
        except Exception:
            return False

    def collect_fills(self, snap):
        self.bind_ledger()
        ex = self.executor
        start = int(ex.state['experiment_start_ms'])
        until = int(ex.now()*1000)
        coverage = ex.state.get('fill_coverage') or {}
        retention_ms = number(coverage.get('retention_seconds', 0))*1000
        cap = number(coverage.get('max_results', 0))
        proof = self.ledger.fill_coverage()
        frontier = proof['through_ms'] if proof else start
        # 86400 is the authorized maximum continuous observation gap, not an
        # exchange retention guarantee. Legacy recovery needs a full-account
        # response crossing the experiment start, independently of local rows.
        bootstrap = proof is None and until-start >= retention_ms
        if (coverage.get('verified') is not True or not coverage.get('evidence')
                or not 0 < retention_ms < float('inf') or not 0 < cap <= 2000
                or until < frontier or (proof is not None and until-frontier >= retention_ms)):
            raise ValueError('REST成交完整覆盖/保留期无法证明')
        since = start
        coverage_interval = None
        coverage_source = None
        if ex.now() < getattr(self, '_fills_retry_at', 0):
            raise BudgetUnavailable('成交覆盖等待调度', retry_at=self._fills_retry_at)
        if ex.now()-getattr(self, '_fills_at', -1e30) >= ex.cfg.get('fills_refresh_seconds', 30):
            # 2026-10-30：成交查询单次权重 = 20 + ceil(2000/20) = 120，占每分钟预算的 1/5。
            # 原实现只在**成功**后更新 _fills_at，一旦因预算不足抛异常就永远保持旧值，
            # 于是每一轮 tick 都重试、每次都尝试扣 120 → 预算永远恢复不了（自锁死循环）。
            # 修法：无论成败都记录尝试时间，失败时按指数退避拉长间隔。
            try:
                from fill_history import validate_history
                request = {'type': 'userFillsByTime', 'user': self.owner,
                           'startTime': 0, 'endTime': until, 'aggregateByTime': False}
                fills = self.info_fn(request)
                coverage_source = validate_history(request, fills, owner=self.owner,
                                                   start=start, until=until, cap=cap,
                                                   bootstrap=bootstrap)
                # 2026-11-01：把实际返回笔数回报给预算层，让 userFillsByTime 的
                # 权重预扣跟随真实规模（原来无条件按 2000 笔预扣，实测只返回 18 笔，
                # 每分钟白扣约 200 权重，正好挤掉撤单复核所需的 openOrders）。
                # 覆盖校验阈值仍是 2000（上面那行），不受影响。
                if hasattr(self.info_fn, 'note_fill_count'):
                    self.info_fn.note_fill_count(len(fills))
            except BudgetUnavailable as exc:
                self._fills_retry_at = exc.retry_at or ex.now()+1
                raise
            except Exception:
                # 记录尝试时间 + 退避，避免每轮都重撞预算
                fails = getattr(self, '_fills_fails', 0) + 1
                self._fills_fails = fails
                backoff = min(300, 30 * (2 ** min(fails - 1, 4)))
                self._fills_retry_at = ex.now() + backoff
                raise
            self._fills_fails = 0
            self._fills_retry_at = 0
            coverage_interval = (since, until)
        else:
            fills = list(self._fills_cache)
        rest_fills = list(fills)
        incoming = list(getattr(self, '_incoming_fills', []))
        self._incoming_fills = []
        while True:
            try:
                kind, data = self.state.events.get_nowait()
            except queue.Empty:
                break
            if kind == 'fills':
                incoming.extend(data)
            elif kind == 'book':
                self.cache_book(data)
        fills = fills + incoming
        ids = ({str(c['outcome_id']) for c in ex.candidates}
               | set(ex.state.get('markets', {})) | set(self.ledger._stored_identity()['markets']))
        oids = set(ex.state.get('submitted_oids', []))
        accepted = []
        for f in fills:
            if int(f.get('time', 0)) < start or not scoped_coin(f.get('coin'), ids):
                continue
            coin = '#' + str(f['coin'])[1:]
            oid = str(int(coin[1:])//10)
            if f.get('dir') == 'Merge Outcome':
                from ledger import event_id
                key = event_id(self.owner, f)
                verified = ex.state.get('verified_merge_events', {})
                pending = ex.state['markets'].get(oid, {}).get('merge_pending')
                if key in verified:
                    accepted.append(f)
                elif (pending and f['time'] >= pending['submitted_ms']
                      and number(f['sz']) == pending['qty'] and f.get('side') == 'A'):
                    accepted.append(f)
                else:
                    ex.state['ownership_unknown'] = True
                    raise ValueError('实验市场发现无法归属本实验的成交')
            elif str(f.get('oid')) in oids:
                accepted.append(f)
            elif str(f.get('tid')) in (ex.state.get('manual_fills_confirmed') or {}):
                # 2026-11-05 人工确认认领通道（用户 13:13 拍板 C 方案）：
                # 操作者在主循环之外手工下过平仓单时，这些成交没有 cloid 承诺、
                # 也不在 submitted_oids 里，原实现一律判「无法归属」→
                # ownership_unknown=True → 永久 halt（实测反复发生：每次手工清仓
                # 都会让下次启动卡住，只能靠换账本绕过）。
                # 现在：操作者明确确认过的成交 tid 记入 manual_fills_confirmed，
                # 认领时按 tid 命中即接受。名单只包含人工逐一确认过的 tid，
                # 不是通配放行；未登记的陌生成交仍走原 fail-closed 分支。
                accepted.append(f)
            elif (ex.cfg.get('dynamic_candidates_enabled')
                  and f.get('dir') == 'Buy' and f.get('side') == 'B'
                  and f.get('cloid')
                  and any(i.get('order_commitment', {}).get('cloid') == f['cloid']
                          and i.get('coin') == coin and i.get('sent') is not False
                          for i in journal(ex).values())):
                # A timed-out submit may fill before orderStatus supplies its oid.
                # The ledger still verifies the durable commitment and size cap.
                accepted.append(f)
            elif (f.get('dir') == 'Settlement' and f.get('side') == 'A'
                    and self._settlement_authorized(f, oid)):
                # 2026-11-08 修复（Settlement 无法归属 → 永久 halt）：
                # 到期结算把持仓按 1.0 兑现，交易所**不分配 oid、也没有 cloid**，
                # 所以它过不了前面任何一条准入（不是 Merge Outcome、不在
                # submitted_oids、不是人工确认、不是 Buy+cloid）。
                # 而 ledger.py:122 的 _v2_fill_authorized 明确把 Settlement
                # 列为合法 disposal —— 账本愿意入账，运行层不认，于是永久 halt。
                #
                # 实测涉事两笔：11-08 13:24:57 #258610 x60、14:37:55 #258631 x33，
                # 都是 side=A、px=1.0，落在授权窗口 12 内。
                #
                # 拦截陌生结算**靠账本判据**（校验 market 在授权窗口内且
                # identity 认可），不靠 ex.state['markets'] 记录 —— 后者会被
                # setdefault 预先建出来，对陌生市场几乎恒真，拦不住。
                accepted.append(f)
            else:
                # Other strategies stay out of this ledger; shared-market activity
                # invalidates isolation instead of silently blessing it.
                ex.state['ownership_unknown'] = True
                raise ValueError('实验市场发现无法归属本实验的成交')
        # A pending intent can explain exactly one equal two-leg remote event.
        from ledger import event_id
        for oid, ms in ex.state['markets'].items():
            pending = ms.get('merge_pending')
            new = {event_id(self.owner, f): f for f in accepted
                   if f.get('dir') == 'Merge Outcome'
                   and str(int(str(f['coin'])[1:])//10) == oid
                   and event_id(self.owner, f) not in ex.state.get('verified_merge_events', {})}
            if new and (not pending or len(new) != 2
                        or {str(f['coin'])[1:] for f in new.values()} != {str(int(oid)*10), str(int(oid)*10+1)}
                        or len({str(f['hash']).lower() for f in new.values()}) != 1):
                raise ValueError('merge两腿身份不完整/多个无法唯一归属的merge')
        self.accounting.ingest_fills(accepted, coverage_interval=coverage_interval,
                                     coverage_source=coverage_source)
        if coverage_interval is not None:
            self._fills_cache, self._fills_at = rest_fills, ex.now()
        # Downstream order quantities and intent evidence require all durable
        # fills, including those that have aged out of the REST overlap.
        accepted = [json.loads(raw) for (raw,) in
                    self.ledger.db.execute('SELECT payload FROM events')]
        closing = {f'#{int(oid)*10+int(s)}': str(q) for oid, p in snap['positions'].items()
                   for s, q in p.items()}
        # 2026-10-30 根因修复：opening 之前被硬编码成空字典 {}，导致账本永远报
        # 'missing verified opening inventory and cost basis' → 算不出库存成本
        # → inventory_exit 为空 → wait_single 拿不到 lot → 判「成本未知」→
        # 单边成交后的仓位被强制清仓（今日 3 次，全部白付手续费）。
        # 注意：双边成交走 merge，不查 inventory_exit，所以这个 bug 只在单边触发。
        #
        # opening 必须来自**实验开始时的真实快照**，而不是拍脑袋的空 dict：
        #   - opening_evidence.snapshot.positions = {oid: {side: qty}}
        #   - 账本要的 opening = {'#<oid*10+side>': {'qty': .., 'cost': ..}}
        # 期初持仓若不为空，成本无法从快照反推（快照只有数量），此时宁可如实报
        # 未知（cost 留空 → 账本报 unvalued），也不要编一个假成本把风险藏起来。
        opening = {}
        oe = ex.state.get('opening_evidence') or {}
        for oid_s, sides in ((oe.get('snapshot') or {}).get('positions') or {}).items():
            for side_s, qty in (sides or {}).items():
                coin = f'#{int(oid_s)*10+int(side_s)}'
                q = str(qty)
                opening[coin] = {'qty': q, 'cost': '0' if number(qty) == 0 else ''}
        # Fills are durable before waiting: never compare post-snapshot events
        # with cached balances, or discard their coverage/ownership evidence.
        if snap is getattr(self, '_snapshot', None):
            latest = max((int(f['time']) for f in accepted), default=0)
            if latest > getattr(self, '_snapshot_started_ms', float('inf')):
                pending = ex.state.setdefault('snapshot_sync_pending', {})
                pending['latest_fill_ms'] = latest
                ex.state.update(snapshot_known=False, snapshot_dirty=True)
                invalidate = getattr(self.adapter, 'invalidate_open_orders_cache', None)
                if invalidate is not None:
                    invalidate()
                raise BudgetUnavailable('成交晚于库存快照，等待刷新后重新对账',
                                        retry_at=ex.now()+1)
        rep = self.ledger.report(opening=opening, opening_evidence=ex.state['opening_evidence'],
                                 closing=closing, coverage={'complete': True})
        self.ledger_report = rep
        ignored = 'missing scoped cash / reward / transfer reconciliation evidence'
        issues = [i for i in rep['issues'] if i != ignored]
        if (issues == ['closing inventory mismatch']
                and snap is getattr(self, '_snapshot', None)
                and (self.ledger.fill_coverage() or {}).get('through_ms', float('inf'))
                    < getattr(self, '_snapshot_started_ms', -float('inf'))):
            # A new balance cannot reconcile against an older REST fill set.
            # WS may also arrive out of order; only the next covered REST view
            # can distinguish that race from a real closing inventory error.
            # Keep the existing refresh/budget schedule and all source checks.
            pending = ex.state.setdefault('snapshot_sync_pending', {})
            pending['fills_through_ms'] = self.ledger.fill_coverage()['through_ms']
            ex.state.update(snapshot_known=False, snapshot_dirty=True)
            invalidate = getattr(self.adapter, 'invalidate_open_orders_cache', None)
            if invalidate is not None:
                invalidate()
            raise BudgetUnavailable('库存与缓存成交覆盖未对齐，等待原调度刷新后重新对账',
                                    retry_at=self._snapshot_at + number(ex.cfg.get(
                                        'snapshot_min_seconds',
                                        ex.cfg.get('snapshot_refresh_seconds', 15))))
        if issues:
            raise ValueError('; '.join(issues))
        for intent in journal(ex).values():
            if intent['status'] == 'awaiting_fill' and intent.get('remote_final'):
                evidenced = any(str(f.get('oid')) == str(intent.get('oid')) and f.get('side') == ('B' if intent['buy'] else 'A') for f in accepted)
                if evidenced:
                    intent['status'] = 'final'
        ex.state['merge_evidence_known'] = True
        hashes = {}
        for g in rep['realizations']:
            pending = ex.state['markets'].get(g['market_id'], {}).get('merge_pending')
            if g['kind'] == 'Merge Outcome' and g['net'] is not None and pending and g['time'] >= pending['submitted_ms']:
                if number(g['paired_qty']) == pending['qty']:
                    hashes.setdefault(g['market_id'], []).extend(g['event_ids'])
                    for key in g['event_ids']:
                        ex.state.setdefault('verified_merge_events', {})[key] = {
                            'market_id': g['market_id'], 'event_ids': g['event_ids'],
                            'submitted_ms': pending['submitted_ms'], 'qty': pending['qty']}
        # Commit verified identities while pending still exists. Crash before this
        # commit replays the pending intent; clearing pending uses the same journal.
        ex.state_save()
        ex.state['merge_fill_hashes'] = hashes
        inventory = rep['inventory']
        trading = number(rep['matched_realized_net_subtotal'])
        reserved = {}
        market_realized = {oid: number(v['matched_realized_net_subtotal'])
                           for oid, v in rep['by_market'].items()}
        market_net = dict(market_realized)
        inventory_exit = {}
        for coin, lot in inventory.items():
            qty = number(lot['qty'])
            if qty < 0 or number(lot['unvalued_cost_qty']) != 0:
                raise ValueError('实际库存成本未知')
            oid = str(int(coin[1:])//10)
            cost = number(lot['known_cost'])
            reserved[oid] = reserved.get(oid, 0)+cost
            if qty:
                # 2026-11-05：止损/熔断复核必须用最新盘口，不能吃缓存。
                # 兼容不支持 force 的 adapter/测试替身（回落到普通读取）。
                try:
                    book = self.adapter._book(coin, force=True)
                except TypeError:
                    book = self.adapter._book(coin)
                if not book:
                    raise ValueError('库存可执行盘口未知/过期')
                left, proceeds = qty, 0.0
                for level in book['levels'][0]:
                    take = min(left, number(level['sz']))
                    execution_px = float(price_wire(Decimal(str(level['px']))*Decimal('.998'), tif='Ioc'))
                    proceeds += sell_proceeds(take, execution_px)
                    left -= take
                    if left <= 1e-8:
                        break
                if left > 1e-8:
                    raise ValueError('可执行bid深度不足，无法保守估值')
                # 2026-11-05 估值合理性下限（事故：薄盘口算出 0.0523 vs 真实 bid 0.3408，
                # 差 6.5 倍，直接把 trading_net 打到 -18 并触发单市场 $4 止损）。
                # 逐档 walk 的均价若远低于 best_bid，这个"可成交价"不代表合理退出价，
                # 判为不可执行：不参与风控，交易照常；等 VALUATION_RETRY_SEC 后重试。
                _best_bid = number(book['levels'][0][0]['px'])
                _avg = proceeds/max(qty, 1e-9)
                if _best_bid > 0 and _avg < _best_bid*VALUATION_FLOOR_RATIO:
                    # 2026-11-06 修复计数噪音：原实现每 tick 都 +1，
                    # 实测 1 次真实薄盘口（#242560 14:25:28）在 4.6 分钟内被
                    # 累加成 211 次，让人误判"阈值偏紧"。
                    # 现在只在「该 coin 首次进入不可执行状态」时 +1：
                    # 连续 tick 重复标记同一 coin 不再累加，解除后再次触发才递增。
                    _vu = ex.state.setdefault('valuation_unreliable', {})
                    _is_new = coin not in _vu
                    _prev_episodes = int((_vu.get(coin) or {}).get('episodes') or 0)
                    _vu[coin] = {
                        'at_ms': int(ex.now()*1000),
                        'best_bid': _best_bid,
                        'walked_avg': _avg,
                        'ratio': _avg/_best_bid,
                        'qty': qty,
                        'since_ms': (_vu[coin].get('since_ms') if not _is_new
                                     else int(ex.now()*1000)),
                        'episodes': _prev_episodes + (1 if _is_new else 0),
                    }
                    if _is_new:
                        ex.state['valuation_unreliable_count'] = (
                            int(ex.state.get('valuation_unreliable_count', 0)) + 1)
                    # 不计入 trading/market_net，避免用失真估值触发风控
                    continue
                else:
                    (ex.state.get('valuation_unreliable') or {}).pop(coin, None)
                inventory_exit[coin] = {'qty': qty, 'cost': cost, 'exit_value': proceeds}
                trading += proceeds-cost
                market_net[oid] = market_net.get(oid, 0)+proceeds-cost
        # REST and WS overlap; count each immutable Buy fill once per order.
        # A partially filled coin can still have a real unfilled Buy remainder.
        filled_by_oid, seen_fills = {}, set()
        for f in accepted:
            key = event_id(self.owner, f)
            if key in seen_fills or f.get('side') != 'B':
                continue
            seen_fills.add(key)
            key_oid = str(f.get('oid'))
            filled_by_oid[key_oid] = filled_by_oid.get(key_oid, 0) + number(f['sz'])
        intents_by_oid = {str(i['oid']): i for i in journal(ex).values()
                          if i.get('oid') is not None}
        for o in snap['orders']:
            if scoped_coin(o['coin'], ids):
                if str(o['oid']) not in oids:
                    ex.state['ownership_unknown'] = True
                    raise ValueError('实验市场存在其他策略/未知挂单')
                if o['side'] == 'B':
                    oid = str(int(str(o['coin'])[1:])//10)
                    remaining = number(o['sz'])
                    intent = intents_by_oid.get(str(o['oid']))
                    if intent is not None:
                        remaining = min(remaining, max(0, number(intent['qty']) -
                            filled_by_oid.get(str(o['oid']), 0)))
                    reserved[oid] = reserved.get(oid, 0)+remaining*number(o['limitPx'])
        for i in journal(ex).values():
            if i['status'] == 'unknown' and i['buy']:
                oid = str(int(i['coin'][1:])//10)
                # 2026-10-31 修复（占款重复计算导致误 halt）：
                # 原实现「即使远端订单也已占用，仍保守再加一次」——
                # 实测后果：O19634 双边挂单共 $19.99，journal 里那笔已出现在
                # openOrders 的 unknown 意图又被加了 $9.57，market_reserved 变 $29.57，
                # 撞上「单市场 $20」上限 → halt → 清仓，成交后 1 分钟就被卖掉。
                # 保守累加只应覆盖「远端看不到、可能仍在途」的那部分，
                # 已在 openOrders 出现（或已有 oid）的不再重复计。
                # 只跳过「当前确实还挂在 openOrders 里」的那一笔（已按实际挂单计过）。
                # 不能用 oids（历史提交记录，含已撤销/已成交的）判断，否则
                # 一张已经不在盘口的在途单就会被漏计，占款变少反而不安全。
                live_oids = {str(o.get('oid')) for o in snap['orders']}
                if i.get('oid') is not None and str(i['oid']) in live_oids:
                    continue
                filled = filled_by_oid.get(str(i.get('oid')), 0)
                if i.get('oid') is None:
                    filled = sum(number(f['sz']) for key, f in {
                        event_id(self.owner, f): f for f in accepted
                        if f.get('side') == 'B' and f.get('cloid') == i.get('client_id')
                    }.items())
                reserved[oid] = reserved.get(oid, 0)+max(0, i['qty']-filled)*i['px']
        # 2026-11-01 修复 P0-1（价格止损是死代码）——断链一：
        # 上面把 inventory_exit 算好了（每腿 qty/cost/exit_value，exit_value 是
        # 按当前盘口逐档模拟卖出的**实际可得金额**），但原来**没有写回 state**。
        # 而 wait_single() 在 `:745` 读的正是 `ex.state.get('inventory_exit')`
        # → 永远拿到空 dict → lot 恒为 None → 每次都走「账本成本缺失」兜底，
        # 止损条件根本不参与计算。
        # 生产实测（21:00）：state 里根本没有 inventory_exit 这个键。
        ex.state.pop('snapshot_sync_pending', None)
        ex.state.update(trading_net=trading, ledger_known=True, market_reserved=reserved,
                        reserved_total=sum(reserved.values()), market_exit_net=market_net,
                        merge_fill_hashes=hashes, ledger_issues=[],
                        inventory_exit=inventory_exit)
        if (ex.state.get('ownership_unknown') and ex.state.get('snapshot_known')
                and not ex.state.get('snapshot_dirty') and not unresolved(ex)):
            # Only the completed owner/scope/fill/order/inventory reconciliation
            # above can release this lock; a scan or elapsed timeout cannot.
            ex.state.update(ownership_unknown=False, ownership_reconciled_at_ms=int(ex.now()*1000))
        # 2026-10-30 方案C：上限按配置计算（不再写死 80/12）
        per_cap = number(ex.cfg.get('capital_per_market', 12))
        exposure_cap = total_cap(ex.cfg)
        if sum(reserved.values()) > exposure_cap + 1e-8 or any(v > per_cap+1e-8 for v in reserved.values()):
            ex.state.update(halted=True,
                            halt_reason=f'真实总占款/每市场占款超过上限（总{exposure_cap:.2f}/单{per_cap:g}）')

    def publish_views(self):
        from datetime import datetime, timezone
        from v2_persistence import publish_owned
        ex = self.executor
        identity = getattr(self, 'experiment_identity', None)
        if identity is None:
            return
        base = ex.state_path.parent
        view_identity = identity
        if identity.get('identity_version') == 2:
            view_identity = {k: identity[k] for k in (
                'identity_version', 'experiment_id', 'owner', 'experiment_start_ms',
                'opening_baseline', 'config_fingerprint')}
        report_path = base / ('audit_v2_' + fingerprint(view_identity)[:20]) / 'report.json'
        generated = datetime.fromtimestamp(ex.now(), timezone.utc).isoformat()
        rep = dict(getattr(self, 'ledger_report', {}) or {
            'status': 'unreconciled', 'issues': ['ledger report unavailable'],
            'realized_net': None, 'realized_loss': None})
        rep.update(experiment_id=identity['experiment_id'], generated_at=generated)
        if not ex.state.get('ledger_known'):
            rep.update(status='unreconciled', realized_net=None, realized_loss=None,
                       issues=list(dict.fromkeys(rep.get('issues', []) + ex.state.get('ledger_issues', []))))
        publish_owned(report_path, rep, view_identity)
        fields = ('markets', 'cum_net', 'settled_periods', 'halted', 'halt_reason',
                  'ledger_known', 'snapshot_known', 'net_confidence', 'experiment_id',
                  # 观察期要看的三项（2026-10-28 22:05 补）：没有这些，看板无法
                  # 区分「配对保护中」和「出事了」，也看不到每市场累计亏损进度。
                  'market_exit_net', 'trading_net', 'reserved_total',
                  'market_reserved', 'stop_applicable', 'inventory_exit')
        view = {k: ex.state.get(k) for k in fields}
        view.update(updated=int(ex.now()), generated_at=generated, ledger_report_ref=str(report_path))
        view_name = (identity['experiment_id'] + '_executor_v2_state.json'
                     if identity.get('identity_version') == 2 else 'executor_v2_state.json')
        publish_owned(base / 'state' / view_name, view, view_identity)
        ex.state['ledger_report_ref'] = str(report_path)

    def tick(self):
        if threading.get_ident() != self.loop_thread:
            raise RuntimeError('ledger/state仅允许主循环线程访问')
        ex = self.executor
        if ex.cfg.get('dynamic_candidates_enabled'):
            from c_runtime import scan_step
            scan_step(self)
        now_ms = int(ex.now()*1000)
        expiry = ex.state.get('authorization_expires_at')
        if expiry is not None and number(expiry) <= ex.now():
            ex.state.update(activation_valid=False, halted=True, halt_reason='独立候选授权到期，停止新仓并收尾')
        guard = getattr(self, 'authorization_guard', None)
        if guard is not None:
            try:
                valid = guard()
            except BudgetUnavailable:
                raise
            except Exception:
                valid = False
            if not valid:
                ex.state.update(activation_valid=False, halted=True, halt_reason='运行中授权/配置/首次激活指纹变化，停止新仓并收尾')
        self.ensure_ws()
        self.drain_events()
        self.budget.denied = False
        ids = {str(c['outcome_id']) for c in ex.candidates} | set(ex.state['markets'])
        ex.state['snapshot_known'] = False
        ex.state['merge_evidence_known'] = False
        try:
            # 2026-10-31 修复（REST 预算耗尽）：
            # 原条件 `dirty or 距上次>=15s` 让 dirty **无条件绕过**间隔限制。
            # halt 状态下每轮 maintain→unwind→cancel_all 都会把 dirty 置真，
            # 于是每秒 tick 都强制刷一次快照(22 权重)：
            #   1.5 次/秒 × 22 × 60 ≈ 1,980/分钟  > 预算 1,200 → 必然耗尽
            # 独立测同一时刻预算只用了 24，说明是进程内自我饿死。
            # 现在：dirty 只能「提前请求刷新」，仍要遵守最小间隔（默认 15s，
            # 可配 snapshot_min_seconds 调到更短）。预算因此稳定在 ~330/分钟。
            min_interval = number(ex.cfg.get('snapshot_min_seconds',
                                            ex.cfg.get('snapshot_refresh_seconds', 15)))
            due_by_age = ex.now()-getattr(self, '_snapshot_at', -1e30) >= min_interval
            pending = ex.state.get('snapshot_sync_pending')
            if pending and not due_by_age:
                raise BudgetUnavailable('快照同步等待调度',
                                        retry_at=self._snapshot_at+min_interval)
            if ex.now() < getattr(self, '_snapshot_retry_at', 0):
                raise BudgetUnavailable('快照等待调度', retry_at=self._snapshot_retry_at)
            if due_by_age:
                # 2026-10-30：与成交查询同理——快照失败时 _snapshot_at 不更新，
                # 每轮 tick 都会重试（每次 22 权重），把预算持续吃满、永远恢复不了。
                # 失败时记录尝试时间并按指数退避，让预算窗口有机会滚过去。
                try:
                    snapshot_started_ms = int(ex.now()*1000)
                    self._snapshot = snapshot(self.info_fn, self.owner, ids, getattr(self.adapter, 'get_open_orders', None))
                    self._snapshot_started_ms = snapshot_started_ms
                except BudgetUnavailable as exc:
                    self._snapshot_retry_at = exc.retry_at or ex.now()+1
                    raise
                except Exception:
                    fails = getattr(self, '_snapshot_fails', 0) + 1
                    self._snapshot_fails = fails
                    backoff = min(120, 10 * (2 ** min(fails - 1, 3)))
                    self._snapshot_retry_at = ex.now() + backoff
                    raise
                self._snapshot_fails = 0
                self._snapshot_retry_at = 0
                self._snapshot_at = ex.now()
                ex.state['snapshot_dirty'] = False
            snap = self._snapshot
            if ex.now()-self._snapshot_at > 20:
                raise ValueError('余额订单快照过期')
            ex.state.update(snapshot_known=True, remote_orders=snap['orders'],
                            free_cash=snap['cash'], snapshot_at=self._snapshot_at)
            if 'opening_evidence' not in ex.state:
                if any(any(q > 0 for q in p.values()) for p in snap['positions'].values()) or any(
                        scoped_coin(o['coin'], ids) for o in snap['orders']):
                    raise ValueError('新实验期初不是已核实空仓空单')
                ex.state.update(experiment_start_ms=now_ms, fill_watermark_ms=now_ms,
                                opening_evidence={'snapshot': snap, 'source': 'REST empty inventory and orders'})
                if ex.cfg.get('dynamic_candidates_enabled') and not ex.state.get('authorization_windows'):
                    ex.state['authorization_windows'] = [{
                        'at_ms': now_ms, 'end_ms': int(ex.state['authorization_expires_at']*1000),
                        'markets': [], 'authorization_fingerprint': ex.state['authorization_fingerprint']}]
                ex.state_save()
            self.reconcile_intents()
            self.collect_fills(snap)
            ex.state.pop('budget_data_retry_at', None)
        except BudgetUnavailable as exc:
            ex.state['rest_budget_blocked'] = True
            ex.state['budget_data_retry_at'] = exc.retry_at or ex.now()+1
            ex.state['ledger_known'] = False
            snap = None if not ex.state.get('snapshot_known') else locals().get('snap')
        except Exception as exc:
            # A real error must not inherit a previous scheduling deferral.
            ex.state.pop('budget_data_retry_at', None)
            ex.state.pop('snapshot_sync_pending', None)
            if not ex.state.get('halted') or ex.state.get('data_pause_reason') == ex.state.get('halt_reason'):
                ex.state['data_pause_reason'] = str(exc)
            # 2026-11-01 halt 重构：L1。账本读不到不影响已有挂单与配对。
            # 今天实测账本读不到持续过 2h40m，若继续用 halted 会整台停摆。
            ex.state.update(ledger_known=False, ledger_issues=[str(exc)])
            block_open(ex, str(exc), source='ledger_unknown')
            snap = None if not ex.state.get('snapshot_known') else locals().get('snap')
        # Worker reads raw HTTP only; all reward and ledger writes remain here.
        try:
            self.reward_step()
            # 2026-10-30：reward_step 成功就不再算「reward轮询失败」，否则解除条件永远不成立。
            if str(ex.state.get('halt_reason', '')).startswith('reward基线/轮询失败'):
                ex.state['data_pause_reason'] = ex.state.get('data_pause_reason')
                ex.state['halt_reason'] = ex.state.get('data_pause_reason') or ''
        except BudgetUnavailable:
            raise
        except Exception as exc:
            # 2026-11-01 halt 重构：L1。reward 轮询失败不影响做市与配对。
            block_open(ex, 'reward基线/轮询失败: '+str(exc), source='reward_baseline')
            ex.state['data_pause_reason'] = 'reward基线/轮询失败: '+str(exc)
        ex.state['rest_budget_blocked'] = (self.budget.denied
            or ex.now() < ex.state.get('budget_data_retry_at', 0))
        # 2026-11-01：预算消耗实测数据（只读统计，进 state 便于直接看）
        ex.state['rest_budget_stats'] = {
            'total_charged': getattr(self.budget, 'total_charged', 0),
            'total_denied': getattr(self.budget, 'total_denied', 0),
            'by_kind': getattr(self.budget, 'stats_by_kind', {}),
            'limit': getattr(self.budget, 'limit', None),
            'reserve': getattr(self.budget, 'reserve', None),
        }
        ex.state['reward_baseline_known'] = self.watcher.state.get('baseline_complete') is True
        recompute_net(ex)
        # 2026-11-01 halt 重构：L1 场景不再写 halt_reason，
        # 所以这里不能无条件用 halt_reason 覆盖 data_pause_reason（会变成空串）。
        # 只在确实是 L2 暂停时才同步。
        if (ex.state.get('data_pause_reason') and not ex.state.get('ledger_known')
                and ex.state.get('halted')):
            ex.state['data_pause_reason'] = ex.state.get('halt_reason') or ex.state['data_pause_reason']
        try:
            maybe_resume(ex)
            maybe_clear_open_block(ex)
        except BudgetUnavailable as exc:
            ex.state['budget_recheck_at'] = exc.retry_at or ex.now()+1
        # 2026-10-30：halt_actions 只在**首次**进入暂停时执行一次。
        # 原实现每轮 halted 都调 halt()，而 halt() 会把非配对市场钉成 unwinding，
        # maintain 随即调 unwind() → cancel_all()。当快照读不到时 cancel_all 返回
        # False，于是 halt_reason 被改写成「清仓撤单未确认」——而下一轮 tick 开头
        # 又把 snapshot_known 置 False，永远来不及恢复成 True。形成自锁死循环，
        # 状态每秒写一条但 phase/snapshot 永不前进。
        # 用 halt_actions_applied 做幂等标记：只在 halted 从 False→True 的当轮执行。
        if ex.state.get('halted') and (snap is None or not ex.state.get('activation_valid')):
            # Authorization/stop cancellation does not require a balance snapshot.
            for oid in ex.state['markets']:
                try:
                    self.adapter.cancel_all(int(oid))
                except BudgetUnavailable as exc:
                    ex.state['budget_cancel_retry_at'] = exc.retry_at or ex.now()+1
        if ex.state.get('halted') and snap is not None and not ex.state.get('halt_actions_applied'):
            # 2026-11-01 halt 重构：传本轮链上快照持仓，不用 state 缓存。
            # snap 为 None（本轮快照失败）时不传 → halt() 不会推 unwinding，
            # 避免拿过期缓存误判「无持仓」而撤掉正在等配对的挂单。
            ex.halt_actions(live_positions=(snap['positions'] if snap else None))
            ex.state['halt_actions_applied'] = True
        elif not ex.state.get('halted') and ex.state.get('halt_actions_applied'):
            ex.state['halt_actions_applied'] = False
        # No-op management no longer dirties snapshots, so existing risk can run first.
        # Existing risk management has priority over new acquisition.
        try:
            maintained = ex.maintain(snap['positions'] if snap else None)
        except BudgetUnavailable:
            ex.state.update(snapshot_known=False, rest_budget_blocked=True)
            maintained = [('all', '预算不足，冻结未知风险；下轮继续检查')]
        opened = []
        if ex.cfg.get('dynamic_candidates_enabled'):
            from c_runtime import opening_candidates as dynamic_opening_candidates
            opening_candidates = dynamic_opening_candidates(self)
        else:
            opening_candidates = ex.candidates
        for c in opening_candidates:
            opened.append((c['outcome_id'], *ex.open_market(c)))
        ex.state['heartbeat'] = {'at_ms': now_ms, 'waiting': not ex.candidates,
                                  'opened': opened, 'maintained': maintained}
        if ex.now()-getattr(self, '_published_at', -1e30) >= 30:
            self.publish_views()
            if getattr(self, 'audit_path', None):
                from v2_persistence import append_record
                append_record(self.audit_path, {'at_ms': now_ms, 'known': ex.state.get('ledger_known'),
                              'net': ex.state.get('cum_net'), 'halted': ex.state.get('halted'),
                              'reason': ex.state.get('halt_reason'), 'heartbeat': ex.state['heartbeat']})
            self._published_at = ex.now()
        ex.state_save(heartbeat=True)
        return ex.state['heartbeat']

    # 2026-11-07 修复（WS 每 10 秒断连 + 扫描入册失败，同一根因）：
    #
    # LiveState.outcome_ids 只增不减——watch_market() 只 add，install_scope()
    # 也只 add，全代码库没有任何 discard/remove。市场结算后从 outcomeMeta 消失，
    # 但 ID 仍留在集合里；ensure_ws() 重连时把它一起订阅，服务器立刻踢连接。
    # 每 10 秒断一次，正好等于下面 last_reconnect 的限流节拍。
    #
    # 对照实验（11-07 09:47，本机同一出口）：
    #   只订 #225770（已结算）→ msgs=0、连接被踢
    #   只订 #258310（活跃）  → msgs=3、连接正常
    #   9 个活跃 + #22577     → 收到 18 条后仍被踢
    # 同时 REST 侧：22577/24256/24258 已不在 outcomeMeta（现有 297 个市场），
    # 对它们查 l2Book 全部 HTTP 500。
    #
    # 只用于「该不该订阅」，不参与交易准入；outcome_ids 本身保持不动
    # （成交过滤仍需要它）。
    WS_OUTCOME_REFRESH_SECONDS = 600

    def live_outcome_ids(self):
        """当前仍在 outcomeMeta 里的 outcome_id 集合。

        取不到元数据时退回上次结果；首次就失败则返回 None，调用方沿用旧行为。
        绝不因元数据不可用而缩小订阅范围——那会让风控失去盘口。
        """
        ex = self.executor
        now = ex.now()
        cached = ex.state.get('ws_live_outcome_ids')
        checked_at = number(ex.state.get('ws_live_outcome_checked_at', 0))
        if cached is not None and now - checked_at < self.WS_OUTCOME_REFRESH_SECONDS:
            return set(int(o) for o in cached)
        try:
            meta = self.info_fn({'type': 'outcomeMeta'})
        except BudgetUnavailable:
            return None
        except Exception as exc:
            self.executor.state['ws_outcome_meta_error'] = (
                type(exc).__name__ + ': ' + str(exc))
            return None
        rows = meta.get('outcomes') if isinstance(meta, dict) else None
        if not isinstance(rows, list) or not rows:
            return None
        alive = {str(r['outcome']) for r in rows
                 if isinstance(r, dict) and r.get('outcome') is not None}
        if not alive:
            return None
        live = {int(o) for o in self.state.outcome_ids if str(o) in alive}
        dropped = sorted(int(o) for o in self.state.outcome_ids if str(o) not in alive)
        ex.state['ws_live_outcome_ids'] = sorted(live)
        ex.state['ws_live_outcome_checked_at'] = now
        if dropped:
            ex.state['ws_dropped_outcome_ids'] = dropped
        return live

    def ensure_ws(self):
        ws = getattr(self, 'ws', None)
        if ws is None or getattr(self, 'ws_thread', None) is None:
            return
        if not self.state.gen['down'].is_set() and ws.is_alive():
            return
        now = self.executor.now()
        if now - self.state.last_reconnect < 10:
            return
        self.state.last_reconnect = now
        try:
            live = self.live_outcome_ids()
            subscribe_ids = (self.state.outcome_ids if live is None
                             else [o for o in self.state.outcome_ids if o in live])
            self.state.begin_stop()
            ws.stop()
            from hyperliquid.websocket_manager import WebsocketManager
            fresh = WebsocketManager('https://api.hyperliquid.xyz')
            self.state.bind(fresh)
            failed = []
            for oid in subscribe_ids:
                for side in (0, 1):
                    try:
                        fresh.subscribe({'type': 'l2Book', 'coin': f'#{oid*10+side}'},
                                        self.state.handle_book)
                    except Exception as sub_exc:
                        failed.append(f'#{oid*10+side}: {type(sub_exc).__name__}')
            if failed:
                self.executor.state['ws_subscribe_failed'] = failed[:20]
            fresh.subscribe({'type': 'userFills', 'user': self.owner}, self.state.handle_fills)
            self.ws = fresh
            self.ws_thread = fresh
            fresh.start()
        except BudgetUnavailable:
            raise
        except Exception as exc:
            self.state.gen['down'].set()
            self.executor.state['ws_error'] = str(exc)
            # REST remains authoritative and continues reconciling exposure.

    def run_forever(self):
        while not self.stop_event.is_set():
            try:
                self.tick()
            except BudgetUnavailable:
                raise
            except Exception as exc:
                # 2026-11-01 halt 重构：L1。一次异常不该把整台机器停掉。
                # 实测：看板写入异常也会走到这里，导致正在等配对的仓被撤单。
                block_open(self.executor, '主循环异常: '+str(exc), source='loop_error')
                self.executor.state_save()
                from executor_v2 import log
                # 2026-11-08 诊断：原来只 log(halt_reason)，而它是空串，
                # 日志里只剩一条空行，异常类型与 traceback 全丢。
                import traceback as _tb
                log('[主循环异常] ' + type(exc).__name__ + ': ' + str(exc))
                log(_tb.format_exc())
            self.stop_event.wait(1.0)
