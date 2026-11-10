#!/usr/bin/env python3
"""HIP4 v2 本地执行器。独立候选授权、持久首次激活、真实资金预算。

安全调度由 v2_safety.RuntimeLoop 执行：每轮REST订单/余额、实验成交补采、
保守退出估值、到账奖励检查点、暂停及残留管理。WS线程仅入队。
本金120、在线占款80、缓冲40；每市场真实资金12，stop4；净亏10提前暂停，
12硬约束，观察期不豁免。滑点/跳空可能突破12，不能保证最大实亏。
--dry-run离线；--preflight-readonly只读且不读keys；--live须先人工激活。
"""
import argparse
import queue
from v2_safety import RuntimeLoop
from v2_protocol import (amount_wire, price_wire, minimum_order, WeightBudget,
                         BudgetedInfo, BudgetUnavailable, DISCOVERY_RESERVE)
import json
import math
import sys
import threading
import time
import urllib.request
from decimal import Decimal
from pathlib import Path

from ledger import Ledger, ZERO, dec, LIVE_GATE_REASON

BASE = Path(__file__).resolve().parent
STATE_FILE = BASE / "executor_v2_state.json"
INFO_URL = "https://api.hyperliquid.xyz/info"
KEY_FILE = BASE / "keys" / "agent.json"        # 与旧 executor 同一份私钥
LEDGER_DB = BASE / "ledger_events.sqlite3"     # live 账本（userFills 唯一入账口）
REWARD_API = "https://pd-liquidity-rewards-payouts.outcome-e91.workers.dev"
REWARD_STATE_FILE = BASE / "reward_watcher_state.json"

# ---- 常量（方案文档第一节，用户 2026-10-27 拍板）----
MERGE_FEE_PER_PAIR = 0.001344          # merge 13.44bps × 2 腿 × $0.5 面值
TAKER_FEE_PER_SHARE = 0.0              # Observed Outcome buy (including taker) fee; ledger records actual fee
QUOTE_MIN_NOTIONAL = 50.0              # 附录 A 约束 3：双边合计名义
CAPITAL_MIN_PER_MARKET = 10.0
CAPITAL_MAX_PER_MARKET = 13.0
MAX_ACTIVE_NOTIONAL = 80.0             # 同时在线做市名义上限
# unwinding 重试上限：连续这么多次仍清不干净 → alert（继续重试只会掩盖故障，
# 且残留持仓可能裸奔到结算，实测可达 $20，远超 $4 止损上限）
UNWIND_MAX_ATTEMPTS = 5
STOP_LOSS_MAX_USD = 4.0                # 每市场止损上限（决策 6）
# 安全倍硬门槛（决策 6）。
# 2026-10-31 用户拍板从 2.0 放宽到 0.7：
#   实测 7 个 A 档市场（全 NBA）没有任何一个能过 2.0——最差单步 2.1~5.8¢ 对 2¢ 计分带，
#   比例 0.34~0.95。2.0 等于把整个 NBA 品类排除，只剩昨天 LoL 那两个偶然样本。
#   0.7 放出 3 个（0.95 / 0.73 / 0.72），仍排除 0.59 以下（止损几乎必被打穿的那批）。
# 门槛放宽的是「入场筛选」，不改变止损额（$4/市场）与净亏上限（本金 10%）。
SAFETY_MULT_MIN = 0.7
FUSE_NET_LIMIT = -10.0                 # 熔断线（〇.1）
FUSE_OBSERVATION_PERIODS = 2           # 仅收益评价观察，不绕过硬风控
BID_CACHE_TTL = 1.5
CHECK_THROTTLE_S = 1.0
SELL_SLIP = 0.002                      # 卖单挂低价保证成交（旧 executor 实测值）
HEDGE_SLIP = 1.002                     # 对冲买单挂高价保证成交（旧 executor 实测值）

# ---------------- 交易所账户常量（沿用旧 executor 的已验证值）----------------
# OWNER来自独立实验配置，agent钱包仅签名；builder fee固定为0。
BUILDER = "REDACTED_ACCOUNT_ADDRESS"

# ---------------- reward 轮询（任务 C）----------------
REWARD_POLL_S = 600.0                  # 默认 10 分钟
REWARD_HTTP_ATTEMPTS = 3               # 失败不重试超过 3 次（不阻塞主循环）
REWARD_HTTP_TIMEOUT = 15.0

BJT = None  # 占位：日志时间戳用本地时间即可，不引入额外依赖


def log(msg):
    line = f"[{time.strftime('%Y-%m-%d %H:%M:%S')}] {msg}"
    print(line, flush=True)


# ---------------- 纯决策函数（无 IO，全部可测）----------------

def parse_time(value):
    """与 edge_scan.parse_time 同口径。"""
    from datetime import datetime, timezone
    if value is None:
        return None
    if isinstance(value, (int, float)):
        return float(value) / (1000 if value > 1e11 else 1)
    dt = datetime.fromisoformat(str(value).replace("Z", "+00:00"))
    if dt.tzinfo is None:
        raise ValueError("时间缺少时区")
    return dt.timestamp()


def settlement_time(market, meta):
    """决策 3 fail-closed：只认明确结算字段；三个时间字段不得互代。

    与 edge_scan.settlement_time 同逻辑（复制而非 import，保持 v2 自包含且
    不拉起 scanner 的网络副作用）。返回 (epoch_seconds|None, source)。
    """
    for source, obj in (("market", market or {}), ("outcomeMeta", meta or {})):
        for field in ("settlement_time", "settlement_at", "resolution_time"):
            if obj.get(field):
                return parse_time(obj[field]), f"{source}.{field}"
    if (meta or {}).get("name") == "template:binaryPrice":
        parts = dict(p.split(":", 1) for p in (meta.get("description") or "").split("|") if ":" in p)
        if parts.get("time"):
            from datetime import datetime, timezone
            dt = datetime.strptime(parts["time"], "%Y%m%d-%H%M").replace(tzinfo=timezone.utc)
            return dt.timestamp(), "outcomeMeta.description.time (binaryPrice观察到期；非最终到账保证)"
    return None, "unknown：无明确结算时间；incentive_end_time/epoch_end_date/scheduledStart/resolutionDeadline均未代用"


# 2026-10-30：补 sportsTotal / sportsSpread。
# 这两个模板的 description 里**确实带 scheduledStart**（实测
# template:sportsTotal → scheduledStart:20261101-2125；template:sportsSpread →
# scheduledStart:20261030-0015），此前不在列表里 → sports_schedule() 返回 None
# → 被当成「无时间锚」判进 B 档，28 个本可做的市场被白白排除。
# 另注：sportsContestParticipant2 / sportsTournamentParticipant 的 description
# 只有 `participant:xxx`，没有时间字段，即使列在这里也会因缺字段返回 None（正确行为）。
SPORTS_TEMPLATES = ('sportsContestWinner', 'sportsContestDraw2',
                    'sportsContestParticipant2', 'sportsTournamentParticipant',
                    'sportsTotal', 'sportsSpread')


def sports_schedule(meta):
    '从 sports 模板解析 scheduledStart 和 resolutionDeadline。\n\n字段格式为 YYYYMMDD-HHMM，按 UTC 解读。返回的 deadline\n表示清仓截止而非结算时间，不能据此判断结果已经产生。'
    name = str((meta or {}).get('name') or '')
    if not any(t in name for t in SPORTS_TEMPLATES):
        return None
    parts = dict(p.split(':', 1) for p in ((meta or {}).get('description') or '').split('|')
                 if ':' in p)
    out = {}
    for field in ('scheduledStart', 'resolutionDeadline'):
        raw = parts.get(field)
        if not raw:
            return None
        try:
            from datetime import datetime, timezone
            dt = datetime.strptime(raw, '%Y%m%d-%H%M').replace(tzinfo=timezone.utc)
        except ValueError:
            return None
        out[field] = dt.timestamp()
    return out


def clearing_deadline(market, meta, cfg):
    '清仓截止时间（epoch 秒）。**这是风控动作点，不是结算时间。**\n\n    用户 历史版本 拍板 B 方案（体育盘）：\n      1. 开赛前双边都持仓  -> 持有到比赛结束（不加仓、不撤，靠结果对冲归零）\n      2. 开赛前 1h 仍无双边 -> 直接清仓，不留到开赛\n\n    因此清仓截止 = 开赛前 `pre_game_clear_seconds`（默认 3600s）。\n    非体育盘或时间字段缺失返回 None（调用方 fail-closed 拒绝）。\n    '
    sched = sports_schedule(meta)
    if not sched:
        return None
    lead = float(cfg.get('pre_game_clear_seconds', 3600))
    return sched['scheduledStart'] - lead


def hold_through_result_allowed(market, meta, cfg):
    """体育盘「持有到比赛结束」是否成立：必须有可解析的开赛时间且已经过开赛点。"""
    sched = sports_schedule(meta)
    if not sched:
        return False
    return bool(cfg.get('hold_through_result_when_paired', True))


def pair_notional(bids, shares):
    """双边合计名义（附录 A 约束 3：$50 门槛按此判断，不是每边）。"""
    return shares * (bids[0] + bids[1])


def quote_mode_of(cfg):
    '读取 quote_mode 配置（附录 B 决策 历史版本）。\n\n    off（默认）= 路线1：放弃 quote 分、只赚 maker/taker fill（60% 池），\n                $50 门槛的【资金门槛】跳过，$12/市场合法开仓。\n    on         = 路线2：吃 quote 池（40%），需过 $50 双边合计门槛（~$52/市场）。\n    返回规范化值 "off"/"on"；非法值返回 None（fail-closed，由调用方拒绝）。\n    '
    mode = cfg.get("quote_mode", "off")
    if mode in ("off", "on"):
        return mode
    return None


def shares_for_open(bids, capital, quote_mode="off"):
    if quote_mode not in ("off", "on"):
        return None, "quote_mode非法"
    try:
        prices = [dec(b) for b in bids]
        cap = dec(capital)
        if len(prices) != 2 or any(b <= 0 or b >= 1 for b in prices) or cap <= 0:
            return None, "双边价格/资金非法"
        price = sum(prices)
        shares = int(cap // price) if quote_mode == 'off' else math.ceil(dec(50)/price)
        cost = shares*price
        if shares <= 0 or cost > cap:
            return None, f"名义{cost}超出真实资金{cap}或不足1份；禁止放大仓位"
        return shares, f"{shares}整数份，双腿实际占款${cost}≤${cap}（{quote_mode}）"
    except (TypeError, ValueError, ArithmeticError):
        return None, '价格/资金未知'


def merge_net_edge(bids):
    """merge 净边际 = 配对边际 − 0.001344/对（第一节公式）。"""
    return (1.0 - bids[0] - bids[1]) - MERGE_FEE_PER_PAIR


def hedge_decision(held_entry, held_bid, other_ask, stop_px):
    """单边对冲比较（决策 1）：补齐成本 < 等待损失 才允许 taker。

    补齐后 merge 的净回收（每份）= 1 − held_entry − other_ask − merge费 − taker费
    等待的期望损失（每份）= held_entry − stop_px（止损路径的实现亏损）
    只有补齐净回收 > 等待损失时才对冲。返回 (hedge: bool, reason: str)。
    """
    if other_ask is None or held_bid is None:
        return False, "盘口缺失，不对冲"
    complete_net = 1.0 - held_entry - other_ask - MERGE_FEE_PER_PAIR - TAKER_FEE_PER_SHARE
    wait_loss = held_entry - stop_px
    if complete_net > wait_loss:
        return True, (f"补齐净回收 {complete_net:.5f} > 等待损失 {wait_loss:.5f}")
    return False, (f"补齐净回收 {complete_net:.5f} ≤ 等待损失 {wait_loss:.5f}，等待/止损")


def exit_decision(merge_edge, pair_edge, settlement_fee, settle_time_known):
    """退出不预设（决策 2）。结算费未知 → fail-closed 只做 merge 模式。

    merge 净边际 = pair_edge − 0.001344；结算净 = pair_edge − settlement_fee。
    返回 dict(mode=..., reason=...)。mode ∈ {'merge', 'hold', 'merge_only'}
    """
    if not settle_time_known:
        return {"mode": "merge_only",
                "reason": "结算时间未知 → fail-closed，不做持有模式"}
    if settlement_fee is None:
        return {"mode": "merge_only",
                "reason": "结算费未实测 → fail-closed，不做持有模式"}
    hold_net = pair_edge - settlement_fee
    if merge_edge > hold_net:
        return {"mode": "merge", "reason": f"merge 净边际 {merge_edge:.5f} > 结算净 {hold_net:.5f}"}
    return {"mode": "hold", "reason": f"结算净 {hold_net:.5f} ≥ merge 净边际 {merge_edge:.5f}"}


def fuse_check(cum_net, completed_periods, hard_limit=12.0, early_limit=10.0):
    '按调用方传入的阈值进行熔断判定。'
    if cum_net is None or not math.isfinite(float(cum_net)):
        return True, '净额未知，暂停新仓'
    if cum_net <= -float(hard_limit):
        return True, f'净亏达到{float(hard_limit):.2f}硬约束，收尾；滑点/跳空仍可能越界'
    if cum_net <= -float(early_limit):
        return True, f'净亏达到{float(early_limit):.2f}提前暂停，观察期不豁免硬风控'
    return False, '净额在提前暂停线内；观察期仅放宽收益评价'


def safety_mult_ok(band_width_cents, worst_step_cents):
    """安全倍 = 挂距 ÷ 历史最差单步，≥2 才能入选（决策 6，硬门槛）。"""
    if worst_step_cents is None or worst_step_cents <= 0:
        return False, "历史最差单步未知 → 安全倍不可证，拒绝"
    if band_width_cents is None or band_width_cents <= 0:
        return False, "带宽未知 → 安全倍不可证，拒绝"
    ratio = band_width_cents / worst_step_cents
    if ratio < SAFETY_MULT_MIN:
        return False, f"安全倍 {ratio:.2f} < {SAFETY_MULT_MIN}"
    return True, f"安全倍 {ratio:.2f} ≥ {SAFETY_MULT_MIN}"


def active_notional(state):
    if not state.get('snapshot_known') or state.get('reserved_total') is None:
        return float('inf')
    return float(state['reserved_total'])


def can_open_market(cand, state, cfg):
    from v2_safety import candidate_reason
    if not state.get('activation_valid') or not state.get('snapshot_known') or not state.get('ledger_known'):
        return False, '首次激活/实时快照/成本覆盖未知'
    if state.get('halted'):
        return False, '全局暂停'
    reason = candidate_reason(cand, time.time(), cfg)
    if reason:
        return False, reason
    shares, reason = shares_for_open(cand.get('bids', []), cfg['capital_per_market'], quote_mode_of(cfg))
    if shares is None:
        return False, reason
    if active_notional(state) + pair_notional(cand['bids'], shares) > 80:
        return False, '同时在线占款超过80'
    return True, reason


def atomic_place_pair(adapter, oid, bids, shares, state):
    # Standalone callers cannot create unjournaled live orders.
    raise LiveAdapterError('必须通过ExecutorV2持久化意图及远程确认后提交配对')


# ---------------- 记账桥（复用 ledger.py 哲学）----------------

class Accounting:
    """只有真实成交（userFills）才进 ledger；动作回执永远不进。
    dry 模式下一切写入被跳过。

    ledger 为 None 时（dry 装配）所有读都是空集，写全部 no-op——绝不静默降级成
    「没有账本但看起来在记账」：`cum_net` 会因此恒为 0，`period_net_since` 会
    返回 known=False 的 0 并标注没有账本。"""

    def __init__(self, ledger, owner, dry):
        self.ledger = ledger
        self.owner = owner
        self.dry = dry

    def ingest_fills(self, fills, started_ms=None, *, coverage_interval=None, coverage_source=None):
        if self.dry or self.ledger is None:
            return 0
        # Runtime owns experiment/order attribution and REST overlap, never
        # filters at process start (which loses fills across a restart).
        real = [f for f in fills if str(f.get('coin', '')).startswith(('#', '+'))]
        return (self.ledger.ingest_fills(real, source_owner=self.owner,
                                         coverage_interval=coverage_interval,
                                         coverage_source=coverage_source)
                if real or coverage_interval is not None else 0)

    def record_action(self, response):
        """动作回执（下单/撤单/merge 的 API 应答）不是成交证据，永不入账。"""
        return 0

    # ---- 当期已实现净损益（熔断的输入；决策 4）----
    def period_net_since(self, since_ms, until_ms=None):
        """[since_ms, until_ms] 内的已实现净损益（含费），按 realization 的 time 切片。

        口径说明（**不可当成认证审计值**）：
        - ledger.report() 不给 opening 库存与完整覆盖证据时，`realized_net` 是 None
          且 status='unreconciled'（方案文档第六节第 4 条：期初库存缺失 → 报
          unreconciled，禁止用挂单 entry 补数据）。所以这里**不用** `realized_net`，
          而是把 report 的逐笔 `realizations[].net` 按时间窗累加。
        - 结果是一个**观测小计**：只覆盖账本里已经存在的 userFills，不证明覆盖完整。
          因此返回 dict 带 `confidence` 与 `issues`，调用方（熔断）按标注使用。
        - 单笔 `net` 为 None（成本未知/被污染）的事件计入 `unknown_events`，不猜、不补 0，
          此时 known=False。
        - 返回 Decimal 就放在 `net` 键里；`net_float` 只是方便落 JSON 状态。
        """
        until_ms = int(time.time() * 1000) if until_ms is None else int(until_ms)
        since_ms = int(since_ms)
        if until_ms < since_ms:
            raise ValueError("period window end precedes start")
        out = {"since_ms": since_ms, "until_ms": until_ms, "net": ZERO,
               "known": True, "events": 0, "unknown_events": 0, "confidence": "",
               "label": "period_realized_net_subtotal_observed",
               "source": "ledger.report().realizations", "issues": []}
        if self.ledger is None:
            out["known"] = False
            out["confidence"] = "unavailable"
            out["issues"] = ["no ledger instance"]
            out["net_float"] = 0.0
            return out
        try:
            rep = self.ledger.report()
        except Exception as exc:                     # 账本读失败 → 明确标注不可用
            out["known"] = False
            out["confidence"] = "unavailable"
            out["issues"] = [f"report failed: {type(exc).__name__}: {exc}"]
            out["net_float"] = 0.0
            return out
        total = ZERO
        in_window = []
        for g in rep.get("realizations") or []:
            t = int(g.get("time") or 0)
            # ⚠️ 左闭右开：`since_ms <= t < until_ms`。
            # 旧写法用双闭区间（<=），相邻两期会在边界事件上重复计数
            # （实测：3 期各亏 $5，第 2/3 期被算成 -$10，cum_net 翻倍）。
            # 期边界的语义是「上一期结束的那一刻归上一期」，下一期从它之后开始。
            if not since_ms <= t < until_ms:
                continue
            in_window.append(g)
            if g.get("net") is None:
                out["unknown_events"] += 1
                continue
            total += dec(g["net"])
        out["net"] = total
        out["net_float"] = float(total)
        out["events"] = len(in_window)
        rep_issues = list(rep.get("issues") or [])
        out["issues"] = rep_issues
        if out["unknown_events"]:
            out["known"] = False
            out["confidence"] = "provisional"
            out["label"] = "period_realized_net_subtotal_observed_partial"
        elif rep.get("status") == "reconciled" and in_window:
            out["confidence"] = "reconciled"
        elif rep.get("status") == "reconciled":
            # 账本整体对平、但该窗口没有任何 realization → 净额确实是 0
            out["confidence"] = "reconciled_empty_window"
        else:
            # 账本不对平（缺期初库存/覆盖证据/startPosition 不一致等）：
            # 数值只是一个切片小计，**不是**认证值。
            out["known"] = False
            out["confidence"] = "provisional"
            out["label"] = "period_realized_net_subtotal_observed_not_audited"
        return out

    def aux_events(self):
        """账本里已入账的 reward/transfer 证据（只读；不做去重决策）。"""
        if self.ledger is None:
            return []
        try:
            rep = self.ledger.report()
        except Exception as exc:
            log(f"  读账本 aux 失败: {type(exc).__name__}: {exc}")
            return []
        return list(rep.get("rewards") or []) + list(rep.get("transfers") or [])


# ---------------- 交易所 IO 适配层（任务 A）----------------

class LiveAdapterError(RuntimeError):
    """交易所 IO 装配/调用失败。带着上下文抛出，绝不静默返回假成功。"""


def _is_market_coin(coin, oid):
    """coin 是否属于该市场。必须按数字解码判断，不能用前缀：
    `"#173470".startswith("#17347")` 会误吃 #1734700（另一个市场）。"""
    coin = str(coin or "")
    if not coin.startswith("#") or not coin[1:].isdigit():
        return False
    return int(coin[1:]) // 10 == int(oid)


class LiveAdapter:
    """ExecutorV2 需要的全部交易所 IO；全部走真实 REST，回执一律不入账。

    记账纪律（与 ledger.py 一致）：本类的每个方法都**只返回执行结果**，
    绝不调用 ledger.ingest_fills / record_action。真实成交只从 WS userFills
    进来（LiveState → Accounting.ingest_fills），动作回执永远不是成交证据。

    best_bid 必带 1.5s 缓存（旧 executor bug 11 的教训）：N 个市场每轮要打
    2×N 次 REST，不缓存会吃掉限速配额；止损复核用 force=True 绕过。
    """

    def __init__(self, exchange, outcome_ids, info_fn=None, cache_ttl=None,
                 now=None, log_fn=None):
        self.ex = exchange
        self.outcome_ids = [int(o) for o in outcome_ids]
        self.info = info_fn or hl_info
        self.cache_ttl = BID_CACHE_TTL if cache_ttl is None else float(cache_ttl)
        self.now = now or time.time
        self.log = log_fn or log
        self._bid_cache = {}        # {coin: (px, ts)}
        self.cache_hits = 0
        self.cache_misses = 0
        self._books = {}
        self.params_registered = False
        # 2026-11-02 L1：openOrders 统一入口缓存。
        # 根因：cancel_all 每次发 2 次 openOrders（查 + 复核），openOrders
        # 权重固定 20（官方文档确认它不在 weight-2 名单），主循环 1 秒一轮
        # → 有持仓期需求达 7200 权重/分，而上限仅 1200 → 必然 BudgetUnavailable。
        # 这里把「同一份全量挂单」在多调用点间复用，只省重复查询，
        # 绝不影响「撤单对象必须精确」这条安全底线（复核强制 force=False 走实时）。
        self._cancel_verified = {}
        self._cancel_unconfirmed = set()
        self._oo_generation = 0
        self._oo_cache = None          # {'at': float, 'orders': list}
        self._oo_cache_seconds = 0.0   # 由 build_live 按 cfg 注入，0=关闭
        self._oo_last_submit_at = 0.0  # 最近一次挂单时刻（用于挂单后冷却）
        self.register_outcome_params()

    # ---- coin 参数注册（旧 make_exchange 同款：HIP-4 outcome coin 不在默认表里）----
    def register_outcome_params(self):
        # SDK 0.24 mapping must be checked by readonly preflight. Do not invent
        # asset ids or precision from old scans. build_live supplies evidence.
        return 0

    def update_outcome_ids(self, outcome_ids):
        """新增市场后补注册（幂等）。"""
        added = [int(o) for o in outcome_ids if int(o) not in self.outcome_ids]
        if not added:
            return 0
        self.outcome_ids.extend(added)
        return self.register_outcome_params()

    # ---- 盘口 ----
    def invalidate(self, coin=None):
        """盘口缓存失效（撤单/下单后调用，避免用旧价判断止损）。"""
        if coin is None:
            self._bid_cache.clear()
            self._books.clear()
        else:
            self._bid_cache.pop(coin, None)
            self._books.pop(coin, None)

    def _book(self, coin, force=False):
        cached = self._books.get(coin)
        if (not force and cached and 0 <= self.now()-cached[1] <= self.cache_ttl
                and 0 <= self.now()-float(cached[0].get('time', 0))/1000 <= 5):
            return cached[0]
        d = self.info({"type": "l2Book", "coin": coin})
        if not isinstance(d, dict) or d.get("__error__"):
            return None
        if d.get('time') is None or abs(self.now()-float(d['time'])/1000) > 5:
            return None
        self._books[coin] = (d, self.now())
        return d

    def best_bid(self, coin, force=False):
        """best bid。1.5s 缓存；force=True 强制刷新（止损/清算复核用）。
        市场下架/网络失败返回 None，绝不抛异常、绝不返回陈旧缓存当作实时价。"""
        now = self.now()
        if not force:
            hit = self._bid_cache.get(coin)
            if hit and now - hit[1] < self.cache_ttl:
                self.cache_hits += 1
                return hit[0]
        self.cache_misses += 1
        try:
            d = self._book(coin, force=force)
            if d is None:
                return None
            bids = (d.get("levels") or [[], []])[0]
            px = float(bids[0]["px"]) if bids else None
            if px is not None:
                self._bid_cache[coin] = (px, now)
            return px
        except BudgetUnavailable:
            raise
        except Exception as exc:
            self.log(f"  best_bid({coin}) 失败: {type(exc).__name__}: {exc}")
            return None

    def best_ask(self, coin):
        """best ask。不带缓存：对冲决策必须吃实时卖盘。"""
        try:
            d = self._book(coin, force=True)
            if d is None:
                return None
            asks = (d.get("levels") or [[], []])[1]
            return float(asks[0]["px"]) if asks else None
        except BudgetUnavailable:
            raise
        except Exception as exc:
            self.log(f"  best_ask({coin}) 失败: {type(exc).__name__}: {exc}")
            return None

    # ---- 订单 ----
    @staticmethod
    def _status_of(res):
        """取 order 应答里的第一条 status（resting/filled/error）。"""
        try:
            return (res.get("response") or {}).get("data", {}).get("statuses", [{}])[0] or {}
        except (AttributeError, IndexError, TypeError):
            return {}

    def place_limit(self, coin, is_buy, sz, px, tif, client_id=None):
        if tif not in ('Alo', 'Ioc', 'Gtc') or client_id is None:
            raise LiveAdapterError('非法tif或缺持久clientorderid')
        px = price_wire(px, buy=bool(is_buy), tif=tif)
        if dec(sz) <= 0 or dec(sz) != dec(sz).to_integral_value():
            raise LiveAdapterError('订单须为正整数份数')
        # Acquisition keeps the $1 protocol/client floor. Position-closing sells
        # may be below $1 (documented Outcome SDK close-flow exception); rejecting
        # them locally would turn a known tiny residual into an unsent unknown intent.
        if is_buy and dec(sz)*dec(px) < 1:
            raise LiveAdapterError('开仓实际单腿名义至少1美元')
        from hyperliquid.utils.types import Cloid
        try:
            if hasattr(self.info, 'budget'):
                self.info.budget.charge(1, essential=not is_buy, kind='order')
            self.note_submit()
            managed = getattr(self, 'managed_executor', None)
            if is_buy and managed is not None:
                from v2_safety import authorization_expired
                if authorization_expired(managed):
                    return {'rejected': True, 'sent': False, 'reason': 'authorization_expired'}
            res = self.ex.order(name=coin, is_buy=bool(is_buy), sz=float(sz),
                                limit_px=float(px), order_type={'limit': {'tif': tif}},
                                reduce_only=False, cloid=Cloid.from_str(client_id),
                                builder={'b': BUILDER, 'f': 0})
        except BudgetUnavailable:
            raise
        except Exception as exc:
            return {'unknown': True, 'error': type(exc).__name__}
        st = self._status_of(res)
        if 'resting' in st:
            return {'oid': st['resting']['oid']}
        if 'filled' in st:
            return {'oid': st['filled'].get('oid'), 'filled': True}
        if 'error' in st:
            return {'rejected': True, 'reason': st['error']}
        return {'unknown': True}

    def cancel(self, coin, oid):
        if oid is None:
            return False
        try:
            if hasattr(self.info, 'budget'):
                self.info.budget.charge(1, essential=True, kind='cancel')
            self.invalidate_open_orders_cache()
            res = self.ex.cancel(coin, oid)
        except BudgetUnavailable:
            raise
        except Exception as exc:
            self.log(f"  ⚠️ cancel {coin} {oid} 异常: {type(exc).__name__}: {exc}")
            return False
        self.invalidate(coin)
        return str(res.get("status", "")).lower() == "ok" if isinstance(res, dict) else False

    # 2026-11-02 L1：全进程唯一的 openOrders 获取点。
    #
    # 背景（实测）：openOrders 单次 20 权重，是全部 REST 消耗的 83%
    # （37 分钟 914 次 / 18280 权重）。5 个独立调用点各自查，同一份数据
    # （账户全量挂单）一分钟被查几十次。
    #
    # 语义约定（必须严格遵守，否则会有资金风险）：
    #   use_cache=True  → 允许复用 oo_cache_seconds 内的结果（省请求）
    #   use_cache=False → 强制真实请求（撤单复核专用，绝不能读旧数据）
    #
    # 挂单后冷却：submit 成功后 note_submit() 记录时刻，冷却期内
    # 缓存可能不含新单，调用方可自行判断是否该跳过缓存。
    def get_open_orders(self, use_cache=True):
        now = self.now()
        c = self._oo_cache
        if (use_cache and c is not None and self._oo_cache_seconds > 0
                and 0 <= now - c['at'] < self._oo_cache_seconds):
            return c['orders']
        orders = self.info({"type": "openOrders", "user": self._owner_addr()})
        if not isinstance(orders, list) or any(not isinstance(o, dict)
                or 'coin' not in o or 'oid' not in o for o in orders):
            raise LiveAdapterError('openOrders malformed; cannot confirm cancellation')
        if c is not None and c['orders'] != orders:
            self._oo_generation += 1
            self._cancel_verified.clear()
        # A forced read is also useful to later consumers; never cache failures.
        self._oo_cache = {'at': now, 'orders': orders}
        return orders

    def invalidate_open_orders_cache(self):
        self._oo_cache = None
        self._oo_generation += 1
        self._cancel_verified.clear()
        managed = getattr(self, 'managed_executor', None)
        if managed is not None:
            managed.state['snapshot_dirty'] = True

    def note_submit(self):
        self._oo_last_submit_at = self.now()
        self.invalidate_open_orders_cache()

    def cache_ready(self, cooldown=0.0):
        return (self._oo_cache is not None and self._oo_cache_seconds > 0
                and self.now() - self._oo_last_submit_at >= cooldown
                and 0 <= self.now() - self._oo_cache['at'] < self._oo_cache_seconds)

    def cancel_all(self, oid, keep_side=None):
        """Cancel, then verify live. Reuse bounded evidence until an IO event invalidates it."""
        oid = int(oid)
        key = (oid, None if keep_side is None else int(keep_side))
        now = self.now()
        self._cancel_unconfirmed.add(key)
        ready = getattr(self, '_cancel_retry', {}).get(key, 0)
        if now < ready:
            raise BudgetUnavailable('撤单复核等待调度', retry_at=ready)
        confirmed = self._cancel_verified.get(key)
        if confirmed is not None and 0 <= now - confirmed < 15:
            self._cancel_unconfirmed.discard(key)
            return True
        budget = getattr(self.info, 'budget', None)
        from contextlib import nullcontext
        try:
            with budget.priority() if budget is not None else nullcontext():
                # 2026-11-02 修复（浮点相等恒假 → 查询阶段每 tick 真实请求 openOrders，
                # halt 时打满 96% 预算并自锁）：查询阶段交给 get_open_orders 按
                # _oo_cache_seconds（3 秒 TTL）判断即可，陈旧数据可容忍；复核阶段
                # 仍然 use_cache=False 强制实时，漏撤一定能被发现。
                oo = self.get_open_orders(use_cache=True)
                mine = [o for o in oo if _is_market_coin(o.get('coin'), oid)]
                managed = getattr(self, 'managed_executor', None)
                foreign = []
                if managed is not None:
                    allowed = set(managed.state.get('submitted_oids', []))
                    foreign = [o for o in mine if str(o['oid']) not in allowed]
                    mine = [o for o in mine if str(o['oid']) in allowed]
                    if foreign:
                        managed.state.update(halted=True, ownership_unknown=True,
                                             halt_reason='未知/其他策略挂单，禁止混合管理')
                if keep_side is not None:
                    mine = [o for o in mine if o['coin'] != f'#{oid*10+int(keep_side)}']
                if mine and budget is not None:
                    # Keep room for the live verification before sending any cancel.
                    at = budget.ready_at(len(mine) + 20, essential=True)
                    # 使用当前时间，避免用 HTTP 请求前的旧时间比较。
                    if at > self.now():
                        raise BudgetUnavailable(retry_at=at)
                for o in mine:
                    self.cancel(o['coin'], o['oid'])
                # A no-op is confirmed by the read itself. Actual cancels always force IO.
                oo2 = self.get_open_orders(use_cache=False) if mine else oo
                left = [o for o in oo2 if _is_market_coin(o.get('coin'), oid)
                        and (keep_side is None or o['coin'] != f'#{oid*10+int(keep_side)}')]
        except BudgetUnavailable as exc:
            self._cancel_retry = getattr(self, '_cancel_retry', {})
            self._cancel_retry[key] = exc.retry_at or now + 1
            raise
        except Exception as exc:
            self._oo_fails = getattr(self, '_oo_fails', 0) + 1
            self._oo_backoff_until = now + min(120, 10 * 2**min(self._oo_fails-1, 4))
            self._cancel_retry = getattr(self, '_cancel_retry', {})
            self._cancel_retry[key] = self._oo_backoff_until
            self.log(f'撤单查询失败: {type(exc).__name__}: {exc}')
            return False
        self._oo_fails = 0
        self._oo_backoff_until = 0
        getattr(self, '_cancel_retry', {}).pop(key, None)
        if not left and not foreign:
            self._cancel_verified[key] = self._oo_cache['at']
            self._cancel_unconfirmed = {
                k for k in self._cancel_unconfirmed
                if k[0] != oid or (keep_side is not None and k != key)
            }
            return True
        return False

    def _owner_addr(self):
        owner = getattr(self.ex, "account_address", None)
        if not owner:
            raise LiveAdapterError("Exchange.account_address 缺失，无法查询账户挂单")
        return owner

    # ---- merge（走 sign_l1_action + _post_action，amount 必须是字符串）----
    def merge(self, oid, amount):
        """merge 双边库存。**amount 必须传字符串**：传 float 会被 HL 拒绝
        （422 Failed to deserialize，旧版实测注释）。返回 True 只代表交易所
        接受了这个动作，不代表成交——merge 的损益只认真实 userFills。"""
        action = {"type": "userOutcome",
                  "mergeOutcome": {"outcome": int(oid), "amount": amount_wire(amount)}}
        try:
            from hyperliquid.utils import constants
            from hyperliquid.utils.signing import sign_l1_action, get_timestamp_ms

            if hasattr(self.info, 'budget'):
                self.info.budget.charge(1, essential=True, kind='merge')
            nonce = get_timestamp_ms()
            sig = sign_l1_action(self.ex.wallet, action, self.ex.vault_address, nonce,
                                 self.ex.expires_after,
                                 self.ex.base_url == constants.MAINNET_API_URL)
            res = self.ex._post_action(action, sig, nonce)
        except BudgetUnavailable:
            raise
        except Exception as exc:
            self.log(f"  ⚠️ merge O{oid} 异常: {type(exc).__name__}: {exc}")
            return None  # possibly sent; keep pending until remote evidence resolves it
        # 2026-11-02 修复（default 回执被误判成失败 → 4 次真实 merge 全走 ack=False）：
        # 交易所对 userOutcome/mergeOutcome 返回 `{"status":"ok","response":{"type":"default"}}`。
        # 该形态在官方 Exchange Endpoint 文档里出现在**成功响应示例区**（与
        # usdClassTransfer / sendAsset / vaultTransfer 并列），但**不携带任何执行
        # 细节**（无 statuses / oid / error）。旧判定只认 statuses == ["success"]，
        # 于是 default → statuses=None → ok=False → 打「被拒」。
        # 实测 4 次 merge 全部链上成功（4 个独立 tx hash、8 笔 Merge Outcome 成交，
        # 提交→成交 0.75~1.53 秒），但 events.jsonl 里 merge-受理=0、merge-假拒实成功=0，
        # 即 4 次全部走了 ack=False 分支。
        # 现在把 default 当作「已受理（在途）」：status==ok 说明交易所收下了这个动作，
        # 只是不给细节；成不成交仍然只认真实 userFills 与持仓减少（记账纪律不变）。
        response = res.get("response") if isinstance(res, dict) else None
        statuses = (response or {}).get("data", {}).get("statuses") if isinstance(response, dict) else None
        default_ack = bool(isinstance(response, dict) and response.get("type") == "default")
        ok = bool(isinstance(res, dict) and res.get("status") == "ok"
                  and (statuses == ["success"] or default_ack))
        if not ok:
            self.log(f"  ⚠️ merge O{oid} 被拒: {json.dumps(res, ensure_ascii=False)[:200] if res else 'None'}")
        elif default_ack and statuses != ["success"]:
            self.log(f"  merge O{oid} 已受理（回执 default 无细节，按在途处理）")
        return ok

    # ---- 主动卖出 / 对冲（taker）----
    def sell_taker(self, oid, side, shares, bid):
        raise LiveAdapterError('卖出必须通过持久化IOC意图及远程确认路径')

    def hedge_taker(self, oid, side, shares, max_px=None):
        '返回对侧 taker 补齐的建议限价。\n\n提交必须由安全层通过持久化 journal 意图完成，包含 write-ahead、\ncloid 和远程对账；此方法不直接下单。'
        coin = f'#{int(oid)*10+int(side)}'
        book = self._book(coin, force=True)
        if not book or not book['levels'] or not book['levels'][1]:
            raise LiveAdapterError(f'{coin} 无卖盘，无法 taker 补齐')
        ask = float(book['levels'][1][0]['px'])
        if max_px is not None and ask > float(max_px):
            raise LiveAdapterError(
                f'{coin} ask {ask} 高于保护价 {max_px}，放弃 taker 补齐')
        return float(price_wire(Decimal(str(ask)), buy=True, tif='Ioc'))


# ---------------- WS 实时状态（复用 realtime_guard LiveState 模式）----------------

class LiveState:
    """l2Book 订阅 + 1s 节流止损。修复 realtime_guard 的三个已知问题：
    1) 重连时 ws.stop() 的 on_close 触发旧代事件 → 分代 Event + closing 标记
    2) on_close 事件驱动感知（不再只靠 is_alive 兜底轮询）
    3) 启动历史成交过滤（started_ms）"""

    def __init__(self, outcome_ids, owner, on_fill, on_book_update=None):
        self.outcome_ids = set(int(o) for o in outcome_ids)
        self.owner = owner
        self.events = queue.Queue()
        self.bids = {}                       # {coin: best_bid}
        self.started_ms = int(time.time() * 1000)
        self.last_check = 0.0
        self.last_reconnect = 0.0
        self.on_fill = on_fill               # callback(fills)  → Accounting.ingest
        self.on_book_update = on_book_update
        self.gen = {"id": 0, "down": threading.Event(), "closing": False}

    def want_coin(self, coin):
        if not str(coin).startswith("#"):
            return False
        try:
            enc = int(coin[1:])
        except ValueError:
            return False
        return enc // 10 in self.outcome_ids

    def handle_book(self, msg):
        data = msg.get('data', {})
        coin, levels = data.get('coin', ''), data.get('levels')
        if self.want_coin(coin) and levels and levels[0]:
            self.events.put(('book', data))

    def handle_fills(self, msg):
        data = msg.get('data', {})
        fills = data.get('fills', []) if isinstance(data, dict) else []
        self.events.put(('fills', [f for f in fills if self.want_coin(f.get('coin', ''))]))

    def watch_market(self, oid):
        """新开市场后把它的两个 coin 纳入成交/盘口过滤（幂等）。"""
        oid = int(oid)
        if oid not in self.outcome_ids:
            self.outcome_ids.add(oid)

    def bind_reexecutor(self, executor):
        """把成交回调接到执行器的账本桥；同时把新开市场登记到 WS。

        返回值只用于留痕（谁绑上了），不改变任何记账语义。
        """
        self.executor = executor
        return executor is not None

    def mark_down(self, reason, my_gen):
        """分代断连感知（修复问题 1/2）：旧代事件、主动关闭均忽略。"""
        if self.gen.get("closing"):
            return
        if my_gen != self.gen["id"]:
            return
        log(f"WS 断开 [{reason}] gen={my_gen}")
        self.gen["down"].set()

    def bind(self, ws):
        """把分代 on_close/on_error 绑到 ws 底层 socket。"""
        self.gen["id"] += 1
        my_gen = self.gen["id"]
        self.gen["down"].clear()
        self.gen["closing"] = False
        ws.ws.on_close = lambda _w, code, msg: self.mark_down(f"close code={code}", my_gen)
        ws.ws.on_error = lambda _w, err: self.mark_down(f"error {type(err).__name__}", my_gen)
        return my_gen

    def begin_stop(self):
        """主动关闭前调用：屏蔽自身 on_close（修复问题 1 的死循环）。"""
        self.gen["closing"] = True


# ---------------- 执行器主体 ----------------

class ExecutorV2:
    """N 市场状态机。adapter 提供全部交易所 IO，测试里全部 mock。"""

    def __init__(self, cfg, adapter, accounting, owner, dry=False,
                 state_path=None, candidates=None, now=None, ledger=None):
        self.cfg = cfg
        self.adapter = adapter
        self.acct = accounting
        self.owner = owner
        self.dry = dry
        self.state_path = Path(state_path) if state_path else STATE_FILE
        self.candidates = candidates or []
        self.now = now or time.time
        # live 由 build_live() 注入真 Ledger；dry/无账本时熔断输入不可用（明确标注）
        self.ledger = ledger
        self.loop_thread = threading.get_ident()
        self.state = self.state_load()

    # ---- 状态持久化：str key，幂等（重启恢复不丢持仓/挂单）----
    def state_load(self):
        if not self.dry and self.state_path.exists():
            try:
                st = __import__('v2_persistence').read_last(self.state_path)
                if not isinstance(st.get('markets'), dict):
                    raise ValueError('missing markets')
                return st
            except Exception as exc:
                raise LiveAdapterError('状态损坏，拒绝按空仓恢复') from exc
        return {'markets': {}, 'cum_net': None, 'settled_periods': 0,
                'halted': False, 'halt_reason': '', 'periods': [], 'seen_payouts': [],
                'ledger_known': False, 'snapshot_known': False, 'activation_valid': False}

    def state_save(self, *, heartbeat=False):
        if threading.get_ident() != self.loop_thread:
            raise LiveAdapterError('状态仅允许主循环线程写入')
        if self.dry:
            return
        # Financial intents/evidence are synchronous; telemetry alone is limited.
        # 2026-10-30 修复：journal 在 1.9 小时内被写满 32MiB（13221 行 × 2.5KB，
        # 约 1.9 次/秒），导致 append 被上限拒绝 → 主循环每 5 秒崩溃一次。
        # 根因不是文件太大，而是**每轮 tick 内的临时标志位翻转**被当成状态变更：
        # tick() 开头把 merge_evidence_known/snapshot_known 置 False，collect_fills()
        # 再置 True，state_save 在这两步之间被调用多次 → encoded 每次都不一样。
        # 这些字段是**单轮内的瞬时中间态**，不构成需要落盘的持久状态，
        # 因此从去重比较中排除（仍然会随下一次真实变更一起写入）。
        # 2026-11-02 修复（重启后 snapshot_known 恒为 None → 新实验永远开不了仓）：
        # 原列表把 snapshot_known 当「单轮瞬时态」排除落盘。但 open_market 用它做
        # 准入门槛（`not snapshot_known` → 拒绝开仓），而内存值在重启后丢失
        # → 落盘值永远是 None → 重启后无法开任何新仓。
        # 实测：新实验 278 行 state 全是 snapshot_known=None，而 TRACE 证明
        # 内存里确实被置 True，只是没写进文件。
        # 旧实验能跑是因为进程从未重启（内存值一直 True），掩盖了这个缺陷。
        # 修法：snapshot_known 必须持久化；它与 merge_evidence_known 不同——
        # 后者只是诊断标志，前者是开仓准入条件。
        # 去重比较仍排除它（避免每轮翻转触发写入），但 projection 要带上。
        TRANSIENT = ('ledger_report', 'heartbeat', 'updated',
                     'merge_evidence_known',
                     # 2026-10-30：resume_blockers 是每轮重算的诊断信息，
                     # 会随预算/网络在 [] 和 [原因] 之间来回切，触发无意义写入。
                     'resume_blockers')
        projection = {k: v for k, v in self.state.items() if k not in TRANSIENT}
        # 2026-11-01 修复 P3-1（intents 无限增长 → 撞 256KB 单记录上限 → tick 崩循环）：
        # journal(ex) 只增不删（全代码库无剪枝），而 state_save 把整个 intents
        # 写进一条 journal 记录。v2_persistence.append_record 在 len(raw) > 256KB
        # 时抛 ValueError → tick 抛 → 每 1 秒一条「主循环异常」，与 10-30 那次
        # journal 写满事故同型，且此时有持仓但状态机不再推进。
        # 实测边界：约 1010 条 final 意图即达 260KB（上限 262144）。
        #
        # 修法：**只裁剪落盘内容，不动内存**。
        # 未了结（unknown/awaiting_fill/submitted）必须全部保留（崩溃恢复要靠它）；
        # 已了结（final/absent/rejected）只保留最近 200 条供排查，完整历史在 ledger。
        _intents = projection.get('intents')
        if isinstance(_intents, dict) and len(_intents) > 200:
            _open_states = ('unknown', 'awaiting_fill', 'submitted')
            _keep = {k: v for k, v in _intents.items()
                     if isinstance(v, dict) and v.get('status') in _open_states}
            _closed = [(k, v) for k, v in _intents.items() if k not in _keep]
            _closed.sort(key=lambda kv: kv[1].get('created_ms', 0) if isinstance(kv[1], dict) else 0)
            for k, v in _closed[-200:]:
                _keep[k] = v
            projection['intents'] = _keep
            projection['intents_pruned'] = {
                'total': len(_intents), 'persisted': len(_keep),
                'note': '已了结意图仅保留最近200条；完整历史见 ledger',
            }
        # 去重签名额外排除 snapshot_known（每轮翻转，但值已随 projection 落盘）
        _sig = {k: v for k, v in projection.items() if k != 'snapshot_known'}
        encoded = json.dumps(_sig, sort_keys=True)
        now = self.now()
        if encoded == getattr(self, '_saved_projection', None):
            # 内容未变：仅在显式心跳时按最小间隔落一次时间戳，其余全部跳过。
            if not heartbeat or now-getattr(self, '_saved_at', -1e30) < 30:
                return
        # 内容有变则**立即写入**，不做时间节流：state_save 承担的是崩溃恢复语义
        # （write-ahead intent、持仓/挂单、暂停原因），节流会丢关键状态。
        # 真正要治的是「瞬时字段翻转被误判为变更」，已在 TRANSIENT 里排除。
        self.state['updated'] = int(now)
        projection['updated'] = int(now)
        # 撞上 32MiB 上限前主动滚动（2026-10-30 崩溃循环事故）。
        # 归档是原子改名、原文不动、不删除；之后在新空文件里继续写。
        persistence = __import__('v2_persistence')
        archived = persistence.maybe_archive(self.state_path)
        if archived is not None:
            self.state['journal_archived_to'] = str(archived)
            projection['journal_archived_to'] = str(archived)
            log(f'  📦 state journal 已滚动归档 → {archived.name}')
        persistence.append_record(self.state_path, projection)
        self._saved_projection, self._saved_at = encoded, now

    # ---- 开仓 ----
    def open_market(self, cand):
        from v2_safety import open_market
        return open_market(self, cand)

    # ---- 维护：merge 后立即重挂 ----
    def merge_and_requote(self, oid_s, pos):
        from v2_safety import merge
        return merge(self, str(oid_s), pos)

    # ---- 单边持仓 ----
    def maintain_single_side(self, oid_s, pos):
        from v2_safety import unwind
        self.state['markets'][str(oid_s)]['phase'] = 'unwinding'
        return True, unwind(self, str(oid_s), pos)

    # ---- 每轮维护 ----
    def maintain(self, positions_by_market):
        from v2_safety import maintain
        return maintain(self, positions_by_market)

    def unwind_residual(self, oid_s, pos):
        from v2_safety import unwind
        return unwind(self, str(oid_s), pos)

    # ---- 熔断（决策 4：吃 ledger 实测数 + reward 到账）----
    def on_period_payout(self, reward_usd, period_ledger_net, period=None):
        from v2_safety import checkpoint
        return checkpoint(self, reward_usd, period_ledger_net, period)

    def halt_actions(self, live_positions=None):
        # 2026-11-01 halt 重构：把链上实时持仓传下去。
        # 不传时 halt() 不会推任何市场到 unwinding（保守，避免误撤挂单）。
        from v2_safety import halt
        halt(self, live_positions=live_positions)

    # ---- 主循环（live 用；dry-run 冒烟走 run_once）----
    def run_once(self, positions_by_market=None):
        """完整走一轮状态机（dry 冒烟入口）。"""
        positions_by_market = positions_by_market or {}
        opened = []
        for cand in self.candidates:
            ok, why = self.open_market(cand)
            opened.append((cand.get("outcome_id"), ok, why))
        maintained = self.maintain(positions_by_market)
        return opened, maintained


# ---------------- reward payout 轮询（任务 C；只读）----------------

def payout_id_of(payout):
    if not payout.get('tx_hash') or payout.get('market_id') is None or payout_paid_at_ms(payout) is None:
        return None
    # One transaction may contain several market payments.
    return f"{str(payout['tx_hash']).lower()}:{payout['market_id']}:{payout_paid_at_ms(payout)}"


def payout_is_paid(payout):
    return ((payout.get('sent') is True or payout.get('status') == 'sent')
            and payout.get('status') not in ('pending', 'failed')
            and bool(payout.get('tx_hash'))
            and payout.get('paid_at') is not None and payout.get('market_id') is not None
            and payout.get('reward_usdc') is not None)


def payout_paid_at_ms(payout):
    raw = payout.get("paid_at") or payout.get("paidAt") or payout.get("payout_at") \
        or payout.get("timestamp") or payout.get("time")
    if raw is None:
        return None
    try:
        return int(float(raw) * (1000 if float(raw) < 1e11 else 1))
    except (TypeError, ValueError):
        pass
    try:
        return int(parse_time(raw) * 1000)
    except Exception:
        return None


class RewardWatcher:
    '轮询奖励到账接口，按新的已支付 payout 划分核算期。\n\n回溯窗口为上一次与本次 payout 的 paid_at，窗口内账本已实现净损益\n加本次奖励构成本期净额，由 on_period_payout 累加并检查熔断。\n请求携带 User-Agent，失败按 REWARD_HTTP_ATTEMPTS 有界重试；\npending 记录跳过，已见 payout 集合持久化，避免重启后重复记账。'

    def __init__(self, executor, accounting, owner, state_path=None, fetcher=None,
                 poll_interval_s=None, now=None, log_fn=None, client=None):
        self.executor = executor
        self.acct = accounting
        self.owner = owner
        self.state_path = Path(state_path) if state_path else REWARD_STATE_FILE
        self.interval = REWARD_POLL_S if poll_interval_s is None else float(poll_interval_s)
        self.now = now or time.time
        self.log = log_fn or log
        self.fetcher = fetcher or (lambda url: http_json(url, client=client))
        self.last_poll = 0.0
        self.state = self.load()

    def load(self):
        st = {'seen': [], 'baseline_complete': False, 'last_error': None}
        if self.state_path.exists():
            st.update(__import__('v2_persistence').read_last(self.state_path))
        return st

    def save(self):
        self.state['last_poll'] = int(self.now())
        __import__('v2_persistence').append_record(self.state_path, self.state)

    def url(self):
        return f"{REWARD_API}/v1/rewards/{self.owner}"

    def due(self):
        return (self.now() - self.last_poll) >= self.interval

    def fetch(self):
        try:
            return self.fetcher(self.url())
        except Exception as exc:
            self.state["last_error"] = f"{type(exc).__name__}: {exc}"
            self.log(f"  reward 接口失败（已重试上限内放弃本轮）: {self.state['last_error']}")
            return None

    def seed(self, data=None):
        '建立已支付 payout 的历史基线，避免将历史到账误计为本期收益。\n\n基线必须非空，每条记录都必须具备唯一且不重复的 id。\n将基线笔数保存到 state 的 baseline_count；笔数减少表示数据源倒退，\n应阻断处理，新增已支付记录则允许基线增长。'
        data = self.fetch() if data is None else data
        if data is None:
            return 0
        paid = [p for p in self._payouts(data) if payout_is_paid(p)]
        raw_ids = [payout_id_of(p) for p in paid]
        ids = set(raw_ids)
        if None in ids:
            raise LiveAdapterError('历史reward基线：存在无法识别的 payout id')
        if len(ids) != len(raw_ids):
            raise LiveAdapterError(
                f'历史reward基线：id 重复（{len(raw_ids)} 条记录仅 {len(ids)} 个唯一 id）')
        if not ids:
            raise LiveAdapterError('历史reward基线：已支付记录为 0，无法建立基线')
        previous = self.state.get('baseline_count')
        if previous is not None and len(ids) < int(previous):
            raise LiveAdapterError(
                f'历史reward基线倒退：上次 {previous} 笔，本次仅 {len(ids)} 笔')
        self.state.update(seen=sorted(ids), baseline_complete=True, baseline=paid,
                          baseline_count=len(ids))
        self.save()
        return len(ids)

    @staticmethod
    def _payouts(data):
        if isinstance(data, dict):
            items = data.get("rewards") or data.get("payouts") or []
        else:
            items = data or []
        return [p for p in items if isinstance(p, dict)]

    def _newest_paid_ms(self, data):
        times = [payout_paid_at_ms(p) for p in self._payouts(data) if payout_is_paid(p)]
        times = [t for t in times if t]
        return max(times) if times else None

    def poll(self, data=None):
        self.last_poll = self.now()
        if not self.state.get('baseline_complete'):
            self.seed(data)
            return []
        data = self.fetch() if data is None else data
        if data is None:
            return []
        credited = []
        ex = self.executor
        # Attribution must name an exact receipt and evidence; market/time alone
        # cannot prove the reward belongs to this experiment.
        claims = ex.cfg.get('reward_attributions', {})
        claim_path = ex.cfg.get('v2_reward_attribution_file')
        if claim_path:
            claims = json.loads((BASE / claim_path).read_text())
        for p in self._payouts(data):
            if not payout_is_paid(p):
                continue
            pid = payout_id_of(p)
            if not pid or (pid in self.state['seen'] and pid not in ex.state.get('rewards', {})):
                continue
            amount = dec(p['reward_usdc'])
            if amount < 0:
                raise ValueError('negative reward')
            claim = claims.get(pid, {})
            attributed = (claim.get('experiment_id') == ex.state.get('experiment_id')
                          and bool(claim.get('evidence'))
                          and __import__('v2_safety').market_id(p['market_id']) in {str(c['outcome_id']) for c in ex.candidates}
                          and payout_paid_at_ms(p) >= ex.state.get('experiment_start_ms', 2**63))
            previous = ex.state.get('rewards', {}).get(pid)
            if previous:
                if previous['reward'] != float(amount):
                    raise ValueError('同一reward身份金额冲突')
                if attributed and not previous.get('attributed'):
                    previous.update(attributed=True, attribution_evidence=claim['evidence'])
                    __import__('v2_safety').recompute_net(ex)
                    ex.state_save()
                if pid in self.state['seen']:
                    continue
            _, _, record = ex.on_period_payout(amount, None, period={
                'payout_id': pid, 'market_id': p['market_id'], 'paid_at_ms': payout_paid_at_ms(p),
                'attribution_confirmed': attributed, 'attribution_evidence': claim.get('evidence'),
                'raw_receipt': p, 'checkpoint_only': True})
            # Financial receipt is durable in executor first. Crash before watcher
            # save is harmless: checkpoint is identity-idempotent.
            self.state['seen'].append(pid)
            credited.append(record)
        self.save()
        return credited

    def run_forever(self, stop_event=None):
        raise LiveAdapterError('reward只允许由RuntimeLoop主线程轮询')


def fetch_rewards(owner, *, attempts=REWARD_HTTP_ATTEMPTS, timeout=REWARD_HTTP_TIMEOUT,
                  client=None):
    """读 reward 接口（只读）。**必须带 User-Agent**：裸 urllib 会被 403（实测）。

    失败最多试 `attempts` 次，仍失败则抛出最后一次异常（由调用方决定降级），
    这样「失败」不会被伪装成「没有新 payout」。
    """
    url = f"{REWARD_API}/v1/rewards/{owner}"
    last = None
    for _ in range(max(1, int(attempts))):
        try:
            req = urllib.request.Request(url, headers={
                "User-Agent": "Mozilla/5.0 (compatible; hip4-executor-v2/1.0)",
                "Accept": "application/json"})
            opener = client or urllib.request.urlopen
            with opener(req, timeout=timeout) as r:
                return json.loads(r.read().decode())
        except Exception as exc:
            last = exc
            time.sleep(0.5)
    raise last if last else RuntimeError("reward fetch failed without exception")


def http_json(url, retries=3, timeout=REWARD_HTTP_TIMEOUT, payload=None, client=None):
    """通用只读 JSON GET/POST（带 User-Agent + 有界重试）。"""
    opener = client or urllib.request.urlopen
    if payload is None:
        req = urllib.request.Request(url, headers={
            "User-Agent": "Mozilla/5.0 (compatible; hip4-executor-v2/1.0)",
            "Accept": "application/json"})
    else:
        req = urllib.request.Request(url, data=json.dumps(payload).encode(),
                                     headers={"Content-Type": "application/json",
                                              "User-Agent": "Mozilla/5.0 (compatible; hip4-executor-v2/1.0)"},
                                     method="POST")
    last = None
    for _ in range(max(1, int(retries))):
        try:
            with opener(req, timeout=timeout) as r:
                return json.loads(r.read().decode())
        except Exception as exc:
            last = exc
            time.sleep(0.5)
    raise last if last else RuntimeError("http_json failed without exception")


# ---------------- live 装配 ----------------

def load_private_key(path=None, *, live_approved=False):
    """读私钥：文件缺失/格式坏/私钥非法 → 抛异常，**不静默降级**。

    不打印任何私钥片段——日志里只出现路径与错误类型。
    """
    if not live_approved:
        raise LiveAdapterError('仅真实live且首次激活已批准后允许读取keys')
    path = Path(path) if path else KEY_FILE
    if not path.exists():
        raise FileNotFoundError(
            f"私钥文件缺失: {path}（live 模式必须由 keys/agent.json 提供 private_key；"
            f"缺失时拒绝启动，绝不降级成只读/模拟运行）")
    try:
        kp = json.loads(path.read_text())
    except Exception as exc:
        raise RuntimeError(f"私钥文件无法解析: {path}（{type(exc).__name__}）") from exc
    if not isinstance(kp, dict) or not kp.get("private_key"):
        raise RuntimeError(f"私钥文件缺少 private_key 字段: {path}")
    return str(kp["private_key"]), str(kp.get("owner") or kp.get("account_address") or "")


def make_exchange_for(outcome_ids, key_path=None, owner=None, live_approved=False):
    if not live_approved:
        raise LiveAdapterError('读keys前必须live+首次激活指纹验证')
    from v2_safety import OWNER
    private_key, _ = load_private_key(key_path, live_approved=True)
    from eth_account import Account
    from hyperliquid.exchange import Exchange
    from hyperliquid.utils import constants
    wallet = Account.from_key(private_key)
    account = owner or OWNER
    if account.lower() != OWNER.lower():
        raise LiveAdapterError('owner不匹配')
    return Exchange(wallet, constants.MAINNET_API_URL, account_address=account), wallet


class LiveRuntime(RuntimeLoop):
    """live 运行期持有物：adapter / WS / 线程句柄。close() 可重入。"""

    def reward_step(self):
        """HTTP worker only returns raw results; loop thread owns all writes."""
        if not hasattr(self, '_reward_results'):
            self._reward_results = queue.Queue(maxsize=1)
            self._reward_started = None
        try:
            ok, data = self._reward_results.get_nowait()
        except queue.Empty:
            pass
        else:
            self._reward_started = None
            if ok and data is not None:
                self.watcher.poll(data=data)
            else:
                self.watcher.state['last_error'] = str(data)
        if self._reward_started is not None:
            return
        if not self.watcher.due() and self.watcher.last_poll:
            return
        self.watcher.last_poll = self.executor.now()
        self._reward_started = self.executor.now()
        fetcher, url, results = self.watcher.fetcher, self.watcher.url(), self._reward_results
        def read():
            try:
                result = (True, fetcher(url))
            except Exception as exc:
                result = (False, type(exc).__name__+': '+str(exc))
            results.put(result)
        self.reward_thread = threading.Thread(target=read, daemon=True, name='reward-readonly')
        self.reward_thread.start()

    def __init__(self, **kw):
        self.__dict__.update(kw)
        self.closed = False
        # 2026-11-04：发现扫描专属桶。额度用代码常量（DISCOVERY_RESERVE），
        # **不读 config** —— config 参与 fingerprint(cfg)，改配置会让
        # authorization/activation 三层指纹失配并触发 halt。
        # 仅在启用动态候选时开启；未启用时保持旧语义（discovery_reserve=0）。
        discovery_reserve = (DISCOVERY_RESERVE
                             if self.executor.cfg.get('dynamic_candidates_enabled')
                             else 0)
        budget = WeightBudget(self.executor.now,
                              self.executor.cfg.get('rest_weight_per_minute', 600),
                              reserve=self.executor.cfg.get('rest_essential_reserve', 200),
                              discovery_reserve=discovery_reserve)
        self.info_fn = BudgetedInfo(self.info_fn, budget)
        self.adapter.info = self.info_fn
        self.budget = budget
        # 2026-11-02 L1：把 openOrders 缓存时长注入 adapter。
        # 默认 3 秒：大于一个 tick（1s），小于撤单+复核耗时上限，且能跨
        # 同一 tick 内多个市场/多个调用点复用同一份全量挂单。
        # 设 0 可完全关闭（回到改造前的行为）。
        try:
            _ttl = float(self.executor.cfg.get('open_orders_cache_seconds', 3))
            self.adapter._oo_cache_seconds = max(0.0, _ttl)
        except (TypeError, ValueError):
            self.adapter._oo_cache_seconds = 3.0

    def close(self):
        if self.closed:
            return
        self.closed = True
        for ev in (getattr(self, "stop_event", None),):
            if ev is not None:
                ev.set()
        ws = getattr(self, "ws", None)
        state = getattr(self, "state", None)
        if ws is not None:
            try:
                if state is not None:
                    state.begin_stop()          # 屏蔽自身 on_close → 不触发重连
                ws.stop()
            except Exception as exc:
                log(f"WS 关闭异常: {type(exc).__name__}: {exc}")
        if getattr(self, "ws_thread", None) is not None:
            try:
                self.ws_thread.join(timeout=5)
            except Exception:
                pass
        if getattr(self, "reward_thread", None) is not None:
            try:
                self.reward_thread.join(timeout=5)
            except Exception:
                pass
        book = getattr(self, "ledger", None)
        if book is not None:
            try:
                book.close()
            except Exception:
                pass


def build_live(key_path=None, state_path=None, ledger_path=None, cfg=None,
               candidates=None, owner=None, ledger=None, exchange=None,
               now=None, info_fn=None, start_threads=False, reward_fetcher=None,
               authorization=None, activation_path=None):
    from v2_safety import OWNER, activation_valid, fingerprint
    cfg = dict(cfg or {})
    if not cfg:
        cfg, authorization, candidates, _ = __import__('v2_safety').load_inputs(BASE)
    candidates = list(candidates or [])
    activation_path = activation_path or BASE/'v2_first_activation.json'
    approved = activation_valid(activation_path, cfg, authorization)
    # Mock injection never grants permission to load real keys.
    if exchange is None:
        if not approved:
            raise LiveAdapterError('首次激活凭据缺失/指纹不匹配；未读keys')
        exchange, wallet = make_exchange_for([], key_path, OWNER, live_approved=True)
    else:
        wallet = getattr(exchange, 'wallet', None)
    resolved_owner = owner or OWNER
    if str(getattr(exchange, 'account_address', '')).lower() != resolved_owner.lower():
        raise LiveAdapterError('SDK account_address必须为配置owner（agent仅签名）')
    outcome_ids = [int(c['outcome_id']) for c in candidates]
    adapter = LiveAdapter(exchange, outcome_ids, info_fn=info_fn, now=now)
    # Only verified mappings from the independent candidate authorization.
    for c in candidates:
        limits = c.get('sdk_limits', {})
        if limits.get('verified') and len(limits.get('asset_ids', [])) == 2:
            for side, aid in enumerate(limits['asset_ids']):
                coin = f"#{int(c['outcome_id'])*10+side}"
                exchange.info.name_to_coin[coin] = coin
                exchange.info.coin_to_asset[coin] = int(aid)
                exchange.info.asset_to_sz_decimals[int(aid)] = limits['sz_decimals']
    path = Path(state_path or BASE/'v2_experiment_state.jsonl')
    if ledger is None:
        if ledger_path is None:
            raise LiveAdapterError('必须指定本实验独立ledger路径，禁止复用历史账本')
        ledger = Ledger(ledger_path, resolved_owner)
    accounting = Accounting(ledger, resolved_owner, dry=False)
    ex = ExecutorV2(cfg, adapter, accounting, resolved_owner, state_path=path,
                    candidates=candidates, now=now, ledger=ledger)
    exp_id = (authorization or {}).get('experiment_id')
    if ex.state.get('config_fingerprint') not in (None, fingerprint(cfg)) or ex.state.get('authorization_fingerprint') not in (None, fingerprint(authorization)):
        raise LiveAdapterError('实验恢复配置/候选指纹不匹配')
    if ex.state.get('experiment_id') not in (None, exp_id):
        raise LiveAdapterError('实验状态experiment_id不匹配')
    ex.state.update(activation_valid=approved, experiment_id=exp_id,
                    authorization_fingerprint=fingerprint(authorization), config_fingerprint=fingerprint(cfg))
    if not approved:
        ex.state.update(halted=True, halt_reason='首次激活未批准')
    adapter.managed_executor = ex
    ex.state['fill_coverage'] = (authorization or {}).get('fill_coverage', {})
    ex.state['authorization_expires_at'] = (authorization or {}).get('expires_at', 0)
    ls = LiveState(outcome_ids, resolved_owner, on_fill=None)
    from hyperliquid.websocket_manager import WebsocketManager
    # SDK 0.24 expects an HTTP base URL and constructs its own wss://.../ws.
    ws = WebsocketManager('https://api.hyperliquid.xyz')
    for oid in outcome_ids:
        for side in (0, 1):
            ws.subscribe({'type': 'l2Book', 'coin': f'#{oid*10+side}'}, ls.handle_book)
    ws.subscribe({'type': 'userFills', 'user': resolved_owner}, ls.handle_fills)
    ls.bind(ws)
    watcher = RewardWatcher(ex, accounting, resolved_owner,
                            state_path=path.with_name(path.stem+'_rewards.jsonl'),
                            fetcher=reward_fetcher, now=now,
                            poll_interval_s=cfg.get('reward_poll_minutes', 10)*60)
    runtime = LiveRuntime(exchange=exchange, adapter=adapter, ledger=ledger,
                          accounting=accounting, executor=ex, state=ls, ws=ws,
                          watcher=watcher, owner=resolved_owner, wallet=wallet,
                          stop_event=threading.Event(), info_fn=info_fn or hl_info,
                          loop_thread=threading.get_ident(), audit_path=path.with_name(path.stem+'_audit.jsonl'))
    if cfg.get('dynamic_candidates_enabled'):
        from c_runtime import initialize
        initialize(runtime, authorization)
    if (ledger.db.execute('SELECT 1 FROM events LIMIT 1').fetchone()
            or ledger.db.execute('SELECT 1 FROM auxiliary LIMIT 1').fetchone()) and 'opening_evidence' not in ex.state:
        raise LiveAdapterError('已有账本缺本实验恢复基线，保留并拒绝使用')
    if 'opening_evidence' in ex.state:
        runtime.bind_ledger()
    if start_threads:
        ws.start()
        runtime.ws_thread = ws
    return runtime


def hl_info(payload, retries=1, timeout=2.0):
    """Hyperliquid info 只读接口。失败返回 {"__error__": ..}（与旧 executor 同约定）。"""
    try:
        return http_json(INFO_URL, retries=retries, timeout=timeout, payload=payload)
    except Exception as exc:
        return {"__error__": f"{type(exc).__name__}: {exc}"}


def main():
    from v2_safety import load_inputs, activation_valid, fingerprint, OWNER
    ap = argparse.ArgumentParser(description='HIP4 v2独立授权、首次激活、单线程风控运行时')
    mode = ap.add_mutually_exclusive_group(required=True)
    mode.add_argument('--dry-run', action='store_true')
    mode.add_argument('--preflight-readonly', action='store_true')
    mode.add_argument('--live', action='store_true')
    mode.add_argument('--arm-live', action='store_true')
    ap.add_argument('--config', type=Path, default=BASE/'config.json')
    ap.add_argument('--authorization', type=Path)
    ap.add_argument('--activation', type=Path, default=BASE/'v2_first_activation.json')
    ap.add_argument('--state', type=Path, default=BASE/'v2_experiment_state.jsonl')
    ap.add_argument('--ledger', type=Path, default=BASE/'v2_experiment_ledger.sqlite3')
    args = ap.parse_args()
    cfg, auth, candidates, issues = load_inputs(
        BASE, args.config, args.authorization, allow_expired_recovery=args.live)
    approved = activation_valid(args.activation, cfg, auth)
    result = {'config_fingerprint': fingerprint(cfg), 'authorization_fingerprint': fingerprint(auth),
              'activation_valid': approved, 'issues': issues, 'candidates': []}
    from v2_safety import candidate_reason, snapshot
    for c in candidates:
        result['candidates'].append({'outcome_id': c['outcome_id'],
                                     'reason': candidate_reason(c, time.time(), cfg)})
    if args.arm_live:
        # Interactive first activation only. No key reads or order side effects.
        if not auth or issues or not candidates or any(x['reason'] for x in result['candidates']):
            raise LiveAdapterError('配置/候选未通过，拒绝首次激活')
        phrase = 'APPROVE FIRST LIVE '+auth['experiment_id']
        if not sys.stdin.isatty() or input('首次实盘人工确认，请输入 '+phrase+': ') != phrase:
            raise LiveAdapterError('未取得首次实盘人工确认')
        with args.activation.open('x') as f:
            json.dump({'schema': 'hip4-v2-first-activation-1', 'approved': True,
                       'approved_at': int(time.time()), 'operator_confirmation': phrase,
                       'owner': OWNER, 'experiment_id': auth['experiment_id'],
                       'config_fingerprint': fingerprint(cfg), 'authorization_fingerprint': fingerprint(auth)}, f)
        return
    if args.preflight_readonly:
        # Info only, never instantiate Exchange or load_private_key.
        result['snapshot'] = snapshot(hl_info, OWNER, {str(c['outcome_id']) for c in candidates})
        try:
            from importlib.metadata import version
            result['sdk_version'] = version('hyperliquid-python-sdk')
            from hyperliquid.websocket_manager import WebsocketManager
            from hyperliquid.utils.types import Cloid
            result['sdk_interfaces_importable'] = bool(WebsocketManager and Cloid)
        except Exception as exc:
            result['issues'].append('SDK不可验证: '+str(exc))
        for c in candidates:
            bids = [hl_info({'type': 'l2Book', 'coin': f"#{int(c['outcome_id'])*10+s}"}) for s in (0, 1)]
            result.setdefault('books', {})[str(c['outcome_id'])] = bids
            try:
                prices = [float(price_wire(book['levels'][0][0]['px'], buy=True)) for book in bids]
                shares, why = shares_for_open(prices, cfg['capital_per_market'], cfg.get('quote_mode', 'off'))
                limits = c.get('sdk_limits', {})
                minimum_ok = (shares is not None and minimum_order(prices, shares, limits))
                result.setdefault('budgets', {})[str(c['outcome_id'])] = {
                    'shares': shares, 'reason': why, 'sdk_minimum_satisfied': minimum_ok,
                    'notional': shares*sum(prices) if shares else None}
            except (KeyError, TypeError, ValueError, IndexError) as exc:
                result['issues'].append('盘口/预算未知: '+str(exc))
        print(json.dumps(result, ensure_ascii=False, indent=2))
        return
    if args.dry_run:
        result['budget_example'] = shares_for_open([0.60725, 0.38917], 12, 'off')
        result['offline'] = True
        print(json.dumps(result, ensure_ascii=False, indent=2))
        return
    if not approved:
        raise LiveAdapterError('首次激活缺失/指纹不匹配，未读取keys，未启动交易')
    runtime = build_live(cfg=cfg, candidates=candidates, authorization=auth,
                         activation_path=args.activation, state_path=args.state,
                         ledger_path=args.ledger, start_threads=True)
    def guard():
        current_cfg, current_auth, _, current_issues = load_inputs(BASE, args.config, args.authorization)
        return (not current_issues and fingerprint(current_cfg) == fingerprint(cfg)
                and fingerprint(current_auth) == fingerprint(auth)
                and activation_valid(args.activation, current_cfg, current_auth))
    runtime.authorization_guard = guard
    try:
        runtime.run_forever()
    except KeyboardInterrupt:
        log('进程中断；未宣称已撤净，重启后须继续对账管理')
    finally:
        runtime.close()


if __name__ == "__main__":
    main()
