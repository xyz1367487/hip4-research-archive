#!/usr/bin/env python3
"""
HIP-4 市场扫描器（第一层，每日一次）

职责：
  1. 拉 current-incentives 全量市场
  2. 按 config.json 过滤（池子/剩余时间/带宽比价差/价差/mid区间）
  3. 检查 best bid 是否在计分带内（挂单即计分 = 硬前提）
  4. 按「池子大小 × 带宽/价差」打分排序
  5. 排除黑名单（连续止损 3 次的市场）
  6. 输出 candidates.json + 人可读表格

用法：
  python3 scanner.py              # 只读扫描，打印表格
  python3 scanner.py --json       # 只输出 JSON（给程序用）
  python3 scanner.py --write-candidates  # 显式保存旧格式 candidates.json
"""
import json
import math
import sys
import time
import urllib.request
from datetime import datetime, timedelta, timezone
from pathlib import Path

# 时间口径与执行器同源：体育盘的闸门是「清仓截止」而不是 incentive_end_time。
# 复用 executor_v2 的解析，避免扫描器与执行器各写一套规则后分叉
# （edge_scan.py 也是这么做的）。不会读取 keys，也没有 import 期副作用。
from executor_v2 import settlement_time, sports_schedule

BASE = Path(__file__).resolve().parent
CONFIG_FILE = BASE / "config.json"
CANDIDATES_FILE = BASE / "candidates.json"
BLACKLIST_FILE = BASE / "blacklist.json"
STATE_FILE = BASE / "executor_state.json"

BJT = timezone(timedelta(hours=8))
INFO_URL = "https://api.hyperliquid.xyz/info"
MONARCH_INC = "https://api.monarch.fast/marina/outcome-markets/current-incentives"
MONARCH_SCORES = "https://api.monarch.fast/marina/outcome-markets/scores?market_id={}"

UA = {"User-Agent": "Mozilla/5.0"}


def load_config():
    with open(CONFIG_FILE) as f:
        return json.load(f)


def http_json(url, payload=None, retries=3, timeout=20):
    last = None
    for _ in range(retries):
        from v2_protocol import charge_scan_http
        charge_scan_http(url, payload)
        try:
            if payload is None:
                req = urllib.request.Request(url, headers=UA)
            else:
                req = urllib.request.Request(
                    url, data=json.dumps(payload).encode(),
                    headers={"Content-Type": "application/json"}, method="POST")
            with urllib.request.urlopen(req, timeout=timeout) as r:
                return json.loads(r.read().decode())
        except Exception as e:
            last = e
            time.sleep(0.8)
    return {"__error__": f"{type(last).__name__}: {last}"}


def hl_info(payload, retries=3):
    return http_json(INFO_URL, payload, retries=retries)


def logit(p):
    return math.log(p / (1 - p))


def logistic(x):
    return 1 / (1 + math.exp(-x))


def load_active_outcomes():
    """已在仓（waiting/holding）的 outcome_id —— 扫描时应排除，避免重复选同一个市场"""
    if not STATE_FILE.exists():
        return set()
    try:
        st = json.loads(STATE_FILE.read_text())
        return {int(v["outcome_id"]) for v in (st.get("markets") or {}).values()
                if v.get("phase") in ("waiting", "holding")}
    except Exception:
        return set()


def load_blacklist():
    """{market_id: {"until": epoch, "count": n}}"""
    if not BLACKLIST_FILE.exists():
        return {}
    try:
        d = json.loads(BLACKLIST_FILE.read_text())
        now = time.time()
        return {k: v for k, v in d.items() if v.get("until", 0) > now}
    except Exception:
        return {}


def band_of(mid, base_cents, band_mult):
    """返回 (下沿, 上沿)。公式来自 docs.monarch.fast/outcome-liquidity-rewards"""
    v = (logit(0.5 + base_cents / 200) - logit(0.5)) * band_mult
    return logistic(logit(mid) - v), logistic(logit(mid) + v), v


def pool_of(market):
    '激励池金额。优先读取子 outcome 的 reward_amount_usdc，\naggregate 可用 total_reward_amount_usdc 作为门槛判断兜底。\n展开后的叶子不继承父级总池，避免将整池金额重复计入每个子 outcome。'
    raw = market.get("reward_amount_usdc")
    if raw is None:
        raw = market.get("total_reward_amount_usdc")
    return float(raw or 0)


_GROUP_KEYS = ("outcomes", "epochs", "markets")
# 父级的「总池」字段：它是 question 级总池，不是单个 outcome 的池。
# 展开时不能继承（见 flatten_markets 的 pool 语义说明）。
_AGGREGATE_POOL_KEYS = ("total_reward_amount_usdc",)


def flatten_markets(raw_markets):
    '展开 aggregate 或嵌套市场为叶子 outcome，并保留来源路径。\n\n子级字段覆盖父级字段，epochs 沿继承链传递。\n展开时剥离父级 reward_amount_usdc 和 total_reward_amount_usdc，\n子级仅使用自己的 reward_amount_usdc，缺失时按零处理。\n不依据未公开的分配假设摊分父池。'
    leaves = []

    def visit(node, parent=None, path="markets"):
        if not isinstance(node, dict):
            return
        merged = dict(parent or {})
        merged.update({k: v for k, v in node.items() if k not in _GROUP_KEYS})
        # epochs 不参与普通字段合并，但要沿链传递到叶子：29 个市场没有顶层
        # incentive_end_time，epochs 是 time_window() 唯一的时间来源，丢了就会
        # 全部误报「无结束时间」。edge_scan 用「按 epoch 展开成多行」达到同一目的，
        # 这里保持 scanner 原有的「一行一 outcome」形态，改为把 epochs 挂到叶子上。
        epochs = node.get("epochs") or (parent or {}).get("epochs")
        children = node.get("outcomes") or node.get("markets")
        if children:
            inherited = dict(merged)
            for k in _AGGREGATE_POOL_KEYS + ("reward_amount_usdc",):
                inherited.pop(k, None)
            inherited["_parent_pool_usdc"] = pool_of(merged)   # 仅供排查，不参与判门槛
            children = children.values() if isinstance(children, dict) else children
            children = [c for c in children if isinstance(c, dict)]
            if epochs:
                inherited["epochs"] = epochs
            for i, child in enumerate(children):
                visit(child, inherited, f"{path}.outcomes[{i}]")
            return
        if epochs:
            merged["epochs"] = epochs
        merged["_source_path"] = path
        leaves.append(merged)

    for i, m in enumerate(raw_markets or []):
        visit(m, path=f"markets[{i}]")
    return leaves


def load_outcome_meta():
    """outcomeMeta → {str(outcome_id): meta}。体育盘的 scheduledStart 只在这个接口里。"""
    raw = hl_info({"type": "outcomeMeta"})
    rows = raw.get("outcomes") if isinstance(raw, dict) else None
    if not isinstance(rows, list):
        return {}
    return {str(r["outcome"]): r for r in rows if isinstance(r, dict) and r.get("outcome") is not None}


def time_window(market, meta, cfg, now_ts):
    """判断剩余时间是否落在配置窗口内。返回 (ok, 淘汰原因, 口径信息)。

    两套口径，不能混：
      - 体育盘：闸门是**清仓截止** = scheduledStart − pre_game_clear_seconds，
        即「还能挂单多久」。下界 0（开赛前 1h 内不该新开），上界 max_hours_left。
        不能套 min_hours_left：体育盘的可做窗口天然短于 12h。
        也不能用 incentive_end_time：体育盘的它恒等于 scheduledStart+168h，
        会把「实际只剩 9h」的市场算成「剩 178h」而全部淘汰。
      - 非体育盘：沿用激励周期结束时间（缺顶层字段时回退当前 epoch），
        双端 min_hours_left/max_hours_left。
    与 v2_safety.candidate_reason()、edge_scan.inspect_market() 完全一致。
    """
    sched = sports_schedule(meta or {})
    if sched:
        lead = float(cfg.get("pre_game_clear_seconds", 3600))
        clear_at = sched["scheduledStart"] - lead
        rem_h = (clear_at - now_ts) / 3600
        info = {"time_basis": "sports_clearing_deadline", "remaining_hours": rem_h,
                "clearing_deadline_epoch": clear_at, "gate_epoch": clear_at, "epoch_end": None}
        if not 0 < rem_h <= cfg["max_hours_left"]:
            return False, "体育盘距清仓截止不在窗口", info
        return True, None, info

    end, epoch_end = market.get("incentive_end_time"), None
    if not end:
        eps = market.get("epochs") or []
        if isinstance(eps, dict):
            eps = list(eps.values())
        cur = None
        for e in eps:
            if not isinstance(e, dict):
                continue
            if str(e.get("incentive_status") or "") in ("incentivized", "active"):
                cur = e
                break
        if cur is None and eps:
            cur = eps[-1] if isinstance(eps[-1], dict) else None
        if cur:
            end = cur.get("incentive_end_time")
            epoch_end = cur.get("epoch_end_date")
    if not end:
        return False, "无结束时间", {"time_basis": "incentive_end", "remaining_hours": None,
                                    "gate_epoch": None, "clearing_deadline_epoch": None,
                                    "epoch_end": epoch_end}
    try:
        end_dt = datetime.fromisoformat(str(end).replace("Z", "+00:00"))
    except Exception:
        return False, "时间解析失败", {"time_basis": "incentive_end", "remaining_hours": None,
                                     "gate_epoch": None, "clearing_deadline_epoch": None,
                                     "epoch_end": epoch_end}
    if end_dt.tzinfo is None:
        return False, "时间解析失败", {"time_basis": "incentive_end", "remaining_hours": None,
                                     "gate_epoch": None, "clearing_deadline_epoch": None,
                                     "epoch_end": epoch_end}
    rem_h = (end_dt.timestamp() - now_ts) / 3600
    info = {"time_basis": "incentive_end", "remaining_hours": rem_h, "end_dt": end_dt,
            "gate_epoch": end_dt.timestamp(), "clearing_deadline_epoch": None,
            "epoch_end": epoch_end}
    if rem_h < cfg["min_hours_left"]:
        return False, f"非体育盘距结算<{cfg['min_hours_left']}h", info
    if rem_h > cfg["max_hours_left"]:
        return False, f"非体育盘距结算>{cfg['max_hours_left']}h", info
    return True, None, info


def scan(cfg=None, *, persist=False):
    cfg = cfg or load_config()
    inc = http_json(MONARCH_INC)
    if isinstance(inc, dict) and inc.get("__error__"):
        return {"error": inc["__error__"], "candidates": []}
    markets = inc.get("markets") if isinstance(inc, dict) else inc
    markets = [m for m in (markets or []) if isinstance(m, dict)]

    # aggregate 行（Q 级）本身没有 hyperliquid_outcome_id，叶子嵌在 outcomes[] 里。
    # 不展开就会把整批嵌套 outcome 当成「无 outcome_id」丢掉（实测 32 行 / 110 叶子）。
    raw_count = len(markets)
    markets = flatten_markets(markets)

    now_ts = time.time()
    meta_by_id = load_outcome_meta()
    if not meta_by_id:
        # 拿不到 meta 就分不出体育盘 → 会退回「用 incentive_end_time 判体育盘」
        # 的错误口径。宁可明确告警，也不要静默扫出一份错名单。
        # 走 stderr：--json 模式下 stdout 必须是纯 JSON。
        print("⚠️ outcomeMeta 拉取失败：体育盘无法识别，时间窗口按非体育盘口径计算",
              file=sys.stderr)
    blacklist = load_blacklist()
    active = set() if cfg.get('dynamic_candidates_enabled') else load_active_outcomes()
    if active:
        print(f"（已在仓 {len(active)} 个市场，将从候选中排除）")

    rows = []
    rejected = {}
    # 嵌套叶子单独记一份淘汰分布：否则「嵌套市场卡在哪一步」会被合并进全市场
    # 计数里看不出来（这正是修复前只知道「无 outcome_id×32」的原因）。
    nested_rejected = {}

    def reject(reason, nested=False):
        rejected[reason] = rejected.get(reason, 0) + 1
        if nested:
            nested_rejected[reason] = nested_rejected.get(reason, 0) + 1

    for m in markets:
        # 是否来自 aggregate 展开（_source_path 形如 markets[3].outcomes[1]）
        nested = ".outcomes[" in (m.get("_source_path") or "")
        hid = m.get("hyperliquid_outcome_id")
        if not hid:
            # 展开后的叶子仍无 id = 该节点本身就没有可交易的 outcome（真缺失）。
            # 曾经的「无 outcome_id」大头其实是未展开的 aggregate 父行，现在
            # 它们已变成有 id 的叶子，所以这个计数应当接近 0。
            reject("无 outcome_id", nested)
            continue
        mid_id = str(m.get("market_id") or "")
        if mid_id in blacklist:
            reject("黑名单", nested)
            continue
        if int(hid) in active:
            reject("已在仓", nested)
            continue

        sp = m.get("scoring_params") or {}
        base = float(sp.get("baseline_total_spread_cents") or 0)
        band_mult = float(sp.get("settlement_band_multiplier") or 1)
        if not base:
            reject("无 baseline 参数", nested)
            continue

        # 时间口径分两种，不能混（详见 time_window()）：
        #   - 体育盘：scheduledStart − pre_game_clear_seconds，下界 0、上界 max_hours_left
        #   - 非体育盘：激励周期结束时间，双端 min/max_hours_left
        # 旧代码对体育盘也用 incentive_end_time，而它恒等于 scheduledStart+168h，
        # 于是「实际只剩 9h」的 NBA 盘被算成「还剩 178h」→ 全被 max_hours_left 淘汰。
        ok, why, win = time_window(m, meta_by_id.get(str(hid)), cfg, now_ts)
        if not ok:
            reject(why, nested)
            continue

        # aggregate 父市场只有 total_reward_amount_usdc，只读 reward_amount_usdc 会得 0
        pool = pool_of(m)
        if pool < cfg["min_pool_usdc"]:
            reject("池子太小", nested)
            continue

        # 盘口
        book = hl_info({"type": "l2Book", "coin": f"#{hid * 10}"})
        if not book or book.get("__error__"):
            reject("盘口查询失败", nested)
            continue
        levels = book.get("levels") or [[], []]
        if not levels[0] or not levels[1]:
            reject("盘口空", nested)
            continue
        bb = float(levels[0][0]["px"])
        ba = float(levels[1][0]["px"])
        bid_depth = float(levels[0][0]["sz"])
        mid = (bb + ba) / 2
        if not (cfg["mid_min"] <= mid <= cfg["mid_max"]):
            reject("mid 出区间", nested)
            continue

        spread_pct = (ba - bb) / mid * 100
        if spread_pct > cfg["max_spread_pct"]:
            reject("价差过宽", nested)
            continue

        lo, hi, v = band_of(mid, base, band_mult)
        band_w_cents = (hi - lo) * 100
        spread_cents = (ba - bb) * 100
        ratio = band_w_cents / spread_cents if spread_cents > 0 else 999
        if ratio < cfg["min_band_over_spread"]:
            reject("带宽/价差 不足", nested)
            continue

        bid_in_band = lo <= bb <= hi
        if not bid_in_band:
            reject("best bid 在带外", nested)
            continue

        # 竞争度延后查（见下方：只对初筛通过的查，避免对 63 个 epoch 市场全查）
        n_wallet, total_q = 0, 0.0
        score = pool * min(ratio, 10)
        # end_bjt/rem_h 现在表示「本市场的有效时间闸门」：体育盘是清仓截止，
        # 非体育盘是激励周期结束。time_basis 显式标出是哪一个，别再把
        # 体育盘的 scheduledStart+168h 当成真实可用时长。
        gate_epoch = win.get("gate_epoch")
        rows.append({
            "_epoch_end": win.get("epoch_end"),
            "market_id": mid_id,
            "outcome_id": hid,
            "name": m.get("market_name") or "",
            "pool": pool,
            "period": m.get("reward_period_type"),
            "time_basis": win["time_basis"],
            "end_bjt": datetime.fromtimestamp(gate_epoch, BJT).strftime("%m-%d %H:%M") if gate_epoch else "-",
            "rem_h": round(win["remaining_hours"], 1),
            "mid": round(mid, 5),
            "best_bid": bb,
            "best_ask": ba,
            "bid_depth": bid_depth,
            "spread_pct": round(spread_pct, 3),
            "band_lo": round(lo, 5),
            "band_hi": round(hi, 5),
            "band_w_cents": round(band_w_cents, 2),
            "ratio": round(ratio, 2),
            "n_wallet": n_wallet,
            "total_quote": round(total_q),
            "score": round(score, 1),
            "etm": float(sp.get("event_time_multiplier") or 1),
        })

    rows.sort(key=lambda r: -r["score"])

    # 只对前 30 个补查竞争度（scores 是重接口，全量查会拖到 100s+）
    for r in rows[:30]:
        url = MONARCH_SCORES.format(r["market_id"])
        if r.get("_epoch_end"):
            url += f"&epoch_end_date={r['_epoch_end']}"
        sc = http_json(url, retries=1, timeout=12)
        if isinstance(sc, list) or (isinstance(sc, dict) and not sc.get("error") and not sc.get("__error__")):
            srows = sc if isinstance(sc, list) else (sc.get("scores") or [])
            srows = [x for x in srows if isinstance(x, dict)]
            r["n_wallet"] = len(srows)
            r["total_quote"] = round(sum(float(x.get("quote_depth_score") or 0) for x in srows))
        r.pop("_epoch_end", None)

    n = int(cfg["n_markets"])
    picked = rows if cfg.get('dynamic_candidates_enabled') else rows[:n]

    # 嵌套可观测性：有多少叶子来自展开、最终卡在哪个闸门。
    # 展开后仍然「无 outcome_id」的叶子 = 真缺失，与「aggregate 未展开」是两回事。
    nested_leaves = sum(1 for m in markets if ".outcomes[" in (m.get("_source_path") or ""))
    aggregate_rows = sum(1 for m in (inc.get("markets") or []) if isinstance(m, dict)
                         and not m.get("hyperliquid_outcome_id")) if isinstance(inc, dict) else 0

    result = {
        "scanned_at": datetime.now(BJT).strftime("%Y-%m-%d %H:%M:%S"),
        "scanned_at_epoch": int(time.time()),
        # total_markets 保持「接口返回的顶层行数」原义（daily.py 用它做对账），
        # 展开后的叶子数另给 flattened_markets，避免这两个口径互相顶替。
        "total_markets": raw_count,
        "flattened_markets": len(markets),
        "aggregate_rows": aggregate_rows,
        "nested_leaves": nested_leaves,
        "nested_rejected_summary": nested_rejected,
        "passed": len(rows),
        "rejected_summary": rejected,
        "candidates": rows,
        "picked": picked,
        "config": cfg,
    }
    if persist:
        CANDIDATES_FILE.write_text(json.dumps(result, ensure_ascii=False, indent=1))
    return result


def print_table(res):
    if res.get("error"):
        print(f"❌ 扫描失败: {res['error']}")
        return
    print(f"=== 扫描 {res['scanned_at']}（北京）===")
    print(f"总市场 {res['total_markets']}，通过筛选 {res['passed']}，选中 {len(res['picked'])}\n")
    if res.get("aggregate_rows"):
        print(f"（展开：顶层 {res['total_markets']} 行 → {res['flattened_markets']} 个叶子，"
              f"其中 {res['aggregate_rows']} 个 aggregate 父行贡献 {res['nested_leaves']} 个嵌套 outcome）")
    if res["rejected_summary"]:
        print("淘汰原因:", ", ".join(f"{k}×{v}" for k, v in sorted(res["rejected_summary"].items(), key=lambda x: -x[1])))
        # 嵌套叶子单独一行，否则看不出嵌套市场到底卡在哪一步
        if res.get("nested_rejected_summary"):
            print("其中嵌套:", ", ".join(f"{k}×{v}" for k, v in sorted(res["nested_rejected_summary"].items(), key=lambda x: -x[1])))
        print()
    if not res["candidates"]:
        print("⚠️ 无合格市场")
        return
    basis_label = {"sports_clearing_deadline": "清仓截止", "incentive_end": "激励截止"}
    hdr = f"{'ID':<8}{'池':>5}{'剩h':>6}{'带宽¢':>7}{'价差%':>7}{'带/价':>6}{'钱包':>5}  {'时间闸门':<10}{'截止(北京)':<12} 事件"
    print(hdr)
    print("-" * len(hdr))
    picked_ids = {c["market_id"] for c in res["picked"]}
    for c in res["candidates"][:12]:
        mark = "★" if c["market_id"] in picked_ids else " "
        basis = basis_label.get(c.get("time_basis"), c.get("time_basis") or "-")
        print(f"{mark}{c['market_id']:<7}{c['pool']:>5.0f}{c['rem_h']:>6.1f}"
              f"{c['band_w_cents']:>7.2f}{c['spread_pct']:>7.2f}{c['ratio']:>6.1f}"
              f"{c['n_wallet']:>5}  {basis:<10}{c['end_bjt']:<12} {c['name'][:40]}")
    print(f"\n★ = 本次选中（N={res['config']['n_markets']}）")
    print("剩h = 体育盘到清仓截止还能挂单多久（下界0）；非体育盘到激励周期结束（12–72h）")


if __name__ == "__main__":
    r = scan(persist="--write-candidates" in sys.argv)
    if "--json" in sys.argv:
        print(json.dumps(r, ensure_ascii=False, indent=1))
    else:
        print_table(r)
