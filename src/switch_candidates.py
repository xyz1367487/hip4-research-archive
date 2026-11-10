#!/usr/bin/env python3
"""HIP-4 候选自动切换（默认 dry-run，写操作必须显式 --apply）。

职责：把 scanner 扫出的市场变成 v2_authorization.json 的新 candidates，
重建指纹链，然后（仅在 --apply 下）重启服务并验证。

设计约束（全部来自只读核实，见报告）：
  1. 不改 config.json —— 三层指纹的第一层是 fingerprint(cfg)，动了全链失效。
  2. 不改 v2_safety.py / executor_v2.py / scanner.py —— 只 import 复用。
  3. 默认 dry-run：`python3 switch_candidates.py` 只做前置检查和计划打印，
     不发任何写操作、不重启、不改授权文件。
  4. 任一前置检查不通过 → 跳过本轮（exit 2，需要人工介入），不切换。

⚠️ 硬阻断（BLOCKING）：账本实验身份绑定
--------------------------------------------------
`executor_v2.build_live()` 会校验 state 里的
`authorization_fingerprint` / `config_fingerprint`；而
`v2_safety.LiveRuntime.bind_ledger()` 又把
`authorization_fingerprint` + `markets` 列表算进账本的
`experiment_identity`，由 `ledger.Ledger.bind_experiment()` 做**字面相等**比较。

实测结论（见报告 §3.4）：
  - 同一个账本 + 换候选 → `ledger experiment identity mismatch` → build_live 抛
    `LiveAdapterError` → 服务起不来（systemd 重启循环）。
  - 即使绕过 build_live，`collect_fills()` 每轮都会抛同一个错 →
    `ledger_known=False` → `can_open_market()` 永久拒绝新仓 → 切了也白切。
  - `experiment_id` 不变也救不了：identity 里的 `markets` 和
    `authorization_fingerprint` 都变了。

因此：**在同一账本 / 同 experiment_id 上换候选组，本仓库当前无法安全实现。**
本脚本把这条做成 `check_ledger_identity()` 前置检查，默认 fail-closed
（`--allow-ledger-identity-change` 才跳过）。要真正做到「扫到就切」，
必须先改 `bind_ledger` 的身份口径（把 markets 从 identity 里摘出，
或按「实验期」而非「候选组」绑定）——那是 v2_safety.py 的改动，
超出本任务「不改 v2_safety.py」的约束，故留作决策项。
"""
import argparse
import json
import shutil
import subprocess
import sys
import time
import urllib.error
import urllib.request
from datetime import datetime, timedelta, timezone
from pathlib import Path

import v2_safety as safe

BASE = Path(__file__).resolve().parent
BJT = timezone(timedelta(hours=8))

# 退出码（与 scan_6h.py 对齐）
EXIT_OK = 0
EXIT_FAILED = 1
EXIT_HUMAN = 2          # 需要人工介入（前置检查不通过 / 回滚后仍异常）

INFO_URL = 'https://api.hyperliquid.xyz/info'
UA = {'User-Agent': 'Mozilla/5.0'}

SERVICE = 'REDACTED_SERVICE_NAME'


# ---------------------------------------------------------------- 基础 IO

def now_epoch():
    return time.time()


def bjt_stamp(epoch=None, fmt='%Y-%m-%d %H:%M:%S'):
    return datetime.fromtimestamp(epoch if epoch is not None else time.time(), BJT).strftime(fmt)


def read_json(path, default=None):
    try:
        return json.loads(Path(path).read_text())
    except FileNotFoundError:
        return default


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
                    headers={'Content-Type': 'application/json'}, method='POST')
            with urllib.request.urlopen(req, timeout=timeout) as r:
                return json.loads(r.read().decode())
        except Exception as exc:               # noqa: BLE001 - 网络层统一收敛
            last = exc
            time.sleep(0.8)
    return {'__error__': f'{type(last).__name__}: {last}'}


def hl_info(payload, retries=3, timeout=20):
    return http_json(INFO_URL, payload, retries=retries, timeout=timeout)


# ------------------------------------------------- 候选字段采集（复用现有逻辑）

def fetch_outcome_meta():
    """outcomeMeta → {str(outcome_id): meta}。体育盘 scheduledStart 只在这里。"""
    raw = hl_info({'type': 'outcomeMeta'})
    rows = raw.get('outcomes') if isinstance(raw, dict) else None
    if not isinstance(rows, list):
        return {}
    return {str(r['outcome']): r for r in rows
            if isinstance(r, dict) and r.get('outcome') is not None}


def fetch_incentive_leaves():
    """取并展开 current-incentives，返回 {str(outcome_id): leaf}。

    复用 scanner.flatten_markets：aggregate 父行（Q 级）本身没有
    hyperliquid_outcome_id，叶子嵌在 outcomes[] 里，不展开会漏掉。
    **一次取全量**，避免每个候选各拉一次（每次都是一次完整 incentives 请求）。
    返回 (map, error)。
    """
    import scanner
    inc = http_json(scanner.MONARCH_INC)
    if isinstance(inc, dict) and inc.get('__error__'):
        return None, inc['__error__']
    markets = inc.get('markets') if isinstance(inc, dict) else inc
    leaves = scanner.flatten_markets([m for m in (markets or []) if isinstance(m, dict)])
    return {str(m.get('hyperliquid_outcome_id')): m
            for m in leaves if m.get('hyperliquid_outcome_id') is not None}, None


def worst_step_cents(outcome_id):
    """历史最差单步（分）：recentTrades 相邻成交价的最大绝对跳变。

    数据来源：`{type: recentTrades, coin: #<oid*10+side>}`，**每条腿仅 10 条**，
    是短窗口代理值而非 24h 全量（`HL数据字典.md` 表 10：`recentTrades` 仅 10 条）。
    这一点必须写进 safety_evidence，不能让下游误以为是长样本。

    取两腿中较差（较大）的一步：安全倍 = 带宽 ÷ 最差单步，单步越大越不安全。
    返回 (cents, evidence_note)；拿不到成交时返回 (None, 原因)。
    """
    worst, total = None, 0
    for side in (0, 1):
        raw = hl_info({'type': 'recentTrades', 'coin': f'#{int(outcome_id) * 10 + side}'})
        if not isinstance(raw, list) or not raw:
            continue
        px = []
        for t in raw:
            try:
                px.append((int(t['time']), float(t['px'])))
            except (KeyError, TypeError, ValueError):
                continue
        px.sort()
        total = max(total, len(px))
        for (_, a), (_, b) in zip(px, px[1:]):
            step = abs(b - a) * 100
            if worst is None or step > worst:
                worst = step
    if worst is None:
        return None, 'recentTrades 无可用成交（仅10条/腿），最差单步不可证'
    return worst, (f'{total}笔近期成交相邻最大步 {worst:.4f}c'
                   f'（recentTrades 仅10条，短窗口代理值，非24h）')


def band_width_cents_for(raw, outcome_id):
    """计分带宽度（分）。复用 scanner.band_of + scoring_params，与扫描同源。

    band_of(mid, baseline_total_spread_cents, settlement_band_multiplier)
    → (lo, hi, v)，宽度 = (hi-lo)*100。
    mid 用两腿 best bid/ask 的实时中价（与 scanner 同口径）。
    """
    import scanner
    sp = raw.get('scoring_params') or {}
    base = float(sp.get('baseline_total_spread_cents') or 0)
    mult = float(sp.get('settlement_band_multiplier') or 1)
    if not base:
        return None, '缺 baseline_total_spread_cents'
    book = hl_info({'type': 'l2Book', 'coin': f'#{int(outcome_id) * 10}'})
    if not isinstance(book, dict) or book.get('__error__'):
        return None, 'l2Book 查询失败'
    levels = book.get('levels') or [[], []]
    if not levels[0] or not levels[1]:
        return None, 'l2Book 盘口为空'
    bb = float(levels[0][0]['px'])
    ba = float(levels[1][0]['px'])
    mid = (bb + ba) / 2
    lo, hi, _ = scanner.band_of(mid, base, mult)
    return (hi - lo) * 100, f'band_of(mid={mid:.5f}, base={base:g}, mult={mult:g})'


def build_candidate(outcome_id, meta_by_id, leaves, cfg, now=None):
    """采集一个候选的**完整**字段（缺任一必需字段 → 返回 (None, 原因)）。

    只复用现有逻辑：
      - 时间：executor_v2.settlement_time() / sports_schedule() / parse_time()
      - 带宽：scanner.band_of() + scoring_params
      - 最差单步：recentTrades 相邻成交
      - asset_ids：100_000_000 + oid*10 + side（见 v2_safety.candidate_reason 断言）

    `leaves` 是 `fetch_incentive_leaves()` 的结果，由调用方一次取好复用。
    """
    from executor_v2 import parse_time, settlement_time, sports_schedule

    now = now if now is not None else time.time()
    raw = (leaves or {}).get(str(outcome_id))
    if raw is None:
        return None, f'incentives 中找不到 outcome_id={outcome_id}'
    meta = meta_by_id.get(str(outcome_id)) or {}

    # --- 时间 ---
    settle, settle_src = settlement_time(raw, meta)
    sched = sports_schedule(meta)
    if sched:
        # 体育盘：清仓截止 = scheduledStart − pre_game_clear_seconds（B 方案）。
        # incentive_end_time 恒等于 scheduledStart+168h，不能当可交易截止。
        gate_epoch = sched['scheduledStart']
        time_note = 'sports:clearing_deadline'
    else:
        gate_epoch = settle
        time_note = settle_src
    if gate_epoch is None:
        return None, f'无法确定时间闸门（{settle_src}）'

    # event_end_time：赛事/事件结束 epoch。体育盘用开赛时间（与现有 3 个候选一致，
    # 可交叉核对：20033 的 event_end_time=1793668500 恰为 scheduledStart）。
    event_end = sched['scheduledStart'] if sched else parse_time(
        raw.get('event_end_time') or meta.get('event_end_time'))
    if event_end is None:
        return None, 'event_end_time 不可得'

    incentive_end = parse_time(raw.get('incentive_end_time'))
    if incentive_end is None:
        return None, 'incentive_end_time 不可得'

    # --- 带宽 / 最差单步 / 安全证据 ---
    band, band_note = band_width_cents_for(raw, outcome_id)
    if band is None:
        return None, f'带宽不可得: {band_note}'
    step, step_note = worst_step_cents(outcome_id)
    if step is None or step <= 0:
        return None, f'最差单步不可证: {step_note}'
    ratio = band / step
    from executor_v2 import SAFETY_MULT_MIN
    safety_evidence = (
        f'计分带宽 {band:.4f}c ÷ 近期最差单步 {step:.4f}c = {ratio:.2f}x'
        f'（门槛 {SAFETY_MULT_MIN}）；{step_note}；带宽来源 {band_note}')

    sp = raw.get('scoring_params') or {}
    candidate = {
        'outcome_id': int(outcome_id),
        'source': {
            'settlement_time': settle,
            'reward_amount_usdc': str(raw.get('reward_amount_usdc') or '0'),
            'incentive_status': raw.get('incentive_status'),
            'hyperliquid_outcome_id': int(outcome_id),
        },
        'meta': {'name': meta.get('name'), 'description': meta.get('description')},
        'incentive_end_time': incentive_end,
        'event_end_time': event_end,
        'band_width_cents': round(band, 4),
        'worst_step_cents': round(step, 4),
        'safety_evidence': safety_evidence,
        # 安全数据只对本次采集有效；takeaway：不允许它长期当作「历史已验证」。
        'safety_valid_until': min(incentive_end, now + 24 * 3600),
        'sdk_limits': {
            'verified': True,
            # 该规则由 v2_safety.candidate_reason() 硬断言，实测 3/3 候选吻合。
            'evidence': 'asset_ids = 100_000_000 + outcome_id*10 + side（v2_safety 硬断言，实测3/3）',
            'min_shares': 1,
            'min_notional_per_leg': 1,
            # sz_decimals=2：沿用旧实验实盘验证的精度（executor_v2 注入 SDK 用）
            'sz_decimals': 2,
            'asset_ids': [100_000_000 + int(outcome_id) * 10 + side for side in (0, 1)],
        },
        '_build_note': {
            'time_basis': time_note,
            'scoring_params': {k: sp.get(k) for k in
                               ('baseline_total_spread_cents', 'settlement_band_multiplier')},
        },
    }
    return candidate, None


def strip_private(candidate):
    """落盘前剥掉以 _ 开头的内部排查字段（授权文件只放正式字段）。"""
    return {k: v for k, v in candidate.items() if not k.startswith('_')}


# ---------------------------------------------------------------- 前置检查

def _shim(state):
    """v2_safety.unresolved() 只要 ex.state；用轻量 shim 避免构造完整 Executor。"""
    from types import SimpleNamespace
    return SimpleNamespace(state=state, now=time.time)


def check_merge_pending(state):
    """检查 1：无在途 merge。任一市场 merge_pending 非空 → 阻断。

    重启会打断 merge 的成交归属（merge_pending 是 ack 前的唯一凭据）。
    """
    bad = {oid: ms.get('merge_pending')
           for oid, ms in (state.get('markets') or {}).items()
           if isinstance(ms, dict) and ms.get('merge_pending')}
    if bad:
        return False, f'有 {len(bad)} 个市场存在在途 merge（待成交归属）: {sorted(bad)}'
    return True, '无在途 merge'


def check_unresolved(state):
    """检查 2：无未了结意图（unknown / awaiting_fill）。

    复用 v2_safety.unresolved()，与运行时口径完全一致。
    """
    from v2_safety import unresolved
    if unresolved(_shim(state)):
        pend = {k: v.get('status') for k, v in (state.get('intents') or {}).items()
                if isinstance(v, dict) and v.get('status') in ('unknown', 'awaiting_fill')}
        return False, f'有 {len(pend)} 条未了结意图: {pend}'
    return True, '无未了结意图'


def check_ownership(state):
    """检查 3：归属已知。ownership_unknown=True 时不许重启。"""
    if state.get('ownership_unknown'):
        return False, 'ownership_unknown=True（有无法归属的成交/挂单）'
    return True, '归属已知'


def check_removal_safe(state, old_ids, new_ids):
    """检查 4：不得把仍有持仓/挂单的市场踢出候选。

    移出一个市场 = executor 不再加载它的元数据与 asset_ids。虽有
    `c is None` 分支能 merge/unwind 已配对仓，但那是「事后补救」路径；
    自动流程不该主动制造这种状态，故直接阻断。
    """
    removed = set(map(str, old_ids)) - set(map(str, new_ids))
    conflicts = {}
    for oid in removed:
        ms = (state.get('markets') or {}).get(oid) or {}
        pos = {s: q for s, q in (ms.get('pos') or {}).items() if float(q or 0) > 0}
        orders = ms.get('orders') or {}
        remote = [o for o in (state.get('remote_orders') or [])
                  if str(o.get('coin', ''))[1:].isdigit()
                  and str(int(str(o['coin'])[1:]) // 10) == oid]
        if pos or orders or remote:
            conflicts[oid] = {'pos': pos, 'local_orders': len(orders),
                              'remote_orders': len(remote)}
    if conflicts:
        return False, f'要移出的市场仍有持仓/挂单，禁止踢出候选: {conflicts}'
    if removed:
        return True, f'移出 {sorted(removed)} 个市场（均无持仓无挂单）'
    return True, '无市场被移出'


def check_material_diff(state, old_candidates, new_candidates):
    """检查 5：新旧候选有实质差异，完全相同就不重启。

    比较「正式字段」（剥掉 _ 前缀），顺序无关。
    返回 (ok, detail)：ok=False 表示「无需动作」，**不是**故障
    （调用方应把它当 skip 而不是 block）。
    """
    def key(c):
        return json.dumps(strip_private(c), sort_keys=True, separators=(',', ':'),
                          ensure_ascii=False)
    old_set = sorted(key(c) for c in (old_candidates or []))
    new_set = sorted(key(c) for c in (new_candidates or []))
    if old_set == new_set:
        return False, '新旧候选完全一致，无需重启'
    old_ids = sorted(int(c['outcome_id']) for c in (old_candidates or []))
    new_ids = sorted(int(c['outcome_id']) for c in (new_candidates or []))
    if old_ids == new_ids:
        return True, f'候选 outcome 集合不变 {new_ids}，但字段有变化（会重建指纹）'
    return True, f'候选集合变化 {old_ids} → {new_ids}'


def check_ledger_identity(base, state, prospective_auth):
    """检查 6（硬阻断）：账本实验身份不允许随候选组变化。

    见模块 docstring。`ledger.Ledger.bind_experiment()` 用字面相等的
    canonical(identity) 比较，identity 里含 `markets` 与
    `authorization_fingerprint`；换候选后两者都变 → mismatch。

    这里**主动复现**该比较（只读打开账本，不写）：拿账本里已有的 identity
    与「按新候选算出的 identity」比对。读不到 identity 时 fail-closed。
    """
    import sqlite3
    from v2_safety import fingerprint

    db = base / 'v2_experiment_ledger.sqlite3'
    if not db.exists():
        return True, '本路径无账本（首次激活前），不涉及身份变更'
    try:
        con = sqlite3.connect(f'file:{db}?mode=ro', uri=True)
        try:
            row = con.execute(
                "SELECT value FROM metadata WHERE name='experiment_identity'").fetchone()
        finally:
            con.close()
    except Exception as exc:                # noqa: BLE001
        return False, f'账本身份不可读（fail-closed）: {exc}'
    if not row:
        return True, '账本尚未绑定实验身份'

    bound = json.loads(row[0])
    # 按 bind_ledger 的口径复算会变的三项
    new_markets = sorted(str(c['outcome_id'])
                         for c in (prospective_auth.get('candidates') or []))
    new_fp = fingerprint(prospective_auth)
    changed = []
    if sorted(bound.get('markets') or []) != new_markets:
        changed.append(f'markets {sorted(bound.get("markets") or [])} → {new_markets}')
    if bound.get('authorization_fingerprint') != new_fp:
        changed.append('authorization_fingerprint 变化')
    cfg = read_json(base / 'config.json')
    if bound.get('config_fingerprint') != fingerprint(cfg):
        changed.append('config_fingerprint 与当前 config.json 不一致')
    # experiment_start_ms / opening_baseline 是期初证据，切换不改它；
    # 但若 state 已被重置到新实验，这里也要提示。
    exp_id = (prospective_auth or {}).get('experiment_id')
    if exp_id and bound.get('experiment_id') and bound['experiment_id'] != exp_id:
        changed.append(f'experiment_id {bound["experiment_id"]} → {exp_id}')
    if changed:
        return False, ('账本实验身份与新候选冲突，重启必然失败：'
                       + '；'.join(changed)
                       + '。ledger.bind_experiment() 要求 identity 字面相等；'
                         '换候选会导致 build_live 抛 LiveAdapterError、'
                         '即使绕过也会让 collect_fills 每轮失败 → ledger_known 永久 False → 无法开仓。'
                         '需改为「新 experiment_id + 新账本」，或调整 bind_ledger 身份口径。')
    return True, '账本实验身份与新候选一致'


def preflight(base, state, old_auth, old_candidates, new_candidates, *,
              allow_ledger_identity_change=False):
    """跑全部前置检查。

    返回 (verdict, checks, reasons)，verdict ∈ {'proceed','skip','block'}：
      - 'skip'  ：本轮不需要动作（如新旧候选完全一致），exit 0
      - 'block' ：需要人工介入（在途 merge / 未了结意图 / 持仓冲突 / 账本身份），exit 2
      - 'proceed'：可以切换

    注意 `material_diff` 的 ok=False 语义是「无需重启」，属 skip 而非失败，
    因此单独归类，不并入 blocking。
    """
    checks = []
    checks.append(('merge_pending', *check_merge_pending(state)))
    checks.append(('unresolved', *check_unresolved(state)))
    checks.append(('ownership', *check_ownership(state)))
    checks.append(('removal_safe', *check_removal_safe(
        state, [c['outcome_id'] for c in old_candidates or []],
        [c['outcome_id'] for c in new_candidates or []])))
    diff_ok, diff_detail = check_material_diff(state, old_candidates, new_candidates)
    if allow_ledger_identity_change:
        checks.append(('ledger_identity', True,
                       '已显式 --allow-ledger-identity-change（危险，需自知后果）'))
    else:
        # 按 apply_switch 的写法复算「将来会被写下的 auth」，再比账本身份
        prospective = dict(old_auth or {})
        prospective['candidates'] = [strip_private(c) for c in new_candidates]
        checks.append(('ledger_identity',
                       *check_ledger_identity(base, state, prospective)))

    blocking = [f'{name}: {detail}' for name, ok, detail in checks if not ok]
    if blocking:
        return 'block', checks, blocking
    if not diff_ok:
        return 'skip', checks, [diff_detail]
    return 'proceed', checks, []


# ---------------------------------------------------------------- 原子写

def backup_files(base, files):
    """带时间戳备份。返回 {原名: 备份路径}；任一失败则整体失败。"""
    stamp = datetime.now(BJT).strftime('%Y%m%dT%H%M%S')
    outdir = base / 'logs' / 'switch_backups' / stamp
    outdir.mkdir(parents=True, exist_ok=True)
    saved = {}
    for name in files:
        src = base / name
        if not src.exists():
            continue
        dst = outdir / name
        shutil.copy2(src, dst)
        saved[name] = dst
    return saved


def atomic_write_json(path, data):
    """写临时文件 + fsync + os.replace（原子替换，不产生半截文件）。"""
    path = Path(path)
    stage = path.with_name(path.name + '.switching')
    with stage.open('w') as f:
        json.dump(data, f, ensure_ascii=False, indent=1)
        f.flush()
        import os
        os.fsync(f.fileno())
    import os
    os.replace(stage, path)


# ---------------------------------------------------------------- 切换主流程

def plan_switch(base, scan=None):
    """只读：算出「应该切成什么」，不发写操作。给 dry-run 和 scan_6h 用。

    `scan` 可传入已跑好的 scanner.scan() 结果，避免重复扫描（每次都是一次
    完整 incentives 拉取 + 逐市场盘口查询，很贵）。
    """
    import scanner
    import v2_safety as safe
    import executor_v2 as ev

    cfg, auth, candidates, issues = safe.load_inputs(base)
    if cfg.get('dynamic_candidates_enabled'):
        return {'verdict': 'skip', 'reasons': ['C动态增补由实盘主循环执行；保留历史管理范围，不整批切换'],
                'exit': EXIT_OK}
    if auth is None:
        return {'verdict': 'block', 'reasons': ['缺独立v2候选授权文件，等待人工选择'],
                'exit': EXIT_HUMAN}
    if issues:
        return {'verdict': 'block', 'reasons': issues, 'exit': EXIT_HUMAN}

    scan = scan if scan is not None else scanner.scan(cfg=cfg)
    if scan.get('error'):
        return {'verdict': 'failed', 'reasons': ['扫描失败: ' + scan['error']],
                'exit': EXIT_FAILED}
    picked = scan.get('picked') or []
    if not picked:
        return {'verdict': 'skip', 'skipped': True,
                'reasons': [f"本轮 0 个合格市场（通过 {scan.get('passed')}）"],
                'scan': scan, 'exit': EXIT_OK}

    leaves, leaves_err = fetch_incentive_leaves()
    if leaves is None:
        return {'verdict': 'failed',
                'reasons': ['incentives 拉取失败: ' + str(leaves_err)],
                'exit': EXIT_FAILED}
    meta_by_id = fetch_outcome_meta()
    built, failed = [], []
    for row in picked:
        oid = int(row['outcome_id'])
        cand, err = build_candidate(oid, meta_by_id, leaves, cfg)
        if cand is None:
            failed.append((oid, err))
            continue
        # 用真实 candidate_reason 复核（复用运行时口径，不自创准入）
        reason = safe.candidate_reason(cand, time.time(), cfg)
        if reason:
            failed.append((oid, f'candidate_reason 不通过: {reason}'))
            continue
        built.append(cand)

    if not built:
        # 扫到市场但字段/复核全部没通过 → 不能切成空清单（授权必须有候选）
        return {'verdict': 'block',
                'reasons': [f'扫到 {len(picked)} 个市场但无一通过字段采集/复核'] +
                           [f'{oid}: {err}' for oid, err in failed],
                'failed': failed, 'scan': scan, 'exit': EXIT_HUMAN}

    state = read_state(base)
    verdict, checks, reasons = preflight(base, state, auth, candidates, built)
    return {'verdict': verdict, 'checks': checks, 'reasons': reasons,
            'built': built, 'failed': failed, 'scan': scan, 'old': candidates,
            'auth': auth, 'cfg': cfg,
            'exit': EXIT_OK if verdict in ('proceed', 'skip') else EXIT_HUMAN}


def read_state(base):
    """只读 state。用 v2_persistence.read_last 保持与运行时同口径（含大小上限）。"""
    import v2_persistence
    path = base / 'v2_experiment_state.jsonl'
    if not path.exists():
        return {}
    try:
        return v2_persistence.read_last(path)
    except Exception as exc:                 # noqa: BLE001
        # fail-closed：读不到 state = 无法证明安全，抛给调用方跳过本轮
        raise RuntimeError(f'state 不可读，拒绝切换: {exc}') from exc


def apply_switch(base, plan, *, restart=True, service=SERVICE, wait_seconds=10,
                 run=subprocess.run):
    """执行切换。仅在 --apply 下被调用。

    顺序（任一步失败 → 回滚）：
      1. 备份 v2_authorization.json + v2_first_activation.json + config.json
      2. 写新 v2_authorization.json（只改 candidates）
      3. 重算指纹，更新 v2_first_activation.json（只改两个指纹字段）
      4. activation_valid() 必须 True（否则回滚）
      5. 同步 state 里的 authorization_fingerprint（否则 build_live 拒绝启动）
      6. 重启服务
      7. 等 10s 读 state：halted=False 且 ledger_known=True
      8. 不通过 → 回滚 + 报警
    """
    import v2_safety as safe

    old_auth = read_json(base / 'v2_authorization.json')
    activation_path = base / 'v2_first_activation.json'
    old_activation = read_json(activation_path)
    cfg = read_json(base / 'config.json')
    if cfg.get('dynamic_candidates_enabled'):
        raise RuntimeError('C动态授权禁止通过整批切换入口改写')
    backups = backup_files(base, ['v2_authorization.json',
                                  'v2_first_activation.json', 'config.json'])
    result = {'backups': {k: str(v) for k, v in backups.items()}, 'steps': []}

    def step(name, ok, detail=''):
        result['steps'].append({'step': name, 'ok': bool(ok), 'detail': detail})
        return ok

    try:
        # 2. 新授权：只改 candidates
        new_auth = dict(old_auth)
        new_auth['candidates'] = [strip_private(c) for c in plan['built']]
        # 自动切换留痕（方案 C：不改写 operator_confirmation 的人工语义）
        log_entry = {'at': int(time.time()), 'at_bjt': bjt_stamp(),
                     'old_outcomes': sorted(int(c['outcome_id']) for c in plan['old']),
                     'new_outcomes': sorted(int(c['outcome_id']) for c in plan['built']),
                     'operator_confirmation_retained': old_activation.get('operator_confirmation')}
        new_auth['auto_switch_log'] = list(old_auth.get('auto_switch_log') or []) + [log_entry]
        atomic_write_json(base / 'v2_authorization.json', new_auth)
        step('write_authorization', True, f"{len(new_auth['candidates'])} 个候选")

        # 3. 重算指纹；保留人工批准字段原义
        new_activation = dict(old_activation)
        new_activation['authorization_fingerprint'] = safe.fingerprint(new_auth)
        new_activation['config_fingerprint'] = safe.fingerprint(cfg)
        atomic_write_json(activation_path, new_activation)
        step('write_activation', True, 'authorization/config 指纹已重算')

        # 4. 激活必须有效
        if not safe.activation_valid(activation_path, cfg, new_auth):
            raise RuntimeError('activation_valid() 返回 False（指纹重建失败）')
        step('activation_valid', True)

        # 5. state 指纹同步（build_live 会校验；不同步则启动即抛）
        state_path = base / 'v2_experiment_state.jsonl'
        state = read_state(base)
        if state:
            state['authorization_fingerprint'] = safe.fingerprint(new_auth)
            state['config_fingerprint'] = safe.fingerprint(cfg)
            import v2_persistence
            v2_persistence.append_record(state_path, state)
            step('sync_state_fingerprint', True)
        else:
            step('sync_state_fingerprint', True, 'state 为空，跳过')

        # 6. 重启
        if restart:
            proc = run(['systemctl', 'restart', service],
                       capture_output=True, text=True, timeout=120)
            if proc.returncode != 0:
                raise RuntimeError(f'systemctl restart 失败: {proc.stderr.strip()}')
            step('restart', True, service)
            time.sleep(wait_seconds)
            st = read_state(base)
            healthy = (st.get('halted') is False and st.get('ledger_known') is True)
            step('post_restart_check', healthy,
                 f"halted={st.get('halted')} ledger_known={st.get('ledger_known')}")
            if not healthy:
                raise RuntimeError('重启后未达到 halted=False 且 ledger_known=True')
        else:
            step('restart', True, '跳过（restart=False）')
        result['ok'] = True
        return result
    except Exception as exc:                 # noqa: BLE001 - 任何失败都要回滚
        result['ok'] = False
        result['error'] = str(exc)
        rollback(base, backups, run=run, restart=restart, service=service)
        result['rolled_back'] = True
        return result


def rollback(base, backups, *, run=subprocess.run, restart=True, service=SERVICE):
    """从备份恢复三个文件；放回后再重启一次让旧授权重新生效。"""
    for name, src in backups.items():
        dst = base / name
        if Path(src).exists():
            shutil.copy2(src, dst)
    if restart:
        try:
            run(['systemctl', 'restart', service],
                capture_output=True, text=True, timeout=120)
        except Exception:                    # noqa: BLE001
            pass


# ---------------------------------------------------------------- CLI

def main(argv=None):
    ap = argparse.ArgumentParser(description='HIP-4 候选自动切换（默认 dry-run）')
    ap.add_argument('--apply', action='store_true',
                    help='真正写入授权文件并重启（默认只做前置检查与计划打印）')
    ap.add_argument('--no-restart', action='store_true',
                    help='与 --apply 同用：写文件但不重启服务（测试/人工接管用）')
    ap.add_argument('--allow-ledger-identity-change', action='store_true',
                    help='危险：跳过账本身份硬阻断（仅在已确认账本可换绑时使用）')
    ap.add_argument('--service', default=SERVICE)
    ap.add_argument('--base', type=Path, default=BASE)
    args = ap.parse_args(argv)
    base = args.base.resolve()

    print(f'=== 候选切换 {bjt_stamp()}（北京）===')
    if not args.apply:
        print('[dry-run] 不做任何写入、不重启\n')

    try:
        plan = plan_switch(base)
    except Exception as exc:                 # noqa: BLE001
        print(f'❌ 计划阶段失败: {exc}')
        return EXIT_HUMAN

    for oid, err in plan.get('failed') or []:
        print(f'  ⚠️ {oid} 字段采集失败: {err}')
    for name, ok, detail in plan.get('checks') or []:
        print(f"  {'✅' if ok else '⛔'} {name}: {detail}")

    verdict = plan.get('verdict')
    if verdict == 'failed':
        print('\n❌ 执行失败')
        for r in plan.get('reasons') or []:
            print(f'   - {r}')
        return plan.get('exit', EXIT_FAILED)
    if verdict == 'block':
        print('\n⛔ 跳过本轮（需要人工介入）')
        for b in plan.get('reasons') or []:
            print(f'   - {b}')
        return plan.get('exit', EXIT_HUMAN)
    if verdict == 'skip':
        print(f"\n✅ {plan['reasons'][0] if plan.get('reasons') else '无需动作'}；不切换")
        return EXIT_OK
    if verdict != 'proceed':
        print(f"\n❌ 未知判定: {verdict}")
        return EXIT_FAILED

    print(f"\n计划：{sorted(int(c['outcome_id']) for c in plan['old'])}"
          f" → {sorted(int(c['outcome_id']) for c in plan['built'])}")
    for c in plan['built']:
        print(f"  + {c['outcome_id']}: band={c['band_width_cents']}c "
              f"step={c['worst_step_cents']}c asset_ids={c['sdk_limits']['asset_ids']}")
        print(f"    {c['safety_evidence']}")

    if not args.apply:
        print('\n[dry-run] 未写入任何文件。确认无误后加 --apply 执行。')
        return EXIT_OK

    out = apply_switch(base, plan, restart=not args.no_restart, service=args.service)
    for s in out['steps']:
        print(f"  {'✅' if s['ok'] else '❌'} {s['step']}: {s['detail']}")
    if out.get('ok'):
        print('\n✅ 切换完成')
        return EXIT_OK
    print(f"\n❌ 切换失败并已回滚: {out.get('error')}")
    return EXIT_HUMAN


if __name__ == '__main__':
    sys.exit(main())
