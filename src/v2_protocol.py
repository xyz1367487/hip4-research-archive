"""Bounded read scheduling and exact Outcome wire rules; no credentials."""
from collections import deque
from decimal import Decimal, ROUND_FLOOR, ROUND_CEILING
import math
import json
import sys
import time
from contextlib import contextmanager
from contextvars import ContextVar
from functools import wraps
from threading import RLock

_SCAN_BUDGET = ContextVar('scan_weight_budget', default=None)
# 本轮扫描已扣权重与「是否已发出过请求」，供 note_discovery_cost 自适应让路量。
_SCAN_SPENT = ContextVar('scan_weight_spent', default=None)

# 2026-11-04：发现扫描的容量（权重），让 6 小时一次的扫描不再被运行时稳态读饿死。
#
# 依据实测：一次真实扫描 43 次 /info 合计 158 权重
# （public-research-evidence/扫描复验说明.md），按候选成本推算 4 个候选约 282，
# 所以 240 是**保底容量**（不是硬天花板，超出部分由让路 + 有界等待补齐）。
#
# ## 这 240 从哪来：从「后台额度」里**临时**让出，绝不动「风控预留」
#
# 上一版把这 240 从 reserve 里划，风控预留被压到 60：
# 撤单可用 304→64、合并预留 len 284→44（审计 F1，实测）。那是拿风控额度换
# 扫描额度，本版撤回。正确的分解是**瞬时让出**，不是永久削减：
#
#   风控 reserve            = 300   ← 任何时刻都不被扫描占用
#   后台 + 扫描合计上限      = limit - reserve = 900   ← 硬约束（风控才拿得到 300）
#     扫描保底（真正的扫描窗口内）= 240
#     后台（同一窗口内让到）      = 900 - 240 = 660
#   全局硬顶                = 1200（官方 1200/min 永不击穿）
#
# 后台 900 只在**没有扫描在跑**时使用；扫描真在跑的那一段（每 6 小时一轮）
# 后台临时让到 660。让路的**时长**由下面两道硬上限约束：单次最多 360 秒，
# 且任意 60 分钟内累计不超过 600 秒——不再是「只要扫描还在发请求就一直让」。
# 审计实测稳态读 60s 峰值 896，若把后台**永久**压到 660 则 100% 的窗口会被拒
# ——所以只能是临时让出，不能是永久削减。（注：「68% 的窗口会被拒」这个数字
# 经复核无法复现，已撤回；正确表述是：可成窗样本 100% 都超过 660，
# 峰值 914/920/930。）
#
# 于是风控 essential/priority 的可用量在任何时刻（含扫描期间）都
# 不低于基线：1200 - 900 = 300，对应撤单 ~304 次、合并预留 len ~284。
#
# **刻意不写进 config.json**：config 参与 fingerprint(cfg)，
# 改配置会让 authorization/activation 三层指纹失配并触发 halt。
DISCOVERY_RESERVE = 240

# 扫描每窗口可用量的**上限**。审计 N2：让路量原本可以一路棘轮到共享池
# （900），于是后台在高负载轮次被压到 160、理论上可到 0，接近停摆。
#
# 480 = 实测最大真实需求（43 次 /info / 158 权重；4 候选约 282）的 1.7 倍，
# 仍足以让 1200 权重的大轮次在 3 个窗口内走完（480+480+240，两次窗口等待
# 共约 120s < 一轮等待预算 240s，见 test_c_scan_starvation 的 F2 用例）。
# 因此后台上限的**下限**变成 900-480=420，而不是 0。
DISCOVERY_NEED_MAX = 480

# 一轮扫描「结束之后」继续让路的尾巴。注意这**不是**让路时长上界：
# 每个扫描请求都会续期，所以单靠它算不出上界（审计 N1 实测可达 374.8s）。
# 真正的上界是下面两道：单次让路上限 + 任意一小时内的让路总时长上限。
DISCOVERY_YIELD_SECONDS = 180.0

# 单次让路的绝对上限（自本轮建立租约起算，用注入时钟）。续期也不能越过它：
# 后台因此最多被压住 DISCOVERY_YIELD_MAX_SECONDS（6 分钟），
# 而不是「最后一个请求 + 180 秒」这种依扫描长度而变的量。
DISCOVERY_YIELD_MAX_SECONDS = 360.0

# 任意滚动 60 分钟内、所有让路的总时长上限（600s = 10% 的时间）。
# 这是「后台吞吐不能被长期削弱」的第二道闸：即使扫描轮次因为退避重试而
# 一轮接一轮地跑，让路也不会连续占满整个小时。
# 长期上限由此可算：窗口内最多削 26%（896 需求只服务 660），
# 而让路至多占 600/3600 的时间 → 长期吞吐损失 <= 26% x 1/6 ≈ 4.3%。
# 生产实际是每 6 小时一轮、每轮让路 240~300s → 长期损失约 0.3%。
DISCOVERY_YIELD_HOURLY_SECONDS = 600.0

# 上面那道「滚动 60 分钟」的窗口长度。
DISCOVERY_YIELD_WINDOW_SECONDS = 3600.0

# 一轮扫描累计最多可以「等」多久（秒）。等待是审计 F2 的正解：
# 扫描跑在后台守护线程（candidate-discovery-readonly），等得起；而把 240 当成
# 硬天花板时，一轮要 13 个请求（260 权重）就**永远**走不完——每轮延期、进度清零、
# 资格静默冻结、scan_ok 恒为 True，外部完全看不出异常。
# 现在 240 只是**让路量**（保底），不是扫描的上限：扫描的上限是整个共享池，
# 跨 60s 窗口不够就等到窗口释放（总等待有上限），等不到才退回延期语义。
# 上限同时保证「让路」始终是临时的，不会无限期压住后台稳态读。
DISCOVERY_SCAN_WAIT_SECONDS = 240.0

# 等待时的探测粒度：每次最多睡这么久再重新取时间。
_WAIT_PROBE_SECONDS = 0.2


@contextmanager
def scan_budget(budget, wait_seconds=None):
    """一轮扫描的预算作用域。进入时建立让路租约，退出时回写本轮成本。

    **一轮总共**可以「等」wait_seconds（默认 DISCOVERY_SCAN_WAIT_SECONDS）：
    一轮扫描因此能跨多个 60s 窗口推进——这是审计 F2 的解，而不是把 240 当硬顶。
    等待预算是**整轮共享**的（不是每请求各一份），所以一轮的时长上界是
    「正常耗时 + 等待预算」，不会因为请求多就无限期压住后台稳态读。
    """
    now = budget.now() if budget is not None and hasattr(budget, 'now') else None
    limit = (DISCOVERY_SCAN_WAIT_SECONDS if wait_seconds is None
             else max(0.0, float(wait_seconds)))
    # [已扣权重, 是否已发出过请求, 整轮等待截止时刻, 已发出请求数]
    state = [0, False, None if now is None else now + limit, 0]
    _scan_budget_token = _SCAN_BUDGET.set(budget)
    _scan_spent_token = _SCAN_SPENT.set(state)
    began = bool(budget is not None and hasattr(budget, 'begin_discovery')
                 and budget.begin_discovery())
    try:
        yield
    finally:
        # 本轮是否正常走完：异常逃出 with 块即视为「没走完，真实需求更大」。
        incomplete = sys.exc_info()[0] is not None
        used, requested = state[0], state[3]
        if began:
            if hasattr(budget, 'note_discovery_cost'):
                # 回写本轮成本：下一轮的让路量据此放宽，
                # 避免「需求上涨 → 每轮延期 → 资格静默冻结」（审计 F2）。
                budget.note_discovery_cost(used, incomplete=incomplete,
                                           requested=requested)
            budget.end_discovery()
        _SCAN_SPENT.reset(_scan_spent_token)
        _SCAN_BUDGET.reset(_scan_budget_token)


def charge_scan_http(url, payload, wait_seconds=None):
    budget = _SCAN_BUDGET.get()
    if budget is not None and url == 'https://api.hyperliquid.xyz/info':
        kind = payload['type']
        weight = 2 if kind == 'l2Book' else 20
        state = _SCAN_SPENT.get()
        wait = wait_seconds
        if wait is None and state is not None and state[2] is not None:
            # 用整轮剩余的等待预算，而不是每请求各发一份。
            wait = max(0.0, state[2] - budget.now())
        # 扫描请求走有界等待：窗口不足就等到释放，而不是把 240 当成硬天花板
        # 让一轮扫描永远走不完（审计 F2）。BudgetUnavailable 仍可能抛出
        # （整轮等待预算耗尽 / 时钟不推进），调用方按「延期」处理。
        if hasattr(budget, 'charge_discovery'):
            budget.charge_discovery(weight, kind=kind, budget_wait=wait)
        else:                                  # 旧签名对象（测试替身）兼容
            budget.charge(weight, kind=kind, discovery=True)
        if state is not None:
            state[0] += weight
            state[1] = True
            state[3] += 1


def _locked(method):
    @wraps(method)
    def call(self, *args, **kwargs):
        with self._lock:
            return method(self, *args, **kwargs)
    return call

MINIMUM_SOURCE = 'https://raw.githubusercontent.com/Outcome-xyz/hip4/main/src/adapter/hyperliquid/pricing.ts'
MINIMUM_DOC = 'https://docs.outcome.xyz/sdk/reference/trading-adapter'


class BudgetUnavailable(RuntimeError):
    """Admission deferred: no request was sent. retry_at uses the injected clock."""
    def __init__(self, message='REST预算等待', retry_at=None):
        super().__init__(message)
        self.retry_at = retry_at


class WeightBudget:
    'Rolling-window admission with a dedicated reserve for risk management.\n\nPriority cancellation, exits and verification may use the reserve. Background\nand discovery traffic share only limit minus reserve. During a discovery\nlease, background admission yields within that shared pool; outside the lease\nit uses the normal shared allowance. The risk reserve remains protected.\n\nLease renewal is bounded by DISCOVERY_YIELD_MAX_SECONDS and the rolling\nhourly allowance DISCOVERY_YIELD_HOURLY_SECONDS. yield_used reports usage.\nDiscovery requests may wait across windows up to DISCOVERY_SCAN_WAIT_SECONDS.\nObserved discovery cost adapts the next allowance, capped by DISCOVERY_NEED_MAX.\nA zero discovery_reserve retains the background admission semantics.\nready_at computes the next rolling-window release without sleeping.'
    def __init__(self, now, limit=600, reserve=200, essential_types=(),
                 discovery_reserve=0, sleep=None):
        if not 1 <= limit <= 1200:  # 2026-10-30 方案④：官方限额实为 1200/min
            raise ValueError('REST budget must be in 1..1200')
        self.now, self.limit, self.events = now, limit, deque()
        self._lock = RLock()
        self._priority_context = ContextVar('weight_budget_priority', default=0)
        self.reserve = max(0, min(int(reserve), limit - 1))
        # 让路量只能落在「后台 + 扫描」的共享池（limit - reserve）之内：
        # 这样风控预留 reserve 一点也动不到。
        self.discovery_reserve = max(0, min(int(discovery_reserve),
                                            limit - self.reserve))
        self._disc = deque()          # 窗口内 discovery 事件的影子副本
        self._discovery_until = None  # 让路租约到期时刻（用注入时钟）
        # 让路时长的两道硬上限（审计 N1）：本轮的起点，以及滚动一小时的账。
        self._discovery_lease_start = None   # 本轮首次建立租约的时刻
        self._yield_open = None              # 当前进行中的让路段起点
        self._yield_closed = deque()         # 已结束的让路段 (start, end)
        # 上一轮实测/推断的一轮需求。夹在 [discovery_reserve, DISCOVERY_NEED_MAX]，
        # 后者是审计 N2 要求的上限：没有它就会单向棘轮到共享池，把后台压停。
        self._disc_need = 0
        self._sleep = sleep or time.sleep
        self.essential_types = frozenset(essential_types)
        self.denied = False           # 只反映「运行时自身」的拒绝，不含扫描/让路
        self.total_denied = 0
        self.discovery_denied = 0     # 审计用：扫描被拒次数，与 denied 解耦
        self.discovery_yield_denied = 0   # 审计用：因让路被拒的后台请求
        self.discovery_rounds = 0     # 让路租约开启次数
        # 最近一轮扫描的实际开销与完成度。审计 F3：上一版把「中途被拒」也写成
        # 「一个请求都没发出」，与实际不符；这里如实记录已发请求数与已扣权重，
        # 让延期日志能区分「首个请求就被拒」和「跑到一半没跑完」。
        self.discovery_last_round = {'spent': 0, 'requested': 0,
                                     'completed': False}
        self.total_charged = 0
        self.discovery_charged = 0
        self.stats_by_kind = {}

    @property
    def _priority(self):
        return self._priority_context.get()

    @_priority.setter
    def _priority(self, value):
        self._priority_context.set(value)

    @contextmanager
    def priority(self):
        self._priority = getattr(self, '_priority', 0) + 1
        try:
            yield
        finally:
            self._priority -= 1

    # ---- 分层上限 -----------------------------------------------------
    def _shared_cap(self):
        """后台 + 扫描 的共享上限。风控预留不在此池内，故风控恒得 reserve。"""
        return self.limit - self.reserve

    def _lease_active(self, at=None):
        """当前（或 at 时刻）是否处于扫描让路租约内。"""
        at = self.now() if at is None else at
        return (self.discovery_reserve > 0 and self._discovery_until is not None
                and at < self._discovery_until)

    def _discovery_cap(self, at):
        """扫描每窗口可用量：保底 240，随上一轮实测需求放宽，但**有上限**。

        上限 `DISCOVERY_NEED_MAX`（480）是审计 N2 的要求：没有它时
        `_disc_need` 会棘轮到共享池（900），后台被压到 160、理论可到 0，
        高负载轮次后台接近停摆。夹到 480 后后台上限的**下限**是 900-480=420。
        """
        if not self._lease_active(at):
            return self.discovery_reserve
        need = min(max(self.discovery_reserve, self._disc_need), DISCOVERY_NEED_MAX)
        return min(self._shared_cap(), need)

    def _background_cap(self, at, disc_used):
        """后台每窗口可用量。租约期内让路，租约期外是完整的 900。

        让路量同样夹到 `DISCOVERY_NEED_MAX`（480），所以租约期内后台
        即使在高负载轮次也保底 900-480=420，不会停摆（审计 N2）。
        """
        shared = self._shared_cap()
        if self._lease_active(at):
            yield_now = min(max(self.discovery_reserve, disc_used), DISCOVERY_NEED_MAX)
            return max(0, shared - yield_now)
        return shared

    def _close_yield(self):
        """把进行中的让路段落记为「已发生」，结束于租约到期或当前时刻（取较早者）。

        会计口径必须是**真实让出的时长**，不是「发放出去的地平线」：
        续期只是把到期时刻往后推，重复续期不能重复计费，否则小时预算会被
        几次续期瞬间吃光，让路反而提前失效。
        """
        if self._yield_open is None:
            return
        end = self.now()
        if self._discovery_until is not None and self._discovery_until < end:
            end = self._discovery_until
        if end > self._yield_open:
            self._yield_closed.append((self._yield_open, end))
        self._yield_open = None

    def _yield_closed_used(self, cutoff):
        """滚动窗口内、**已结束**的让路总时长。"""
        while self._yield_closed and self._yield_closed[0][1] <= cutoff:
            self._yield_closed.popleft()
        return sum(max(0.0, e - max(s, cutoff)) for s, e in self._yield_closed)

    @_locked
    def yield_used(self, now=None):
        """滚动 3600s 窗口内已让出的秒数（进行中的那一段只算到此刻）。

        运维可观测量：与 `DISCOVERY_YIELD_HOURLY_SECONDS`（600）对照，
        就能看出「后台上限被压低」这件事本小时还剩多少额度。
        """
        now = self.now() if now is None else now
        cutoff = now - DISCOVERY_YIELD_WINDOW_SECONDS
        used = self._yield_closed_used(cutoff)
        if self._yield_open is not None:
            end = min(now, self._discovery_until if self._discovery_until is not None
                      else now)
            used += max(0.0, end - max(self._yield_open, cutoff))
        return used

    # ---- 让路租约 -----------------------------------------------------
    @_locked
    def begin_discovery(self, seconds=None):
        """开启/续期让路租约：租约期内后台临时让出扫描容量。

        返回值表示「让路当前是否生效」：`False` 表示没有额度可让，调用方
        应退回每窗口保底量 `discovery_reserve` 继续推进（后台立刻回到 900）。

        **续期不等于无限延长**——这是审计 N1 的核心。旧实现对每个扫描请求都
        把租约推成 `now + DISCOVERY_YIELD_SECONDS`，于是实际压住后台的时长
        是「最后一个请求 + 180 秒」，随扫描长度漂移（实测 374.8s，
        与文档/注释/测试 docstring 反复声称的 180s 不符）。本版给租约两道
        硬上限，让「后台最多被压住多久」成为可陈述、可断言的事实：

          1. 单轮上限：自本轮首次建立租约起，最多 `DISCOVERY_YIELD_MAX_SECONDS`；
          2. 滚动一小时上限：任何 3600s 窗口内，让路总时长不超过
             `DISCOVERY_YIELD_HOURLY_SECONDS`。

        单轮上限保证「一轮扫描压不住后台超过 6 分钟」；小时上限保证
        「一轮接一轮也压不住整个小时」。两者都只影响让路时长，不动风控预留。
        """
        if self.discovery_reserve <= 0:
            return False
        now = self.now()
        hold = DISCOVERY_YIELD_SECONDS if seconds is None else max(0.0, float(seconds))
        active = self._lease_active(now)
        if active:
            base = self._discovery_until
            open_start = self._yield_open if self._yield_open is not None else now
            start = (self._discovery_lease_start
                     if self._discovery_lease_start is not None else now)
        else:
            # 上一段让路已自然到期：先结账，再开新的一段。
            self._close_yield()
            base = open_start = start = now
        candidate = min(base + hold, start + DISCOVERY_YIELD_MAX_SECONDS)
        # 小时预算：窗口内已结束的让路 + 本轮从 max(open_start, cutoff) 起算的部分
        # 不得超过 DISCOVERY_YIELD_HOURLY_SECONDS。
        cutoff = now - DISCOVERY_YIELD_WINDOW_SECONDS
        closed = self._yield_closed_used(cutoff)
        allowed_end = (max(open_start, cutoff)
                       + (DISCOVERY_YIELD_HOURLY_SECONDS - closed))
        candidate = min(candidate, allowed_end)
        if candidate <= base:
            # 让路预算用尽（或已达单轮上限）：不再延长，已有租约按原到期时刻失效。
            return active
        if not active:
            self.discovery_rounds += 1        # 只统计「新开一轮」，不是每次续期
            self._discovery_lease_start = start
            self._yield_open = open_start
        self._discovery_until = candidate
        return True

    @_locked
    def end_discovery(self):
        """结束让路租约：后台额度立即恢复 limit - reserve，不留任何永久削减。

        已消耗的让路时长**不**退还：它记在滚动一小时的预算里，防止
        「扫描一结束立刻重开租约」绕过小时上限（审计 N1）。
        """
        self._close_yield()
        self._discovery_until = None
        self._discovery_lease_start = None

    @_locked
    def note_discovery_cost(self, weight, incomplete=False, requested=0):
        """回写一轮扫描的成本，让下一轮的让路量与其实际需求匹配（审计 F2）。

        incomplete=True 表示这一轮没走完（被拒/异常）：真实需求**大于**已用掉的量，
        于是按「已用 + 一个让路量」放宽。incomplete=False 表示跑完了，按本轮实测
        用量收敛（允许回落），避免一次尖峰把让路量永久抬高。

        两者都夹在 `[discovery_reserve, DISCOVERY_NEED_MAX]` 之间：

          - 上界是审计 N2 的要求。旧实现夹到 `_shared_cap()`（900），于是
            `incomplete` 连续出现时 `_disc_need` 单向棘轮到 900，
            后台在扫描窗口内被压到 900-900=0（实测最低 160），高负载轮次
            后台接近停摆。夹到 480 后后台上限的下限是 420。
          - 下界是保底量，同时保证「跑完的一轮」把小需求收敛回 240，
            不会被一次尖峰永久抬高。

        因此永远触碰不到风控预留（它也从不越过 `_shared_cap()`）。
        """
        try:
            used = max(0, int(math.ceil(float(weight))))
        except (TypeError, ValueError):
            used = 0
        # 真实需求 = 已用量 + 一个让路量（没跑完时），保证下一轮够用；
        # 每轮最多放宽一个让路量，不会一步跳到整个共享池把后台长期压死。
        if incomplete:
            need = used + self.discovery_reserve
        else:
            need = used
        self._disc_need = min(DISCOVERY_NEED_MAX,
                              self._shared_cap(),
                              max(self.discovery_reserve, need))
        # 如实记录：requested=0 才是「一个请求都没发出」（审计 F3）。
        self.discovery_last_round = {'spent': used, 'requested': int(requested or 0),
                                     'completed': not incomplete}

    # ---- 准入判定 -----------------------------------------------------
    def _prune(self, now):
        while self.events and self.events[0][0] <= now - 60:
            self.events.popleft()
        while self._disc and self._disc[0][0] <= now - 60:
            self._disc.popleft()

    def _window(self, at):
        """at 时刻滚动 60s 窗口内的（总用量, 扫描用量）；后台用量 = 两者之差。"""
        total = sum(w for t, w in self.events if t > at - 60)
        disc = sum(w for t, w in self._disc if t > at - 60)
        return total, disc

    def _path(self, essential, kind, discovery):
        """(路径, 是否扫描请求)。判定依据是「谁发起 + 能否动用风控预留」。"""
        if essential or self._priority or kind in self.essential_types:
            return 'risk', False
        if discovery and self.discovery_reserve > 0:
            return 'disc', True
        return 'bg', bool(discovery)

    def _fits(self, path, weight, at):
        """at 时刻能否再吃下 weight。后台+扫描永远不允许越过 limit-reserve。"""
        total, disc = self._window(at)
        if path == 'risk':
            # 风控可动用全局限额；由于 shared 上限的存在，这里恒有 >= reserve 空间。
            return total + weight <= self.limit
        shared = self._shared_cap()
        if total + weight > shared:
            return False
        if path == 'disc':
            return disc + weight <= self._discovery_cap(at)
        return total - disc + weight <= self._background_cap(at, disc)

    def _cap_for(self, path, at):
        """单请求上限（仅用于拒绝不可能满足的超大请求）。"""
        if path == 'risk':
            return self.limit
        if path == 'disc':
            return min(self._discovery_cap(at), self._shared_cap())
        return self._background_cap(at, self._window(at)[1])

    @_locked
    def ready_at(self, weight, essential=False, kind=None, discovery=False):
        now = self.now()
        self._prune(now)
        path, is_scan = self._path(essential, kind, discovery)
        if is_scan:
            # 扫描请求一落地就建立让路租约：即使调用方没显式 begin_discovery，
            # 扫描也不会退化成「只能抢后台余量」而被饿死。
            self.begin_discovery()
        if weight > min(self._cap_for(path, now), self.limit):
            raise ValueError('single request exceeds REST budget capacity')
        if self._fits(path, weight, now):
            return now
        for at in sorted({t + 60 for t, _ in self.events}):
            if at > now and self._fits(path, weight, at):
                return at
        return now + 60

    @_locked
    def charge(self, weight, essential=False, kind=None, discovery=False,
               count_denial=True):
        """准入并记账。count_denial=False 供 charge_discovery 的等待轮询使用。

        等待轮询每 0.2s 试一次，若每次都记一次拒绝，一次真实延期会写成几百次
        `discovery_denied`（实测：等 60s → discovery_denied=300），
        使「扫描被拒了几次」这个审计量完全失真。等待中的尝试不算拒绝，
        只有最终退回延期的那一刻才算一次（由 charge_discovery 记）。
        """
        path, is_scan = self._path(essential, kind, discovery)
        use_disc = path == 'disc'
        if is_scan:
            self.begin_discovery()
        ready = self.ready_at(weight, essential, kind, discovery)
        if ready > self.now():
            if not count_denial:
                raise BudgetUnavailable(retry_at=ready)
            self.total_denied += 1
            if path == 'risk':
                self.denied = True
            elif is_scan or use_disc:
                # 链路 3 修复：发现线程的延期**不得**写 self.denied。
                # 运行时每 tick 用它写 rest_budget_blocked（LOCKED_FLAGS），
                # 后台扫描无权反向影响资金风控状态。
                # 判定依据是「谁发起的请求」，不是「落在哪个桶」：让路量未配置、
                # 请求回落到后台额度时，扫描的拒绝依旧不许污染风控。
                self.discovery_denied += 1
            elif self._yield_caused(weight):
                # 后台请求只因「给扫描让路」被拒：风控预留一分未动（仍可用 300），
                # 置 denied 会误锁资金风控，故单独计数。
                self.discovery_yield_denied += 1
            else:
                self.denied = True
            raise BudgetUnavailable(retry_at=ready)
        self.record(weight, kind, discovery=use_disc)

    def charge_discovery(self, weight, kind=None, budget_wait=None):
        '扫描专用准入，窗口不足时在配置上限内等待。\n\nBudgetUnavailable 表示请求尚未发出，可稍后恢复。等待期间不持有\n_locked 锁；每次尝试由 charge 单独管理锁，避免阻塞主循环。'
        wait = DISCOVERY_SCAN_WAIT_SECONDS if budget_wait is None else float(budget_wait)
        deadline = self.now() + max(0.0, wait)
        while True:
            try:
                # 等待轮询不记拒绝：只有最终退回延期时才算一次（见下方 except）。
                return self.charge(weight, kind=kind, discovery=True,
                                   count_denial=False)
            except BudgetUnavailable as exc:
                retry = exc.retry_at
                # 等到 retry_at 会超出整轮等待预算 → 退回延期语义，交给调用方
                # （refresh_pool 退避后重试），绝不无限期压住后台稳态读。
                if retry is None or retry > deadline:
                    raise self._note_deferred(exc)
                before = self.now()
                self._sleep(max(0.0, min(retry - before, _WAIT_PROBE_SECONDS)))
                if self.now() <= before:
                    # 时钟不推进（固定时钟的测试环境 / 时钟源异常）：等待无法推进，
                    # 立刻退回延期语义，绝不在此空转。
                    raise self._note_deferred(exc)

    def _note_deferred(self, exc):
        """把「等待用尽、退回延期」记成一次扫描拒绝，然后原样抛回该异常。

        记账口径与 `charge()` 的拒绝分支保持一致：只计入 `total_denied` /
        `discovery_denied`，**绝不**写 `self.denied`（链路 3：后台扫描无权
        影响资金风控标志）。异常本身原样返回，保留其 `retry_at`。
        """
        with self._lock:
            self.total_denied += 1
            self.discovery_denied += 1
        return exc

    def _yield_caused(self, weight):
        """这次后台拒绝是否只是让路造成的（不让路就吃得下）。"""
        now = self.now()
        if not self._lease_active(now):
            return False
        total, disc = self._window(now)
        return total - disc + weight <= self._shared_cap()

    def usable(self, essential=False, kind=None, discovery=False, at=None):
        """窗口内该路径还能吃下多少权重（只读，供断言与看板用）。"""
        with self._lock:
            at = self.now() if at is None else at
            path, _ = self._path(essential, kind, discovery)
            total, disc = self._window(at)
            if path == 'risk':
                return max(0, self.limit - total)
            shared = self._shared_cap()
            if path == 'disc':
                return max(0, min(shared - total,
                                  self._discovery_cap(at) - disc))
            return max(0, min(shared - total,
                              self._background_cap(at, disc) - (total - disc)))

    @_locked
    def record(self, weight, kind=None, discovery=False):
        # Only admitted or already incurred costs belong in charged statistics.
        at = self.now()
        self.events.append((at, weight))
        if discovery:
            self._disc.append((at, weight))
            self.discovery_charged += weight
        st = self.stats_by_kind.setdefault(kind or 'unknown', {'n': 0, 'w': 0})
        st['n'] += 1
        st['w'] += weight
        self.total_charged += weight


class BudgetedInfo:
    def __init__(self, read, budget, fill_cap=2000, fill_reserve_cap=None):
        self.read, self.budget, self.fill_cap = read, budget, fill_cap
        # 2026-11-01：成交查询的**预扣上限**与「覆盖校验阈值」解耦。
        #
        # 实测（3 分钟分类统计，20:40）：userFillsByTime 占预算 65%（720/1100），
        # 单次预扣 120 权重（20 + ceil(2000/20)），而实际窗口只返回 18 笔
        # （6.8 小时、实验起点起算）。每小时白扣约 200 权重，正好挤掉撤单复核。
        #
        # 原设计意图是「发请求前预留最坏响应」（见下方注释），方向正确，
        # 但这里的最坏值应取**本实验窗口的实际可能峰值**，而非全局 2000。
        # 保留 fill_cap=_2000 用于覆盖校验（len(fills) >= 2000 即 fail-closed），
        # 该阈值不动 —— 它是正确性保护，不是成本项。
        self.fill_reserve_cap = (fill_cap if fill_reserve_cap is None
                                 else int(fill_reserve_cap))
        # 观察到的最大返回笔数（只用于把预扣往保守方向修正，不会低于基线）
        self.fill_observed_max = 0
        self._deferred = {}

    def note_fill_count(self, n):
        """记录一次实际返回笔数，并对「预扣不足」部分补扣差额。

        安全要求（test_fill_surcharge_reserved_before_request 锁定）：
        实际返回可能远超预扣——预扣 25 而真实返回 2000 笔（应扣 120）时，
        少扣的 95 会让这一分钟预算被击穿，必须补扣。

        重要：补扣只针对**刚刚这此请求已预扣的那笔**。
        `self._pending_reserve` 记录本次预扣的权重，读完立刻清零；
        没有待对账的预扣时（例如外部直接调 note_fill_count），
        只更新观测值、**不做补扣**——否则会凭空扣费。
        实测问题：note_fill_count(5000) 单独调用时，reserved 按当前 cap 算
        而实际并无预扣记录，结果凭空多扣 150，单次请求记到 365（应 ≤120）。
        """
        try:
            n = int(n)
        except (TypeError, ValueError):
            return
        actual = math.ceil(max(1, n)/20)
        pending = getattr(self, '_pending_reserve', None)
        self._pending_reserve = None
        if pending is not None:
            extra = actual - pending
            if extra > 0:
                # 真实成本高于预扣：记下全部已发生成本，后续准入等待偿还窗口。
                # The response has already arrived: account debt, never report unsent.
                self.budget.record(extra, kind='userFillsByTime_surcharge')
        if n > self.fill_observed_max:
            self.fill_observed_max = n

    def _fill_reserve_cap_now(self):
        observed = max(0, getattr(self, 'fill_observed_max', 0))
        cap = max(100, observed * 2)
        return min(cap, self.fill_reserve_cap)

    def __call__(self, payload):
        kind = payload['type']
        weight = 2 if kind in ('l2Book', 'spotClearinghouseState', 'orderStatus', 'allMids', 'clearinghouseState', 'exchangeStatus') else 20
        # Preserve adaptive fill admission. Unexpected response cost is recorded
        # as incurred debt, never misreported as an unsent request.
        if kind in ('userFills', 'userFillsByTime'):
            # 预扣 = 基线 20 + ceil(cap/20)
            # cap 取 min(fill_reserve_cap, max(观察峰值×2, 100))：
            # 给观察峰值留 2 倍余量，但绝不超过 fill_reserve_cap。
            # 若实际返回超出预扣，note_fill_count() 会补扣差额（不少算）。
            reserve = math.ceil(self._fill_reserve_cap_now()/20)
            weight += reserve
            # 记下本次预扣量，供读完后对账（见 note_fill_count）
            self._pending_reserve = reserve
        # Routine reads leave headroom; cancel_all and exit operations enter priority().
        essential = kind in ('orderStatus', 'spotClearinghouseState')
        # 2026-11-01：把 kind 传下去，否则 charge() 里的分类统计全是 'unknown'
        # （实测踩到：120 秒 1588 权重、denied=1，但 by_kind 只有 unknown 一项，
        #   完全看不出是哪种请求吃掉了预算，等于白统计）。
        key = json.dumps({k: v for k, v in payload.items() if k != 'endTime'},
                         sort_keys=True) + str(bool(getattr(self.budget, '_priority', 0)))
        ready = self._deferred.get(key, 0)
        try:
            if self.budget.now() < ready:
                raise BudgetUnavailable(retry_at=ready)
            self.budget.charge(weight, essential=essential, kind=kind)
        except BudgetUnavailable as exc:
            self._pending_reserve = None
            self._deferred[key] = exc.retry_at
            raise
        self._deferred.pop(key, None)
        # 2026-11-01 修复 P3-2（_pending_reserve 异常路径泄漏）：
        # 原来 self.read(payload) 抛异常时 note_fill_count 不会被调用，
        # _pending_reserve 残留；之后一次外部 note_fill_count(5000)
        # 会按 `extra = actual - 残留值` 多扣（实测多扣 245 权重）。
        # 用 try/finally 保证：无论 read 成败，预扣配对状态都被清零。
        try:
            result = self.read(payload)
        except Exception:
            if kind in ('userFills', 'userFillsByTime'):
                self._pending_reserve = None
            raise
        # 成交查询返回后立刻对账——若实际笔数超出预扣，补扣差额。
        # 这是「预扣可以按实际规模下调」的安全前提：
        # 少扣的部分在这里补回，记账量始终 >= 真实成本。
        if kind in ('userFills', 'userFillsByTime') and isinstance(result, list):
            try:
                self.note_fill_count(len(result))
            except BudgetUnavailable:
                # 真实成本已发生但预算已透支 → 必须上抛，不能吞掉
                raise
        elif kind in ('userFills', 'userFillsByTime'):
            # 返回不是 list（异常形态）：同样清零，避免泄漏
            self._pending_reserve = None
        return result


def positive_decimal(value):
    d = Decimal(str(value))
    if not d.is_finite() or d <= 0:
        raise ValueError('amount/price must be positive and finite')
    return d


def amount_wire(value):
    d = positive_decimal(value)
    s = format(d, 'f')
    return s.rstrip('0').rstrip('.') if '.' in s else s


def price_wire(value, buy=False, tif='Alo'):
    d = positive_decimal(value)
    if d >= 1:
        raise ValueError('outcome price must be below 1')
    tick = max(Decimal('0.00001'), Decimal(10) ** (d.adjusted()-4))
    # Passive buys never round up. IOC buys round up, sells down.
    mode = ROUND_CEILING if buy and tif == 'Ioc' else ROUND_FLOOR
    rounded = (d/tick).to_integral_value(rounding=mode)*tick
    if not 0 < rounded < 1:
        raise ValueError('price outside outcome range after tick rounding')
    return amount_wire(rounded)


def minimum_order(prices, shares, limits=None):
    limits = limits or {}
    p = [positive_decimal(v) for v in prices]
    n = positive_decimal(shares)
    if len(p) != 2 or n != n.to_integral_value() or any(v >= 1 for v in p):
        return False
    floor = max(Decimal('1'), Decimal(str(limits.get('min_notional_per_leg', 1))))
    required = max(int((Decimal(1)/max(Decimal('.01'), min(v, 1-v))).to_integral_value(rounding=ROUND_CEILING)) for v in p)
    return (n >= max(required, Decimal(str(limits.get('min_shares', 0))))
            and all(n*v >= floor for v in p))


def sell_proceeds(qty, execution_px):
    return qty*execution_px*(1-0.001344)
