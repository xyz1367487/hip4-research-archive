'执行器业务事件记录。\n\n事件记录作为旁路运行，写入异常不会中断交易主流程。\n人读事件通过 print 输出，机读事件逐行写为 JSON；时间戳带毫秒。\n事件字段包含市场、份数、价格、耗时和状态。\nev_change 按稳定 key 去重，仅记录连续状态变化；reset 清除去重记忆。'

import json
import os
import threading
import time

# ---- 配置 ----
_EVENTS_PATH = os.environ.get(
    'HIP4_EVENTS_LOG',
    os.path.join(os.path.dirname(os.path.abspath(__file__)), 'logs', 'events.jsonl'),
)
_MAX_TEXT = 400          # 单条文本日志截断上限
_lock = threading.Lock()
_last = {}               # key -> 上次写入的规范化内容
_disabled = False


def _now_ms():
    return int(time.time() * 1000)


def _stamp(ms=None):
    """北京时间 HH:MM:SS.mmm（用户要求：全时间戳带毫秒）。

    不用 strftime('%f') —— 那取的是 microseconds，需要先 //1000。
    """
    ms = _now_ms() if ms is None else ms
    sec, milli = divmod(ms, 1000)
    return time.strftime('%Y-%m-%d %H:%M:%S', time.localtime(sec)) + '.%03d' % milli


def _safe_write(path, line):
    try:
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, 'a', encoding='utf-8') as fh:
            fh.write(line + '\n')
    except Exception:
        # 旁路日志失败绝不外抛
        pass


def _emit(tag, payload, key, dedup):
    global _disabled
    if _disabled:
        return
    try:
        ms = _now_ms()
        payload = {k: v for k, v in payload.items() if v is not None}
        if dedup and key is not None:
            sig = json.dumps(payload, ensure_ascii=False, sort_keys=True)
            with _lock:
                if _last.get(key) == sig:
                    return
                _last[key] = sig

        # 机读：events.jsonl
        rec = {'ts': ms, 'ts_bjt': _stamp(ms), 'event': tag}
        rec.update(payload)
        _safe_write(_EVENTS_PATH, json.dumps(rec, ensure_ascii=False))

        # 人读：混进 stdout（→ executor_v2.log）
        # 键值用「k=v」，空值已剔除
        parts = []
        for k, v in payload.items():
            if isinstance(v, float):
                parts.append('%s=%g' % (k, v))
            else:
                parts.append('%s=%s' % (k, v))
        text = ('[%s] [%s] %s' % (_stamp(ms), tag, ' '.join(parts)))[:_MAX_TEXT]
        print(text, flush=True)
    except Exception:
        # 任何意外都吞掉，避免拖垮交易循环
        pass


def ev(tag, key=None, dedup=False, **fields):
    """写一条业务事件。tag 形如 '成交' / '报价' / '退出'。"""
    _emit(tag, fields, key, dedup)


def ev_change(tag, key, **fields):
    """只在内容变化时写（内容相同则跳过）。key 必须稳定且唯一标识该状态。"""
    _emit(tag, fields, key, True)


def reset(key=None):
    """清除去重记忆。key=None 清全部；用于测试或显式重报。"""
    with _lock:
        if key is None:
            _last.clear()
        else:
            _last.pop(key, None)


def events_path():
    return _EVENTS_PATH
