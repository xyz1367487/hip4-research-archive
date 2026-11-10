"""Bounded append journals and program-owned read-only dashboard projections."""
import json
import os
import time
import uuid
from pathlib import Path

JOURNAL_MAX_BYTES = 32 * 1024 * 1024
RECORD_MAX_BYTES = 256 * 1024
VIEW_OWNER = 'hip4-v2-runtime-derived-1'


def read_last(path):
    path = Path(path)
    if path.stat().st_size > JOURNAL_MAX_BYTES:
        # 保持 fail-closed：超限即拒绝，绝不静默归档或改字原文。
        # （test_v2_blockers 明确锁定这条契约：报错且原文件字节不变。）
        # 滚动由调用方在**撞墙之前**主动调用 archive_journal() 完成。
        raise ValueError('journal size limit exceeded; preserve file and refuse recovery')
    with path.open('rb') as f:
        size = f.seek(0, 2)
        f.seek(max(0, size - RECORD_MAX_BYTES - 1))
        raw = f.read(RECORD_MAX_BYTES + 1)
    if not raw or not raw.endswith(b'\n'):
        # Support bounded legacy single JSON documents.
        if size > RECORD_MAX_BYTES:
            raise ValueError('journal trailing record incomplete/oversized')
        return json.loads(raw)
    record = raw[:-1].rsplit(b'\n', 1)[-1]
    if len(record) > RECORD_MAX_BYTES:
        raise ValueError('journal record size limit exceeded')
    return json.loads(record)


def archive_journal(path):
    '把写满的 journal 整份改名归档，腾出新的空文件继续写。\n\n    历史版本：32MiB 上限原本是 fail-closed 保护，但它把执行器锁死在\n    「拒绝写入 → 主循环崩溃 → 重启 → 再次拒绝」的循环里（NRestarts 4000+）。\n    上限本身有意义（防单文件无限增长），但不该让进程永久瘫痪。\n\n    归档策略（可恢复、不丢证据）：\n    - 整份改名为 <name>.<时间戳>.archived，原文件一字不改\n    - 新建同名空文件，read_last() 会把它当作「无历史状态」处理\n    - 归档文件保留在磁盘，人工可查；不自动删除\n    '
    path = Path(path)
    if not path.exists() or path.stat().st_size == 0:
        return None
    stamp = time.strftime('%Y%m%dT%H%M%SZ', time.gmtime())
    target = path.with_name(path.name + '.' + stamp + '.archived')
    n = 0
    while target.exists():          # 同一秒内重复归档
        n += 1
        target = path.with_name(path.name + '.' + stamp + f'.{n}.archived')
    os.replace(path, target)        # 原子改名，内容不变
    return target


def append_record(path, data):
    path = Path(path)
    raw = (json.dumps(data, ensure_ascii=False, separators=(',', ':')) + '\n').encode()
    if len(raw) > RECORD_MAX_BYTES:
        raise ValueError('journal record size limit exceeded; no append')
    if (path.stat().st_size if path.exists() else 0) + len(raw) > JOURNAL_MAX_BYTES:
        # 保持 fail-closed（契约见 test_v2_blockers）：不在这里自动归档。
        # 正常路径下调用方会在接近上限时先调 archive_journal()，不会走到这里。
        raise ValueError('journal size limit exceeded; preserve file and refuse append')
    with path.open('ab') as f:
        f.write(raw)
        f.flush()
        os.fsync(f.fileno())


def maybe_archive(path, ratio=0.9):
    '在撞上 32MiB 硬上限**之前**主动滚动 journal。\n\n    历史版本 事故：journal 2 小时写满 32MiB → append 每次被拒 → 主循环\n    每 5 秒崩溃一次（NRestarts 4000+），仓位无人管理、merge 没跑。\n    上限本身是合理的 fail-closed 保护（超限拒绝、原文不动），\n    但必须有人在**到达上限前**把文件滚走，否则保护会变成永久瘫痪。\n\n    这里只做「整份原子改名 + 新建空文件」，不改任何字节、不删除归档。\n    返回归档路径（未触发则 None）。\n    '
    path = Path(path)
    try:
        size = path.stat().st_size
    except FileNotFoundError:
        return None
    if size < JOURNAL_MAX_BYTES * ratio:
        return None
    return archive_journal(path)


def publish_owned(path, data, identity):
    path = Path(path)
    if path.is_symlink():
        raise ValueError('derived view symlink refused')
    if path.exists():
        if path.stat().st_size > 16 * 1024 * 1024:
            raise ValueError('derived view oversized')
        previous = json.loads(path.read_text())
        if previous.get('derived_by') != VIEW_OWNER or previous.get('experiment_identity') != identity:
            raise ValueError('unknown derived-view destination; preserve original file')
    path.parent.mkdir(parents=True, exist_ok=True)
    data = dict(data, derived_by=VIEW_OWNER, experiment_identity=identity)
    stage = path.with_name(path.name + '.' + uuid.uuid4().hex + '.pending')
    with stage.open('x') as f:
        json.dump(data, f, ensure_ascii=False)
        f.flush()
        os.fsync(f.fileno())
    os.replace(stage, path)  # only a verified program-owned projection is replaced
