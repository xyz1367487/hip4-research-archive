"""Conservative single-response account history proof; no pagination assumptions."""
from ledger import canonical, dec, fingerprint

DOC_URL = 'https://hyperliquid.gitbook.io/hyperliquid-docs/for-developers/api/info-endpoint'


def validate_history(request, fills, *, owner, start, until, cap, bootstrap=False):
    expected = {'type': 'userFillsByTime', 'user': owner.lower(), 'startTime': 0,
                'endTime': until, 'aggregateByTime': False}
    if (not isinstance(request, dict) or not isinstance(request.get('user'), str)
            or type(request.get('startTime')) is not int
            or type(request.get('endTime')) is not int
            or request.get('aggregateByTime') is not False
            or dict(request, user=request['user'].lower()) != expected):
        raise ValueError('account history request / owner mismatch')
    if (type(start) is not int or type(until) is not int or until < start
            or not 0 < cap <= 2000 or not isinstance(fills, list) or len(fills) >= cap):
        raise ValueError('REST成交覆盖失败/达到上限，不能证明完整')
    keys = set()
    for f in fills:
        if (not isinstance(f, dict) or type(f.get('time')) is not int
                or not 0 <= f['time'] <= until
                or any(f.get(k) is None or str(f[k]) == ''
                       for k in ('coin', 'tid', 'oid', 'hash', 'px', 'sz', 'fee', 'feeToken', 'dir'))
                or not isinstance(f['coin'], str) or f.get('side') not in ('A', 'B')):
            raise ValueError('REST成交时间窗/字段响应无效')
        if dec(f['sz']) <= 0 or dec(f['px']) < 0:
            raise ValueError('invalid account history size / price')
        dec(f['fee'])
        key = canonical([f['coin'], str(f['tid']), str(f['oid'])])
        stable = canonical([str(f['hash']).lower(), str(f['tid']), f['coin'].replace('+', '#', 1)])
        if key in keys or stable in keys:
            raise ValueError('duplicate account history identity')
        keys.update((key, stable))
    if bootstrap and (not fills or min(f['time'] for f in fills) >= start):
        raise ValueError('保留期外bootstrap history does not cross experiment start')
    return {'schema': 1, 'request': request, 'response': fills,
            'response_sha256': fingerprint(fills), 'official_contract': DOC_URL,
            'semantics': 'visible_at_query_not_event_time_finality',
            'mode': 'bootstrap' if bootstrap else 'full_account_replay',
            'cap': cap}
