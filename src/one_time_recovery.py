"""One explicitly armed recovery, consumed permanently on any subsequent fill.

There is no discovery, scheduler or automatic arming entry point here.
"""
from decimal import Decimal

BATCH_ID = 'REDACTED_RECOVERY_BATCH_ID'
PRICES = (0.0, 0.0)
QUANTITIES = (0, 0)


def finish(ex, batch, reason):
    batch.update(status='finished', reason=reason, finished_at=ex.now())
    ex.state_save()
    return False


def active(ex, oid, pos):
    """Only exempt the original redacted inventory while this batch is intact."""
    if oid != 'REDACTED_INVALID_RECOVERY_MARKET':
        return False
    ms = ex.state['markets'][oid]
    batch = ms.get('one_time_recovery')
    if not batch or batch.get('id') != BATCH_ID or batch.get('status') == 'finished':
        return False
    if batch.get('status') not in ('armed', 'waiting'):
        return finish(ex, batch, 'interrupted submission: never repeat either leg')
    st = ex.state
    if (st.get('halted') or st.get('open_blocked') or not st.get('activation_valid')
            or not st.get('ledger_known') or ex.now() >= st.get('authorization_expires_at', 0)
            or ms.get('phase') != 'waiting' or ms.get('merge_pending')
            or oid in st.get('stopped_markets', {})):
        return finish(ex, batch, 'normal risk/authorization management takes precedence')
    if any(float(pos.get(s, 0)) != q for s, q in [('0', 0), ('1', 0)]):
        return finish(ex, batch, 'inventory changed: normal net-gap management resumes')
    from v2_safety import candidate_reason, scoped_coin, number
    lot = st.get('inventory_exit', {}).get('REDACTED_INVALID_RECOVERY_TOKEN')
    threshold = number(ex.cfg['stop_loss_usd_per_market'])/(max(number(ms.get('sz', 0)), 1)*2)
    ms['single_stop_threshold'] = threshold
    if (lot is None or number(lot.get('qty', 0)) != 0
            or number(lot['exit_value']) - number(lot['cost']) <= -threshold):
        return finish(ex, batch, 'original inventory stop/cost management takes precedence')
    candidate = next((c for c in ex.candidates if str(c['outcome_id']) == oid), None)
    if candidate is None or candidate_reason(candidate, ex.now(), ex.cfg):
        return finish(ex, batch, 'entry/cutoff evidence no longer valid')
    # reconcile_intents can temporarily mark a confirmed Alo oid unknown when
    # its new order is not yet visible in the previous balance/order snapshot.
    # A waiting batch never submits again; retain only these already-known oids.
    known = {str(o['oid']) for o in batch.get('orders', {}).values()}
    pending = [i for i in st.get('intents', {}).values()
               if i.get('status') in ('unknown', 'awaiting_fill')]
    if any(batch['status'] != 'waiting' or i.get('status') == 'awaiting_fill'
           or str(i.get('oid')) not in known for i in pending):
        return finish(ex, batch, 'unresolved submission: no recovery retry')
    if st.get('snapshot_dirty') or not st.get('snapshot_known'):
        return batch['status'] == 'waiting'
    orders = [o for o in st.get('remote_orders', []) if scoped_coin(o['coin'], {oid})]
    if batch['status'] == 'armed':
        if orders:
            return finish(ex, batch, 'unexpected existing orders')
    else:
        expected = batch['orders']
        if len(orders) != 2 or any(not any(
                str(o['oid']) == str(e['oid']) and o['side'] == 'B'
                and Decimal(str(o['sz'])) == Decimal(str(e['sz']))
                and Decimal(str(o['limitPx'])) == Decimal(str(e['px']))
                for o in orders) for e in expected.values()):
            return finish(ex, batch, 'order changed or filled: normal management resumes')
    return True


def maintain(ex, oid):
    """Submit each leg once through the normal write-ahead journal and ledger."""
    from v2_safety import number, price_wire, submit, total_cap, minimum_order
    st = ex.state
    ms = st['markets'][oid]
    batch = ms['one_time_recovery']
    if batch['status'] == 'waiting':
        return '本次一次性双边恢复等待成交；新成交后回归净缺口管理'
    max_age = number(ex.cfg.get('snapshot_max_age_seconds',
                     ex.cfg.get('snapshot_refresh_seconds', 15) + 5))
    if (st.get('snapshot_dirty') or st.get('rest_budget_blocked')
            or not all(st.get(k) for k in ('snapshot_known', 'ledger_known',
                                         'activation_valid', 'reward_baseline_known'))
            or ex.now() - st.get('snapshot_at', -1e30) > max_age):
        return '一次性恢复等待正常新鲜快照/预算'
    if oid not in st.get('eligible_market_ids', []):
        finish(ex, batch, 'outside current authorized candidate window')
        return batch['reason']
    books = [ex.adapter._book(f'#REDACTED_INVALID_RECOVERY_TOKEN_{0+s}') for s in (0, 1)]
    for side, book in enumerate(books):
        bid, ask = [number(book['levels'][s][0]['px']) for s in (0, 1)]
        mid = (bid + ask) / 2
        if (abs(ex.now() - number(book['time'])/1000) > 5
                or not 0 < bid <= ask < 1
                or not ex.cfg['mid_min'] <= mid <= ex.cfg['mid_max']
                or (ask-bid)/mid*100 > ex.cfg['max_spread_pct']
                or PRICES[side] >= ask
                or float(price_wire(PRICES[side], buy=True, tif='Alo')) != PRICES[side]):
            finish(ex, batch, f'original maker quote no longer eligible: side={side}, bid={bid}, ask={ask}')
            return batch['reason']
    if abs(number(books[0]['time']) - number(books[1]['time'])) > 2000:
        finish(ex, batch, 'two-leg book timestamps differ by more than two seconds')
        return batch['reason']
    c = next(c for c in ex.candidates if str(c['outcome_id']) == oid)
    if any(not minimum_order([px, px], qty, c['sdk_limits'])
           for px, qty in zip(PRICES, QUANTITIES)):
        finish(ex, batch, 'original sizes do not meet SDK minimums')
        return batch['reason']
    cost = sum(Decimal(str(px))*q for px, q in zip(PRICES, QUANTITIES))
    reserved = Decimal(str(st.get('market_reserved', {}).get(oid, 0)))
    if (reserved != Decimal('0')
            or reserved+cost > Decimal(str(ex.cfg['capital_per_market']))
            or Decimal(str(st.get('reserved_total', 0)))+cost > Decimal(str(total_cap(ex.cfg)))
            or number(st.get('free_cash', 0)) < float(cost)+number(ex.cfg['experiment_principal_usdc'])*0.1):
        finish(ex, batch, 'inventory cost/capital bounds changed')
        return batch['reason']
    # Persist the full reservation and a consumed submission slot before any send.
    # A crash at any point goes to normal reconciliation, never to another send.
    batch.update(status='sending', orders={})
    st['reserved_total'] = float(Decimal(str(st['reserved_total']))+cost)
    st.setdefault('market_reserved', {})[oid] = float(reserved+cost)
    st['free_cash'] -= float(cost)
    ex.state_save()
    for side, (px, qty) in enumerate(zip(PRICES, QUANTITIES)):
        batch['sending_side'] = side
        ex.state_save()
        intent = submit(ex, f'#REDACTED_INVALID_RECOVERY_TOKEN_{0+side}', True, qty, px, 'Alo')
        if intent['status'] != 'submitted':
            finish(ex, batch, 'submission not confirmed: no repeat; normal reconciliation resumes')
            ex.adapter.cancel_all(-1)
            return batch['reason']
        batch['orders'][str(side)] = {'oid': intent['oid'], 'px': px, 'sz': qty,
                                      'client_id': intent['client_id']}
        ex.state_save()
    ms['orders'] = batch['orders']
    batch.update(status='waiting', submitted_at=ex.now())
    ex.state_save()
    return '本次一次性REDACTED_TEAM_A/REDACTED_TEAM_B原价maker买单已提交，等待真实快照'
