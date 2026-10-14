#!/usr/bin/env python3
"""Reproduce the manuscript's 70-digit outward-rounded calculation.

This is independent numerical evidence, not a Lean proof or a certificate
checked by the Lean kernel. Python's Decimal exp/ln provide correctly rounded
nearest results; adjacent representable decimals give outward enclosures.
All subsequent arithmetic uses ROUND_CEILING. No optimization is performed.
"""
from decimal import Decimal as D, getcontext, ROUND_CEILING
from pathlib import Path
import json
import time

getcontext().prec = 70
getcontext().rounding = ROUND_CEILING
HERE = Path(__file__).resolve().parent

def exp_hi(x):
    return x.exp().next_plus()

def exp_lo(x):
    return x.exp().next_minus()

def log_hi(x):
    return x.ln().next_plus()

def log_lo(x):
    return x.ln().next_minus()

def upward_six(x):
    return str(x.quantize(D('0.000001'), rounding=ROUND_CEILING))

def main():
    started = time.monotonic()
    knots = list(map(D, json.loads((HERE / 'finite-parameters.json').read_text())))
    assert len(knots) == 61 and min(knots) > 0
    times = [D(0)] + [D(1) - D(2) ** (-k) * (D(1) - D(j)/128)
                     for k in range(30) for j in range(1, 65)]
    theta = [D(0)] + [(D(1)-D(j)/32)*knots[r] + D(j)/32*knots[r+1]
                     for r in range(60) for j in range(1, 33)]
    assert len(times) == len(theta) == 1921
    assert all(times[i-1] < times[i] < 1 for i in range(1,1921))
    bounds = [D(0)]
    checkpoints = {}
    for i in range(1,1921):
        th = theta[i]
        h = -log_lo(1-times[i]) + th - 1 - log_lo(th)
        value = exp_hi(th*(times[i]-times[i-1])) * h / th
        weighted_sum = D(0)
        for j in range(1,i):
            w = (exp_hi(-th*(times[i-1]-times[j]))
                 - exp_lo(-th*(times[i-1]-times[j-1])))
            assert w >= 0
            weighted_sum += bounds[j]*w
        value += weighted_sum
        bounds.append(value)
        if i in (64,128,320,640,1280,1920):
            checkpoints[str(i)] = upward_six(value)
            print(f'b[{i}] <= {checkpoints[str(i)]}', flush=True)
    terminals = []
    eps = D(2)**(-30)
    for label, log_m_hi, th in [('100',log_hi(D(100)),D(7)),
                                ('1000',log_hi(D(1000)),D(12)),
                                ('10000',log_hi(D(10000)),D(19)),
                                ('1000000',log_hi(D(1000000)),D(36)),
                                ('10^80',D(80)*log_hi(D(10)),D(1600))]:
        value = D(1) + log_m_hi / th
        weighted_sum = D(0)
        for j in range(1,1921):
            w = exp_hi(-th*(1-times[j])) - exp_lo(-th*(1-times[j-1]))
            assert w >= 0
            weighted_sum += bounds[j]*w
        value += weighted_sum
        value += D(7)/6*th*eps*(-log_lo(eps)+2-log_lo(D(2)))
        terminals.append({'maximum_types':label,'terminal_theta':str(th),
                          'upper_70_digits':str(value),'upper_six_digits':upward_six(value)})
        print(label, upward_six(value), flush=True)
    partial = [bounds[64]/D('.5'),bounds[128]/D('.75'),
               (D('.4')*bounds[217]+D('.6')*bounds[218])/D('.9')]
    result = {'status':'numerical reproduction only; not Lean kernel verification',
              'precision':70,'rounding':'ROUND_CEILING with adjacent exp/ln enclosures',
              'checkpoints':checkpoints,'terminals':terminals,
              'partial_allocation_upper_six_digits':list(map(upward_six,partial)),
              'elapsed_seconds':time.monotonic()-started}
    (HERE/'finite-certificate-results.json').write_text(json.dumps(result,indent=2)+'\n')
    (HERE/'grid-upper-bounds.json').write_text(json.dumps(list(map(str,bounds)))+'\n')
    assert D(terminals[-1]['upper_70_digits']) < D('4.921241') < 5
    print('Finite calculation reproduced; this is not a Lean proof.',flush=True)

if __name__ == '__main__':
    main()
