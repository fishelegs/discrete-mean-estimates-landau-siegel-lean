#!/usr/bin/env python3
"""Finite regressions for the separate fixed-log-window addendum."""
from fractions import Fraction as F
import mpmath as mp

mp.mp.dps=70
Alo,Ahi=F(502,1000),F(504,1000)
Blo,Bhi=F(499,1000),F(500,1000)
Jlo,Jhi=F(500,1000),F(504,1000)
Rright=F(9995,10000)
Rleft=Rtarget=F(1005,1000)
widths={'A':Ahi-Alo,'B':Bhi-Blo,'J':Jhi-Jlo}
assert widths=={'A':F(1,500),'B':F(1,1000),'J':F(1,250)}
gaps={
    'C1 right':Rright+Alo+Blo-2,
    'C1 left':Rleft-Ahi-Bhi,
    'T1 right':Rtarget+Alo-1-Jhi,
    'T1 left':Rtarget+Jlo-Ahi-1,
    'C0[J,B] right':Rtarget+Jlo+Blo-2,
    'C0[J,B] left':Rtarget-Jhi-Bhi,
}
assert gaps=={
    'C1 right':F(1,2000),'C1 left':F(1,1000),
    'T1 right':F(3,1000),'T1 left':F(1,1000),
    'C0[J,B] right':F(1,250),'C0[J,B] left':F(1,1000),
}
assert all(gap>0 for gap in gaps.values())
lengths={'right kappa square':2*Rright,'left/target kappa':Rleft,
         'A cube':3*Ahi,'B cube':3*Bhi,'J cube':3*Jhi}
assert all(length<2 for length in lengths.values())
assert Jlo<=Alo<=Ahi<=Jhi
right_budget=F(144,4)+F(81,6)+F(81,6)-F(739*5,12)+F(77*7,12)
other_budget=F(36,2)+F(81,6)+F(81,6)-F(739,6)+F(77*5,6)
assert right_budget==-200 and other_budget==-14
print('Fixed logarithmic widths:',widths)
print('Positive power gaps before D/t0 factors:',gaps)
print('Large-sieve input length exponents, all below 2:',lengths)
print('Exact unchanged Holder budgets:',right_budget,other_budget)

checks=0
for low,high in [(10,1000),(mp.mpf('10.25'),1000),(100,5000)]:
    ns=range(int(mp.ceil(low)),high+1)
    for sigma in [mp.mpf('1.5'),mp.mpf('2'),mp.mpf('8'),mp.mpf('50')]:
        # Normalize each term before adding, avoiding small/large power issues.
        normalized=mp.fsum((mp.mpf(n)/low)**(-sigma)/low for n in ns)
        assert normalized<=3
        checks+=1
    for sigma in [mp.mpf('-.5'),mp.mpf('-2'),mp.mpf('-8'),mp.mpf('-50')]:
        normalized=mp.fsum((mp.mpf(n)/high)**(-sigma)/high for n in ns)
        assert normalized<=1
        dual_normalized=mp.fsum((mp.mpf(n)/low)**(sigma-1)/low for n in ns)
        assert dual_normalized<=3
        checks+=2
print(checks,'finite normalized endpoint bounds passed')
print('ALL CHECKS PASSED. No arithmetic main term or signed gain is established by these checks.')
