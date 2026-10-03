#!/usr/bin/env python3
"""Exact support/budget/profile checks for the separate fixed-log-window addendum."""
from fractions import Fraction as F
from pathlib import Path
import hashlib
import sympy as sp

amin,amax=F(502,1000),F(504,1000)
bmin,bmax=F(499,1000),F(500,1000)
jmin,jmax=F(500,1000),F(504,1000)
cr,cl,tr,tl=F(9995,10000),F(1005,1000),F(1005,1000),F(1005,1000)
gaps={
 'C1 right, cutoff+product_min-2':cr+amin+bmin-2,
 'C1 left, cutoff-product_max':cl-amax-bmax,
 'T1 right, cutoff+A_min-1-J_max':tr+amin-1-jmax,
 'T1 left, cutoff+J_min-1-A_max':tl+jmin-1-amax,
 'C0[J,B] right':tr+jmin+bmin-2,
 'C0[J,B] left':tl-jmax-bmax,
}
assert list(gaps.values())==[F(1,2000),F(1,1000),F(3,1000),F(1,1000),F(1,250),F(1,1000)]
lengths={'right_kappa_square':2*cr,'left_and_target_kappa':cl,'A_cube':3*amax,'B_cube':3*bmax,'J_cube':3*jmax}
assert all(x<2 for x in lengths.values())
assert jmin<=amin<=amax<=jmax
left=F(36,2)+F(81,6)+F(81,6)-F(739,6)+F(77*5,6)
right=F(144,4)+F(81,6)+F(81,6)-F(739*5,12)+F(77*7,12)
assert left==-14 and right==-200
print('Exact positive endpoint gaps:',{k:str(v) for k,v in gaps.items()})
print('Exact large-sieve support exponents (<2):',{k:str(v) for k,v in lengths.items()})
print('Unchanged Holder budgets:',{'C1_right':str(right),'C1_left_and_T1_both':str(left)})
print('A support is contained in the unchanged original J class')

u=sp.symbols('u',real=True)
profile_checks={}
for name,lo,hi in [('A',amin,amax),('B',bmin,bmax),('J',jmin,jmax)]:
    lo,hi=sp.Rational(lo.numerator,lo.denominator),sp.Rational(hi.numerator,hi.denominator)
    mid=(lo+hi)/2
    norm=sp.integrate(((u-lo)/(mid-lo))**2,(u,lo,mid))+sp.integrate(((hi-u)/(hi-mid))**2,(u,mid,hi))
    assert sp.simplify(norm-(hi-lo)/3)==0
    profile_checks[name]=str(norm)
assert profile_checks=={'A':'1/1500','B':'1/3000','J':'1/750'}
print('Fixed bounded triangular profile L2 norms:',profile_checks)
for disc in [-8,12,13]:
    D=abs(disc)
    assert sum(sp.kronecker_symbol(disc,n)**2 for n in range(D))==sp.totient(D)
print('Chi-square periodic density is phi(D)/D; it must not be omitted')
frozen=Path(__file__).resolve().parents[1] / 'reports' / 'DYADIC_REPORT.md'
assert hashlib.sha256(frozen.read_bytes()).hexdigest()=='f1dc2dfa62e0eb7310eb557f14e1dc2ff1eb99681d9acd4f147b2f9139d54635'
print('Frozen base report hash remains unchanged')
print('ALL CHECKS PASSED; endpoint tail bounds and norm distinctions require the written review')
