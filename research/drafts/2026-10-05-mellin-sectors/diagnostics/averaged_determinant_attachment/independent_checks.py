#!/usr/bin/env python3
"""Portable read-only exact identities and outer-error exponent checks."""
from fractions import Fraction as F
import json,itertools
# Mathematical portion of the pinned independent diagnostic; source pins are separate.
cases=0;signs=set()
for M,E,a,b,c,d in itertools.product(range(1,5),repeat=6):
 k=M*a*d;l=E*b*c
 for sigma in (-1,1):
  Delta=k-sigma*l
  if not Delta:continue
  eps=1 if Delta>0 else -1
  AF=F(k,abs(Delta));r=sigma*(1-F(eps,1)/AF)
  assert r==F(l,k)
  assert AF*sigma*(AF-eps)==F(k*l,Delta*Delta)
  signs.add((sigma,eps));cases+=1
assert signs=={(1,1),(1,-1),(-1,1)}
# Exponent vectors are ordered (P,D,L), using phi(D)<=D.
def add(*vecs):return tuple(sum(v[i] for v in vecs) for i in range(3))
def mul(a,v):return tuple(a*t for t in v)
p=(F(1),F(0),F(0));D=(F(0),F(1),F(0));Q=(F(1),F(0),F(519));x=(F(2),F(1,2),F(1038));W=(F(0),F(0),F(400));Np=(F(1),F(0),F(-68))
H=add(x,mul(-1,p),mul(-1,W));rootK=add(p,mul(F(1,2),add(D,Np)))
base=add(mul(F(-1,2),x),rootK,mul(F(1,2),H));outer=add(base,mul(2,Q));r0=mul(F(1,2),add(H,mul(-1,Q)))
assert base==(1,F(1,2),-234)
assert outer==(3,F(1,2),804)
assert add(outer,r0)==(3,F(3,4),F(1727,2))
arg1=add(Q,mul(F(-1,2),D),mul(-1,p));arg2=add(H,mul(-1,Q),mul(-1,D))
assert arg1==(0,F(-1,2),519) and arg2==(0,F(-1,2),119)
print(json.dumps(dict(status='PASS',exact_normalization_cases=cases,signs=sorted(signs),outer_R2=list(map(str,outer)),outer_R0=list(map(str,add(outer,r0))),actual_fixed_outer_attachment_only=True,global_middle_bound=False,mathematical_certification=False),indent=2,sort_keys=True))
