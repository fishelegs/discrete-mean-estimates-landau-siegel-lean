#!/usr/bin/env python3
"""Finite regressions for the universal proof in PROOF.md; not an asymptotic proof."""
from fractions import Fraction as F
from math import comb, isqrt
from pathlib import Path
import hashlib
import json

ROOT=Path(__file__).resolve().parent
checks=0
def require(cond):
    global checks
    assert cond
    checks+=1
def tau(k,v):
    return int(v==0) if k==0 else comb(v+k-1,k-1)
def local_nu(v,t):
    return sum(t**i for i in range(v+1))

for q in range(1,10):
    r=2*q
    K=max(0,q*(q-3)//2)
    require(r+K>=q*(q+1)//2)
    require(F(21,20)*r<F(19))
    for t in [-1,0,1]:
        for v in range(101):
            left=local_nu(v,t)**2*tau(q,v)
            if t==-1:
                right=tau(r+K,v//2) if v%2==0 else 0
            else:
                degree=2*r if t==1 else r
                right=sum(tau(degree,v-2*h)*tau(K,h) for h in range(v//2+1))
            require(left<=right)
    for h in range(101):
        require(tau(q,2*h)<=tau(q*(q+1)//2,h))

characters={
  3:{0:0,1:1,2:-1},
  5:{0:0,1:1,2:-1,3:-1,4:1},
  8:{0:0,1:1,2:0,3:-1,4:0,5:-1,6:0,7:1},
  12:{0:0,1:1,2:0,3:0,4:0,5:-1,6:0,7:-1,8:0,9:0,10:0,11:1},
}
for modulus,table in characters.items():
    chi=lambda n:table[n%modulus]
    partial=[0]
    for n in range(1,301):
        partial.append(partial[-1]+chi(n))
    nu=[0]+[sum(chi(d) for d in range(1,n+1) if n%d==0) for n in range(1,301)]
    for n in range(1,301):
        u=isqrt(n)
        hyp=sum(partial[n//a] for a in range(1,u+1))
        hyp+=sum(chi(b)*(n//b) for b in range(1,u+1))-u*partial[u]
        require(sum(nu[1:n+1])==hyp)
        require(nu[n]>=0)

rows=[]
expected_d=[-1949,-1815,-1609,-1331]
expected_b=[F(-1273,2),F(-1103,2),F(-861,2),F(-547,2)]
for j in range(1,5):
    q=2*j+1
    tail=4*q-2015
    d=tail+18*j*q
    labels=81+18*j
    b=F(labels+77)+F(324+d,2)
    require(d==expected_d[j-1])
    require(b==expected_b[j-1])
    require(b==18*j*j+31*j-F(1371,2))
    rows.append(dict(j=j,q=q,tail=tail,d=d,labels=labels,log=str(b)))
require(F(72+77)+F(144-1815,2)==F(-1373,2))
require(4*4-2015+9*4*3==-1891)
require(F(99+77)+F(225-1891,2)==-657)
require(F(1,2)-F(21,40)==F(-1,40))
require(F(-1,2)*F(1,2)==F(-1,4))
require(F(41,20)**2+5+26<64)

receipt=dict(status='PASS_FINITE_CHECKS_SOURCE_ONLY', checks=checks, rows=rows,
             scope='Finite regressions only; universal proofs are PROOF.md and REVIEW.md. No compiler was run.')
(ROOT/'AUTHOR_CHECKS.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
