#!/usr/bin/env python3
"""Finite bookkeeping checks only; no Lean and no exceptional-character test."""
from fractions import Fraction as F
from pathlib import Path
import hashlib, json, math, cmath

checks = {}

assert (2*82+36+3*77-739)/4 == -77
assert F(77)+(F(82)+9)/2 == F(245,2)
assert F(245,2)+400-9-519 == -F(11,2)
assert 9+12*2+49 == 82
assert F(151,100)+F(1005,2000) > 2
assert 2*F(1005,2000) < 2
assert 1+F(1005,2000)-F(151,100) == -F(3,400)
checks['exponent_budgets'] = True

def reduce_phi_p(vec, p):
    v = vec+[0]*(p-len(vec))
    return tuple(v[j]-v[p-1] for j in range(p-1))

for p in [3,5,7,11,13,17,19]:
    for m in range(1,p):
        for k in range(0,2*p):
            lhs=[0]*p
            if k%p:
                for a in range(1,p):
                    lhs[a] = (p-1 if (a*m-k)%p==0 else 0)-1
            rhs=[0]*p
            aa=k*pow(m,-1,p)%p
            rhs[aa]+=p-1
            rhs[0]+=1
            if k%p==0:
                rhs[0]-=p
            assert reduce_phi_p(lhs,p)==reduce_phi_p(rhs,p)
            if m>1:
                reciprocity=F(pow(m,-1,p),p)+F(pow(p,-1,m),m)-F(1,p*m)
                assert reciprocity.denominator==1
checks['gauss_primitive_principal_nonunit_exact'] = True
checks['additive_reciprocity_exact'] = True

for chi in [-1,0,1]:
    assert (3+2*chi)**2 <= 13+12*chi
    # At every prime, the five coefficients are two chi phases and three pure phases.
    for y in [-4,-.3,0,.7,5]:
        for z in [.0001,.01,.2,1,2]:
            ds=[.4,.8,1.2]
            a=chi*(1+cmath.exp(1j*y*z))+sum(cmath.exp(-1j*d*z) for d in ds)
            signs=[chi,chi,1,1,1]
            phases=[0,y*z]+[-d*z for d in ds]
            cosine=sum(signs[j]**2 for j in range(5))+sum(
                2*signs[j]*signs[k]*math.cos(phases[j]-phases[k])
                for j in range(5) for k in range(j+1,5))
            assert abs(abs(a)**2-cosine)<1e-10
checks['five_factor_cosine_identity_numeric'] = True

def divisors(n):
    return [d for d in range(1,n+1) if n%d==0]
def conv(a,b,n):
    return sum(a(d)*b(n//d) for d in divisors(n))
def chi5(n):
    return [0,1,-1,-1,1][n%5]
def mu(n):
    sign=1
    for p in range(2,n+1):
        if n%p==0:
            count=0
            while n%p==0:
                n//=p; count+=1
            if count>1:return 0
            sign=-sign
    return sign
def ups(n):return conv(mu,lambda k:mu(k)*chi5(k),n)
betas=[.02,.03,.05]
def db(n):
    val=0j
    for a in divisors(n):
        for b in divisors(n//a):
            for c in divisors(n//a//b):
                d=n//a//b//c
                val+=chi5(a)*cmath.exp(-1j*(betas[0]*math.log(b)+betas[1]*math.log(c)+betas[2]*math.log(d)))
    return val
y=.7; scale=10; X=8
def hy(n):return chi5(n)*cmath.exp(1j*y*math.log(n)/scale)
def fy(n):return conv(hy,db,n)
for k in range(1,91):
    direct=sum(ups(d)*hy(v)*db(k//d//v) for d in divisors(k)
               if d<=X and d%5!=0 for v in divisors(k//d))
    grouped=sum(ups(d)*fy(k//d) for d in divisors(k) if d<=X and d%5!=0)
    assert abs(direct-grouped)<1e-9
checks['masked_finite_convolution_numeric'] = True

result={'checks':checks,'limits':'Finite algebra checks only; no analytic theorem verification, no numerical exceptional-character experiment, no compiler.'}
print(json.dumps(result,indent=2))
