#!/usr/bin/env python3
"""Finite algebra and exact rational budgets only; no analytic or Lean proof."""
import cmath
import json
from fractions import Fraction as F
from math import comb, gcd, prod, sqrt, tau


def fac(n):
    d, fs = 2, {}
    while d*d <= n:
        while n%d == 0:
            fs[d] = fs.get(d, 0)+1
            n //= d
        d += 1
    if n > 1: fs[n] = fs.get(n, 0)+1
    return fs

def divs(n):
    ds = [1]
    for p, j in fac(n).items():
        ds = [d*p**i for d in ds for i in range(j+1)]
    return ds

def mu(n):
    fs = fac(n)
    return 0 if any(j>1 for j in fs.values()) else (-1)**len(fs)

def tau_r(n, r): return prod(comb(j+r-1, r-1) for j in fac(n).values())

def chi(n, D):
    if D == 5: return [0,1,-1,-1,1][n%5]
    if D == 8: return [0,1,0,-1,0,-1,0,1][n%8]
    if D == 12: return [0,1,0,0,0,-1,0,-1,0,0,0,1][n%12]
    raise ValueError(D)

count = 0
for D in (5,8,12):
    lim = 700
    nu = [0]+[sum(chi(d,D) for d in divs(n)) for n in range(1,lim+1)]
    up = [0]+[sum(mu(d)*mu(n//d)*chi(n//d,D) for d in divs(n)) for n in range(1,lim+1)]
    for X in (3,7,13):
        rho = [0]+[sum(up[n//e]*nu[e] for e in divs(n) if e>X) for n in range(1,lim+1)]
        cut = [0]+[sum(up[n//e]*nu[e] for e in divs(n) if e<=X) for n in range(1,lim+1)]
        for n in range(1,lim+1):
            assert rho[n]+cut[n] == int(n==1)
            fs = fac(n)
            b = prod(p for p,j in fs.items() if j%2)
            t = prod(p**(j//2) for p,j in fs.items())
            assert n == t*t*b
            assert abs(rho[n]) <= tau_r(t,9)*tau_r(b,4)
            assert rho[n]**2*tau_r(n,3) <= tau_r(t,486)*tau_r(b,48)
            if rho[n]:
                assert all(j%2 == 0 for p,j in fs.items() if chi(p,D)==-1)
            for ell,j in fs.items():
                if ell>X and chi(ell,D)==1:
                    w = n//ell**j
                    local = {1:-2,2:1}.get(j,0)
                    assert rho[n] == -local*cut[w]
                    count += 1

for j in range(1000):
    assert 2*j+1 <= comb(j+2,2)
    assert comb(2*j+2,2) <= comb(j+5,5)
    # Universal ratio differences behind the two previous inductions.
    assert (j+3)*(2*j+1)-(2*j+3)*(j+1) == 2*j
    assert (j+6)*(2*j+1)-(j+2)*(2*j+3) == 6*j

def generator(p):
    return next(g for g in range(2,p) if len({pow(g,k,p) for k in range(p-1)})==p-1)

max_gauss_error = 0.0
for p in (5,7,11,13):
    g = generator(p)
    logs = {pow(g,k,p):k for k in range(p-1)}
    def psi(k,n):
        return 0 if n%p==0 else cmath.exp(tau*1j*k*logs[n%p]/(p-1))
    for a in (0,1):
        for c in range(1,p):
            for n in range(1,p):
                for orient in (1,-1):
                    z = 0j
                    for k in range(1,p-1):
                        if k%2 != a: continue
                        gauss = sum(psi(orient*k,x)*cmath.exp(tau*1j*x/p) for x in range(1,p))
                        z += gauss*psi(k,c)*psi(k,n).conjugate()
                    arg = n*pow(c,-1,p)%p if orient==1 else c*pow(n,-1,p)%p
                    expected=(p-1)/2*(cmath.exp(tau*1j*arg/p)+(-1)**a*cmath.exp(-tau*1j*arg/p))+int(a==0)
                    err=abs(z-expected)
                    assert err<1e-10
                    max_gauss_error=max(max_gauss_error,err)

beta=F(3,20)
k0=F(7,5)
high_breaks=(k0,F(1103,600),F(224,100),F(301,100))
def f(k): return -F(1,4)+beta/2+max(F(0),-F(896,1000)+F(2,5)*k)/2+max(F(0),F(1103,1000)-F(3,5)*k)/2
def g(k): return (beta-k)/4+max(F(0),-F(663,1000)+F(2,3)*k)
assert max(map(f,high_breaks)) == -F(21,1000)
assert g(k0) == -F(253,6000)
assert F(225,2)+F(2916,4)+F(324,4)+36+77+72 <1200
assert F(4860+324,2)+77+72 <3000
assert 2*9*9*6//2 == 486

result={"finite_large_split_prime_cases":count,"largest_gauss_identity_error":max_gauss_error,"high_range_max_exponent":str(max(map(f,high_breaks))),"low_range_max_exponent":str(g(k0)),"checks":"passed; finite algebra and rational arithmetic only"}
print(json.dumps(result,indent=2))
