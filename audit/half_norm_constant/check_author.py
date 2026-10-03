#!/usr/bin/env python3
"""Exact finite bookkeeping only; no exceptional-character experiment or compiler."""
from fractions import Fraction as F
from functools import lru_cache
from math import comb, gcd
import json

if not __debug__:
    raise SystemExit("Run without Python optimization; exact checks use assertions.")

@lru_cache(None)
def factors(n):
    out = []
    p = 2
    while p*p <= n:
        if n % p == 0:
            a = 0
            while n % p == 0:
                n //= p
                a += 1
            out.append((p,a))
        p += 1
    if n > 1:
        out.append((n,1))
    return tuple(out)

@lru_cache(None)
def divisors(n):
    ds = [1]
    for p,a in factors(n):
        ds = [d*p**e for d in ds for e in range(a+1)]
    return tuple(sorted(ds))

def mu(n):
    fs = factors(n)
    return 0 if any(a>1 for _,a in fs) else (-1)**len(fs)

def rad(n):
    z = 1
    for p,_ in factors(n):
        z *= p
    return z

def phi(n):
    z = n
    for p,_ in factors(n):
        z = z//p*(p-1)
    return z

def tau(n,j):
    z = 1
    for _,a in factors(n):
        z *= comb(a+j-1,j-1)
    return z

def conv(a,b,N):
    return [0]+[sum(a[d]*b[n//d] for d in divisors(n)) for n in range(1,N+1)]

def char(D,n):
    if gcd(D,n)>1:
        return 0
    if D in (5,7):
        return 1 if pow(n,(D-1)//2,D)==1 else -1
    if D == 8:
        return 1 if n%8 in (1,7) else -1
    if D == 12:
        return 1 if n%12 in (1,11) else -1
    raise ValueError(D)

N = 600
checks = {}
one = [0]+[1]*N
mob = [0]+[mu(n) for n in range(1,N+1)]
delta = [0]+[int(n==1) for n in range(1,N+1)]
# Algebraic unit-valued multiplicative fixtures, not the actual beta shifts.
power1 = [0]+[(-1)**sum(a for _,a in factors(n)) for n in range(1,N+1)]
power2 = [0]+[(-1)**dict(factors(n)).get(2,0) for n in range(1,N+1)]
power3 = [a*b for a,b in zip(power1,power2)]
triple = conv(conv(power1,power2,N),power3,N)
kappa = conv(mob,triple,N)
assert all(abs(kappa[n])<=tau(n,4) for n in range(1,N+1))

case_count = 0
for D in (5,7,8,12):
    chi = [0]+[char(D,n) for n in range(1,N+1)]
    nu = conv(one,chi,N)
    ups = conv(mob,[a*b for a,b in zip(mob,chi)],N)
    assert conv(ups,nu,N)==delta
    assert conv(nu,kappa,N)==conv(chi,triple,N)
    full_deleted = conv([u if n and n%D==0 else 0 for n,u in enumerate(ups)],nu,N)
    exact_deleted = [0]+[mu(D)*int(rad(n)==D) if mu(D) else 0 for n in range(1,N+1)]
    assert full_deleted==exact_deleted
    h = [0]+[chi[n]*F((n%5)-2,2) if 9<=n<=17 else 0 for n in range(1,N+1)]
    g = conv(kappa,h,N)
    assert all(abs(g[n])<=tau(n,5) for n in range(1,N+1))
    for X in (1,9,23,41):
        ux = [u if n and n<=X and n%D else 0 for n,u in enumerate(ups)]
        ut = [u if n>X and n%D else 0 for n,u in enumerate(ups)]
        qt = conv(ut,nu,N)
        assert all(qt[n]==0 for n in range(1,min(X,N)+1))
        assert all(abs(qt[n])<=nu[n]*tau(n,2) for n in range(1,N+1))
        assert conv(ux,nu,N)==[d-t-e for d,t,e in zip(delta,qt,full_deleted)]
        b = conv(conv(ux,h,N),conv(chi,triple,N),N)
        et = conv(qt,g,N)
        ed = conv(full_deleted,g,N)
        assert b==[a-c-d for a,c,d in zip(g,et,ed)]
        # Exact weighted finite Cauchy comparison at the fixture endpoint.
        energy = sum(F(abs(et[n])**2,n) for n in range(1,N+1))
        qenergy = sum(F(abs(qt[n])**2*tau(n,2),n) for n in range(1,N+1))
        genergy = sum(F(abs(g[n])**2*tau(n,2),n) for n in range(1,N+1))
        assert energy<=qenergy*genergy
        case_count += 1
checks['finite_coefficient_cases'] = case_count
checks['coefficient_fixture_endpoint'] = N
checks['fixtures_not_claimed_to_satisfy_A'] = True
checks['fixture_cutoffs_test_an_identity_valid_for_every_X'] = True

ram_count = 0
for m in range(1,141):
    for k in range(1,141):
        d = gcd(m,k)
        c = sum(r*mu(m//r) for r in divisors(d))
        assert F(c,phi(m))==F(mu(m//d),phi(m//d))
        assert abs(c)<=phi(m)
        assert abs(c)<=sum(divisors(d))
        assert sum(F(r,phi(r)) for r in divisors(k))<=tau(k,3)
        ram_count += 1
checks['ramanujan_gcd_cases'] = ram_count

for n in range(1,N+1):
    assert tau(n,2)<=tau(n,3)
    assert tau(n,5)**2*tau(n,2)<=tau(n,50)
    assert tau(n,4)*tau(n,3)<=tau(n,12)
    for d in divisors(n):
        assert phi(n)>=phi(d)*phi(n//d)
        assert tau(n,3)<=tau(d,3)*tau(n//d,3)
checks['divisor_envelope_endpoint'] = N

budget = {
    'sparse_weighted_energy': -F(1853,2),
    'defect_energy': F(450)-F(1853,2),
    'whole_mean_tail': F(77)+F(9,2)-F(953,4),
    'whole_mean_deleted_log': F(77)+F(9,2)+225,
    'principal_sparse_l1': -F(1853,4)+F(27,2),
    'principal_prefactor': F(260+9+27+108),
    'principal_error': F(260+9+27+108)-F(1799,4),
    'whole_safe_tail_R2000': F(101,100)-F(3,400)*2000,
    'principal_safe_tail_R2000': F(51,100)-F(3,400)*2000,
    'Y_below_P2': F(2)-F(151,100),
    'g_tail_resonance_margin': F(151,100)-F(201,400)-1,
}
assert budget['defect_energy']==-F(953,2)
assert budget['whole_mean_tail']==-F(627,4)
assert budget['whole_mean_deleted_log']==F(613,2)<307
assert budget['principal_sparse_l1']==-F(1799,4)
assert budget['principal_error']==-F(183,4)
assert budget['whole_safe_tail_R2000']<-10
assert budget['principal_safe_tail_R2000']<-10
assert budget['Y_below_P2']>0 and budget['g_tail_resonance_margin']==F(3,400)
checks['rational_budgets'] = {k:str(v) for k,v in budget.items()}
checks['sign_identity'] = 'Re(-i*z)=Im(z); both original source means contain -i*w_p'
checks['complex_nonprincipal_chain'] = [
    'Jright=Theta_H/(a*Mcal)+o(1)',
    '-i*R_D=Jright+o(1)',
    '-i*R_pr=PrincipalMean_P7/(a*Mcal)+o(1)',
    'Theta_H-PrincipalMean_P7=o(Mcal)',
    '-i*R_np=o(1)',
]

checks['analytic_or_Lean_verification'] = False
checks['result'] = 'PASS: exact finite algebra and rational budgets only'
print(json.dumps(checks,indent=2))
