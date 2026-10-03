#!/usr/bin/env python3
"""Independent exact bookkeeping; no candidate import, compiler, or analytic experiment."""
from fractions import Fraction as Q
from functools import lru_cache
from math import comb, gcd
import json

if not __debug__:
    raise SystemExit("Run without Python optimization; exact checks use assertions.")
checks = {}

@lru_cache(None)
def factor(n):
    ans = []
    p = 2
    while p*p <= n:
        e = 0
        while n % p == 0:
            n //= p
            e += 1
        if e:
            ans.append((p,e))
        p += 1
    if n > 1:
        ans.append((n,1))
    return tuple(ans)

@lru_cache(None)
def divs(n):
    result = [1]
    for p,e in factor(n):
        result = [d*p**j for d in result for j in range(e+1)]
    return tuple(sorted(result))

def mu(n):
    ff = factor(n)
    return 0 if any(e>1 for _,e in ff) else (-1)**len(ff)

def radical(n):
    out = 1
    for p,e in factor(n):
        out *= p
    return out

def tau(j,n):
    ans = 1
    for p,e in factor(n):
        ans *= comb(e+j-1,j-1)
    return ans

def phi(n):
    ans = n
    for p,e in factor(n):
        ans = ans//p*(p-1)
    return ans

def chi_odd_prime(p,n):
    return 0 if n%p==0 else (1 if pow(n,(p-1)//2,p)==1 else -1)

def chi4(n):
    return 0 if n%2==0 else (1 if n%4==1 else -1)

def chi8(n):
    return 0 if n%2==0 else (1 if n%8 in (1,7) else -1)

def char(D,n):
    if D in (5,7): return chi_odd_prime(D,n)
    if D == 8: return chi8(n)
    if D == 12: return chi4(n)*chi_odd_prime(3,n)
    if D == 21: return chi_odd_prime(3,n)*chi_odd_prime(7,n)
    if D == 24: return chi8(n)*chi_odd_prime(3,n)
    if D == 28: return chi4(n)*chi_odd_prime(7,n)
    raise ValueError(D)

N = 840
def convolution(a,b):
    return [0]+[sum(a[d]*b[n//d] for d in divs(n)) for n in range(1,N+1)]

def norm_sq(z):
    # All fixtures are Gaussian integers represented exactly below 2**53.
    z = complex(z)
    assert z.real.is_integer() and z.imag.is_integer()
    return int(z.real)**2+int(z.imag)**2

one = [0]+[1]*N
mob = [0]+[mu(n) for n in range(1,N+1)]
delta = [0]+[int(n==1) for n in range(1,N+1)]
def valuation(n,p): return dict(factor(n)).get(p,0)
shift1 = [0]+[1j**valuation(n,2) for n in range(1,N+1)]
shift2 = [0]+[(-1j)**sum(e for p,e in factor(n)) for n in range(1,N+1)]
shift3 = [0]+[(-1)**valuation(n,3) for n in range(1,N+1)]
for n in range(1,N+1):
    for d in divs(n):
        for a in (shift1,shift2,shift3):
            assert a[n] == a[d]*a[n//d]
triple = convolution(convolution(shift1,shift2),shift3)
kappa = convolution(mob,triple)
assert any(complex(z).imag != 0 for z in kappa)
assert all(norm_sq(kappa[n]) <= tau(4,n)**2 for n in range(1,N+1))

cases = 0
for D in (5,7,8,12,21,24,28):
    chi = [0]+[char(D,n) for n in range(1,N+1)]
    nu = convolution(one,chi)
    upsilon = convolution(mob,[mob[n]*chi[n] for n in range(N+1)])
    assert convolution(upsilon,nu) == delta
    assert convolution(nu,kappa) == convolution(chi,triple)
    deleted = [upsilon[n] if n>0 and n%D==0 else 0 for n in range(N+1)]
    qD = convolution(deleted,nu)
    wanted = [0]+[mu(D)*int(radical(n)==D) if mu(D) else 0 for n in range(1,N+1)]
    assert qD == wanted
    for n in range(1,N+1):
        assert qD[n] in (-1,0,1)
        if qD[n]:
            assert n%D == 0 and all(D%p==0 for p,e in factor(n//D))
    h = [0]+[chi[n]*((n%3)-1) if 11<=n<=29 else 0 for n in range(1,N+1)]
    g = convolution(kappa,h)
    assert all(norm_sq(g[n])<=tau(5,n)**2 for n in range(1,N+1))
    for X in (1,7,19,43,91):
        finite = [upsilon[n] if 0<n<=X and n%D else 0 for n in range(N+1)]
        tail = [upsilon[n] if n>X and n%D else 0 for n in range(N+1)]
        qt = convolution(tail,nu)
        assert all(qt[n]==0 for n in range(min(X,N)+1))
        assert all(abs(qt[n])<=nu[n]*tau(2,n) for n in range(1,N+1))
        assert convolution(finite,nu) == [delta[n]-qt[n]-qD[n] for n in range(N+1)]
        b = convolution(convolution(finite,h),convolution(chi,triple))
        et,ed = convolution(qt,g),convolution(qD,g)
        assert b == [g[n]-et[n]-ed[n] for n in range(N+1)]
        # Opposite h mask is retained in a finite bilinear functional.
        lhs = sum(h[m]*(b[k]-g[k]+et[k]+ed[k]) for m in range(1,30) for k in range(1,91))
        assert lhs == 0
        for q,e in ((qt,et),(qD,ed)):
            lhs_energy = sum(Q(norm_sq(e[n]),n) for n in range(1,N+1))
            eq = sum(Q(norm_sq(q[n])*tau(2,n),n) for n in range(1,N+1))
            eg = sum(Q(norm_sq(g[n])*tau(2,n),n) for n in range(1,N+1))
            assert lhs_energy <= eq*eg
        cases += 1
checks['finite_complex_coefficient_cases'] = cases
checks['coefficient_endpoint'] = N
checks['real_primitive_fixture_conductors'] = [5,7,8,12,21,24,28]
checks['fixtures_claimed_to_satisfy_A'] = False

# Universal local comparisons: multiply low-degree polynomials exactly.
def poly_mul(a,b):
    out = [0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): out[i+j] += x*y
    return out
def poly_pow(a,n):
    out = [1]
    for _ in range(n): out = poly_mul(out,a)
    return out
def poly_sub(a,b):
    out = [(a[i] if i<len(a) else 0)-(b[i] if i<len(b) else 0) for i in range(max(len(a),len(b)))]
    while len(out)>1 and out[-1]==0: out.pop()
    return out
ratio_polynomials = {
    'r9_split': poly_sub(poly_mul([18,1],poly_pow([1,1],3)),poly_pow([2,1],4)),
    'r9_ramified': poly_sub(poly_mul([9,1],[1,1]),poly_pow([2,1],2)),
    'r9_inert': poly_sub(poly_mul([9,1],poly_pow([1,2],2)),poly_mul([1,1],poly_pow([3,2],2))),
    'r54_split': poly_sub(poly_mul([108,1],poly_pow([1,1],4)),poly_mul(poly_pow([2,1],4),[3,1])),
    'r54_ramified': poly_sub(poly_mul([54,1],poly_pow([1,1],2)),poly_mul(poly_pow([2,1],2),[3,1])),
    'r54_inert': poly_sub(poly_mul([54,1],poly_pow([1,2],3)),poly_mul([2,1],poly_pow([3,2],3))),
}
assert ratio_polynomials == {
    'r9_split':[2,23,33,13], 'r9_ramified':[5,6], 'r9_inert':[0,16,24],
    'r54_split':[60,321,548,390,101], 'r54_ramified':[42,93,49], 'r54_inert':[0,190,528,392],
}
assert all(all(c>=0 for c in p) for p in ratio_polynomials.values())
checks['universal_sparse_ratio_polynomials_ascending'] = ratio_polynomials

ramanujan_cases = 0
for m in range(1,181):
    for k in range(1,181):
        d = gcd(m,k)
        cmk = sum(r*mu(m//r) for r in divs(d))
        assert Q(cmk,phi(m)) == Q(mu(m//d),phi(m//d))
        assert abs(cmk)<=phi(m) and abs(cmk)<=sum(divs(d))
        ramanujan_cases += 1
for n in range(1,N+1):
    assert sum(Q(d,phi(d)) for d in divs(n)) <= tau(3,n)
    assert tau(5,n)**2*tau(2,n) <= tau(50,n)
    assert tau(4,n)*tau(3,n) <= tau(12,n)
    assert tau(2,n)**4*tau(3,n)**2 <= tau(144,n)
    for d in divs(n):
        assert phi(n)>=phi(d)*phi(n//d)
        assert tau(2,n)<=tau(2,d)*tau(2,n//d)
        assert tau(3,n)<=tau(3,d)*tau(3,n//d)
checks['ramanujan_gcd_cases'] = ramanujan_cases
checks['divisor_envelope_endpoint'] = N

# Direct versus reindexed finite principal row with a nonconstant rational kernel.
def kernel(x): return 1/(1+x*x)
def add_scaled(pair,z,scalar):
    z = complex(z)
    return (pair[0]+int(z.real)*scalar,pair[1]+int(z.imag)*scalar)
direct = (Q(0),Q(0))
reindexed = (Q(0),Q(0))
for p in (37,41):
    for m in range(1,30):
        for k in range(1,121):
            cmk = sum(r*mu(m//r) for r in divs(gcd(m,k)))
            scalar = Q(h[m]*cmk,m*phi(m))*kernel(Q(k,p*m))
            direct = add_scaled(direct,g[k],scalar)
    for d in range(1,30):
        for q in range(1,30//d+1):
            if d*q>=30: continue
            for ell in range(1,120//d+1):
                if gcd(ell,q)!=1: continue
                scalar = Q(h[d*q]*mu(q),d*q*phi(q))*kernel(Q(ell,p*q))
                reindexed = add_scaled(reindexed,g[d*ell],scalar)
assert direct == reindexed
checks['finite_gcd_principal_reindexing'] = 'exact complex equality with rational nonconstant kernel'

budgets = {
    'tail_linear': -2022+9,
    'sparse_unweighted': 2*9-2015,
    'sparse_high_weighted': 2*54-2015,
    'sparse_low_weighted': -Q(1997,2)+72,
    'defect_energy': -Q(1853,2)+450,
    'whole_mean_tail': 77+Q(9,2)-Q(953,4),
    'whole_deleted_log': 77+Q(9,2)+225,
    'principal_sparse_l1': -Q(1853,4)+Q(27,2),
    'principal_prefactor': 260+9+108+27,
    'principal_error': 404-Q(1799,4),
    'whole_R2000_tail': Q(101,100)-Q(3,400)*2000,
    'principal_R2000_tail': Q(51,100)-Q(3,400)*2000,
    'Y_length_margin': 2-Q(151,100),
    'g_resonance_margin': Q(151,100)-Q(201,400)-1,
    'support_cutoff_leading_margin': 1-Q(201,400),
    'lambda_derivative_half_multiplier': Q(16000,2),
    'lambda_mass_half_multiplier_without_pi': Q(11,500),
}
assert budgets['sparse_unweighted']==-1997
assert budgets['sparse_high_weighted']==-1907
assert budgets['sparse_low_weighted']==-Q(1853,2)
assert budgets['defect_energy']==-Q(953,2)
assert budgets['whole_mean_tail']==-Q(627,4)
assert budgets['whole_deleted_log']==Q(613,2)<307
assert budgets['principal_error']==-Q(183,4)
assert budgets['whole_R2000_tail']<-10 and budgets['principal_R2000_tail']<-10
assert budgets['Y_length_margin']>0 and budgets['g_resonance_margin']==Q(3,400)
checks['rational_budgets'] = {k:str(v) for k,v in budgets.items()}
checks['sign_check'] = 'Re(-i*(x+i*y))=y=Im(x+i*y)'
checks['complex_nonprincipal_chain'] = [
    'J=-i(R_pr+R_np)+o(1)', 'J=Theta/(a*Mcal)+o(1)',
    '-i*R_pr=Principal/(a*Mcal)+o(1)', 'Theta-Principal=o(Mcal)', '-i*R_np=o(1)',
]
checks['analytic_proof_location'] = 'INDEPENDENT_REVIEW.md, Sections 1-7'
checks['compiler_or_Lean_run'] = False
checks['AFE_used_to_assign_constant'] = False
checks['strict_gain_proved'] = False
checks['result'] = 'PASS: independent exact finite checks only; analytic acceptance is in INDEPENDENT_REVIEW.md'
print(json.dumps(checks,indent=2))
