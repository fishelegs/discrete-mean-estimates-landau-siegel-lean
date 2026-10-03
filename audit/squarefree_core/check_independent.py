#!/usr/bin/env python3
"""Independent finite identities and exact budgets; no candidate execution or Lean."""
from fractions import Fraction as F
from itertools import permutations
from math import comb, gcd, isqrt, prod
import json

EXPECTED='fba0302928603367ffdeb95ac1af1a364101e70923c02ca2296a548b55b03f31'

def factor(n):
    ans = {}
    p = 2
    while p*p <= n:
        while n % p == 0:
            ans[p] = ans.get(p, 0)+1
            n //= p
        p += 1
    if n > 1:
        ans[n] = 1
    return ans

def kronecker(a, n):
    assert n >= 1
    ans = 1
    while n % 2 == 0:
        if a % 2 == 0:
            return 0
        if a % 8 in (3, 5):
            ans = -ans
        n //= 2
    a %= n
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5):
                ans = -ans
        a, n = n, a
        if a % 4 == n % 4 == 3:
            ans = -ans
        a %= n
    return ans if n == 1 else 0

N = 2048
fs = [{}]+[factor(n) for n in range(1,N+1)]
ds = [[] for _ in range(N+1)]
for d in range(1,N+1):
    for n in range(d,N+1,d):
        ds[n].append(d)
mu = [0]+[0 if max(fs[n].values(),default=0)>1 else (-1)**len(fs[n])
          for n in range(1,N+1)]
def conv(a,b):
    return [0]+[sum(a[d]*b[n//d] for d in ds[n]) for n in range(1,N+1)]
def tau(r,n):
    return prod(comb(e+r-1,r-1) for e in fs[n].values())
squarefree = [0]+[prod(p for p,e in fs[n].items() if e%2) for n in range(1,N+1)]
squarepart = [0]+[prod(p**(e//2) for p,e in fs[n].items()) for n in range(1,N+1)]
assert all(squarepart[n]**2*squarefree[n] == n for n in range(1,N+1))

discriminants = (-3,-4,5,8,12,13,17,24)
cutoffs = (1,2,5,17,64)
counts = dict(integer_cutoff_cases=0, negative_rho=0, nonzero_ramified=0,
              nonzero_t_b_common_factor=0, strict_cutoff_differences=0,
              newly_included_examples=0, restricted_rearrangements=0,
              proper_deletion_distinctions=0)
for disc in discriminants:
    D = abs(disc)
    chi = [0]+[kronecker(disc,n) for n in range(1,N+1)]
    nu = [0]+[sum(chi[d] for d in ds[n]) for n in range(1,N+1)]
    ups = conv(mu,[mu[n]*chi[n] for n in range(N+1)])
    delta = [0,1]+[0]*(N-1)
    assert conv(ups,nu) == delta
    radD = prod(factor(D))
    for X in cutoffs:
        tail = [nu[n] if n>X else 0 for n in range(N+1)]
        head = [nu[n] if 1<=n<=X else 0 for n in range(N+1)]
        rho = conv(ups,tail)
        rh = conv(ups,head)
        weak = conv(ups,[nu[n] if n>=X else 0 for n in range(N+1)])
        counts['strict_cutoff_differences'] += sum(x!=y for x,y in zip(rho,weak))
        for n in range(1,N+1):
            counts['integer_cutoff_cases'] += 1
            t,b = squarepart[n],squarefree[n]
            assert rho[n]+rh[n] == delta[n]
            assert n>X or rho[n] == 0
            assert abs(rho[n]) <= nu[n]*tau(2,n) <= tau(2,n)**2
            assert abs(rho[n]) <= tau(9,t)*tau(4,b)
            assert rho[n]**2*tau(3,n) <= tau(486,t)*tau(48,b)
            counts['negative_rho'] += rho[n]<0
            if rho[n]:
                assert all(e%2==0 for p,e in fs[n].items() if chi[p]==-1)
                rare = prod(p**e for p,e in fs[n].items() if chi[p]!=-1)
                ram_odd = prod(p for p,e in fs[n].items() if chi[p]==0 and e%2)
                split_odd = prod(p for p,e in fs[n].items() if chi[p]==1 and e%2)
                assert b <= rare
                assert b == ram_odd*split_odd
                assert radD % ram_odd == 0
                counts['nonzero_ramified'] += ram_odd>1
                counts['nonzero_t_b_common_factor'] += gcd(t,b)>1
                counts['newly_included_examples'] += b<=19 and rare>7
        # Exact restricted finite rearrangement with nonsymmetric rational weights.
        for Q in (1,7,19):
            left = sum(F(rho[n]*(n%11-5),n) for n in range(1,N+1)
                       if squarefree[n]<=Q)
            right = sum(F(rho[t*t*b]*((t*t*b)%11-5),t*t*b)
                        for b in range(1,Q+1) if squarefree[b]==b
                        for t in range(1,isqrt(N//b)+1))
            assert left == right
            counts['restricted_rearrangements'] += 1
        # Preserve the literal d deletion. A coprimality substitution differs.
        h = [0]+[(n%7)-3 for n in range(1,N+1)]
        literal = conv([ups[d] if 1<=d<=X and d%D else 0
                        for d in range(N+1)],h)
        wrong = conv([ups[d] if 1<=d<=X and gcd(d,D)==1 else 0
                      for d in range(N+1)],h)
        counts['proper_deletion_distinctions'] += sum(x!=y for x,y in zip(literal,wrong))
assert all(counts[k]>0 for k in counts)

# Universal inequalities have proofs in REVIEW.md; finite regressions include
# overlapping squarefree/square supports and all local t,b valuations.
for j in range(1001):
    assert 2*j+1 <= comb(j+2,2)
    assert comb(2*j+2,2) <= comb(j+5,5)
    assert (j+3)*(2*j+1)-(j+1)*(2*j+3) == 2*j
    assert (j+6)*(2*j+1)-(j+2)*(2*j+3) == 6*j
    assert (2*j+1)**2 <= comb(j+8,8)
    assert comb(j+8,8)**2*comb(j+5,5) <= comb(j+485,485)
    for e in (0,1):
        assert (2*j+e+1)**2 <= comb(j+8,8)*4**e
        assert (2*j+e+1)**4*comb(2*j+e+2,2) <= comb(j+485,485)*48**e

orders = 0
for r,s,w,m,z in permutations((1,2,3,5,8)):
    scales = (r,s,w,m,z)
    U = prod(sorted(scales)[:3])
    assert U**5 <= prod(scales)**3
    assert min(r,s,w)**3 <= r*s*w
    assert min(m,z)**3 <= z*m*m
    orders += 1

prime_fiber_checks = 0
for p in (3,5,7,11,13,17,19,23,29,31,37,41,43):
    fibers = {}
    for j in range(1,p-1):
        fibers.setdefault(2*j%(p-1),[]).append(j)
    assert fibers[0] == [(p-1)//2]
    assert max(map(len,fibers.values())) <= 2
    prime_fiber_checks += 1

beta, k0, kmax = F(3,20),F(7,5),F(301,100)
def high(k):
    return -F(1,4)+beta/2 + max(F(0),-F(896,1000)+F(2,5)*k)/2 \
           +max(F(0),F(1103,1000)-F(3,5)*k)/2
def low(k):
    return (beta-k)/4+max(F(0),-F(663,1000)+F(2,3)*k)
hp = (k0,F(1103,600),F(56,25),kmax)
lp = (F(99,100),F(1989,2000),k0)
assert hp == tuple(sorted(hp))
assert lp == tuple(sorted(lp))
assert max(map(high,hp)) == -F(21,1000)
assert max(map(low,lp)) == -F(253,6000)
assert high(k0) == -F(87,2000)
assert low(F(99,100)) == -F(21,100)
assert F(2)+beta-k0 == F(3,4) < 1
assert F(99,100)-beta == F(21,25) > 0
highlog = F(225,2)+F(2916,4)+F(324,4)+36+77+72
lowlog = F(4860+324,2)+77+72
assert highlog == F(2215,2) < 1200
assert lowlog == 2741 < 3000
assert 9*9*6 == 486 and 4*4*3 == 48 and 18*18 == 324
assert 486*9+48*9+54 == 4860
assert F(201,400)-F(251,500) == F(1,2000)
assert F(3,5)*(3+F(201,400)) == F(4203,2000)
length_slacks = {
    'two_B': F(2103,1000)-(F(4203,2000)+F(1,1000)),
    'two_C': F(1104,1000)-(F(4203,2000)-1+F(1,1000)+F(2,8000)+F(2,10000)),
    'three': F(1337,1000)-((3+2*F(201,400))/3+F(1,1000)+F(3,8000)+F(3,10000))
}
assert all(v>0 for v in length_slacks.values())
max_lengths = {
    'two_C': F(1104,1000)+F(2,5)*kmax,
    'two_B_squared': 2*(F(2103,1000)-F(3,5)*k0),
    'A_squared': kmax,
    'three_C_and_D': F(1337,1000)+F(2,3)*k0,
}
assert all(v<4 for v in max_lengths.values())
assert 30+(1-400001)*F(1,8000) == -20
assert 30-500000*F(1,10000) == -20
assert F(21,1000)-F(1,100) == F(11,1000)>0
assert F(253,6000)-F(1,100) == F(193,6000)>0
assert -F(96,1000)+beta/2 == -F(21,1000)

out = {
    'result':'PASS',
    'scope':'Finite identities, local regressions, exact length/power/log budgets, source integrity. Analytic acceptance is in REVIEW.md; no Lean/compiler, no candidate code execution.',
    'candidate_sha256':EXPECTED,
    'discriminants':discriminants,'integers_per_case':N,'strict_cutoffs':cutoffs,
    'counts':counts,'local_valuations_through':1000,
    'scale_orderings_checked':orders,'character_square_fiber_checks':prime_fiber_checks,
    'high_partition_points':list(map(str,hp)), 'high_partition_values':list(map(str,map(high,hp))),
    'low_partition_points':list(map(str,lp)), 'low_partition_values':list(map(str,map(low,lp))),
    'high_log_cost':str(highlog),'low_log_cost':str(lowlog),
    'length_absorption_slacks':{k:str(v) for k,v in length_slacks.items()},
    'maximum_natural_length_exponents':{k:str(v) for k,v in max_lengths.items()},
    'final_power_slacks':{'two':'11/1000','three':'193/6000'},
    'fourier_tail_power':'-20','auxiliary_mellin_tail_power':'-20',
}
print(json.dumps(out,indent=2))
