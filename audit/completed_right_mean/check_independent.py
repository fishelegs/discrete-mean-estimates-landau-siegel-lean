#!/usr/bin/env python3
"""Portable independent exact mathematical checks; prints JSON, never writes files."""
from collections import defaultdict
from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from math import comb, gcd
import json
checks={}
counts={}
# Every exponent is exact rational arithmetic, independently reconstructed.
v = Q(201,400)
y = Q(151,100)
assert v*2 == Q(201,200) < 2
assert y < 2 and v < 1 and y+v > 2
assert y-v == Q(403,400)
assert 1+v-y == -Q(3,400)
assert y-Q(1,2) == Q(101,100)
assert Q(101,100)-Q(3,400)*1600 < -10
assert (1-v)-Q(49,100) == Q(3,400)
assert Q(1)+Q(251,500)-v == Q(1999,2000)
assert Q(1)+v-Q(251,500) == Q(2001,2000)
checks['lengths_tail_resonance_and_power_margins'] = True
assert 9+12*2 == 33
assert 33+49 == 82
assert 9*4 == 36
assert Q(2*82+36+3*77-739,4) == -77
assert 77+Q(82+9,2) == Q(245,2)
assert Q(245,2)+400-9-519 == -Q(11,2)
assert Q(245,2)+405-9-519 == -Q(1,2)
checks['energy_holder_and_gaussian_exponents'] = True

# Offsets are polynomials alpha*(constant+coefficient*c*alpha*L).
d1 = (1,-5)
d2 = (2,2)
d3 = (3,-3)
assert tuple(a+b for a,b in zip(d1,d2)) == d3
assert tuple(Q(a+b+c,2) for a,b,c in zip(d1,d2,d3)) == d3
checks['exact_shift_sum_and_positive_branch_exponent'] = True

# Prime baselines and higher prime-power majorants, including ramification.
for chi in (-1,0,1):
    amps = (chi,chi,1,1,1)
    cosine_at_zero = sum(a*a for a in amps)+2*sum(amps[i]*amps[j]
        for i in range(5) for j in range(i+1,5))
    assert cosine_at_zero == (3+2*chi)**2 <= 13+12*chi
    assert 13+12*chi == 1+12*(1+chi)
checks['all_prime_baselines_and_cosine_coefficients'] = True
for j in range(501):
    assert comb(j+6,6)**2 <= comb(j+48,48)
    assert (j+7)**2 <= (j+49)*(j+1)
    assert comb(j+7,6) <= 7*comb(j+6,6)
    for chi in (-1,0,1):
        short = [1,abs(1+chi),abs(chi)]
        majorant = sum(short[i]*comb(j-i+4,4) for i in range(min(2,j)+1))
        assert majorant <= comb(j+6,6)
checks['all_prime_power_short_majorant_and_tau49_envelope'] = True
counts['local_prime_power_indices'] = 501

# Polynomial division / cyclotomic reduction, with exact integer coefficients.
def trim(a):
    a=list(a)
    while len(a)>1 and a[-1]==0:
        a.pop()
    return a

def divide(a,b):
    a=trim(a)
    b=trim(b)
    assert b[-1]==1
    quotient=[0]*max(1,len(a)-len(b)+1)
    while len(a)>=len(b) and a!=[0]:
        d=len(a)-len(b)
        coefficient=a[-1]
        quotient[d]=coefficient
        for i,bi in enumerate(b):
            a[d+i]-=coefficient*bi
        a=trim(a)
    return trim(quotient),trim(a)

@lru_cache(None)
def cyclotomic(n):
    a=[-1]+[0]*(n-1)+[1]
    for d in range(1,n):
        if n%d==0:
            a,remainder=divide(a,cyclotomic(d))
            assert remainder==[0]
    return tuple(a)

def cyclo_reduce(coeff,n):
    a=[0]*n
    for exponent,value in coeff.items():
        a[exponent%n]+=value
    return tuple(divide(a,cyclotomic(n))[1])

def tensor_reduce(coeff,p):
    # zeta_p and zeta_(p-1), coprime orders: exact tensor basis reduction.
    rows={a:defaultdict(int) for a in range(p)}
    for (a,b),value in coeff.items():
        rows[a%p][b%(p-1)]+=value
    short={a:cyclo_reduce(row,p-1) for a,row in rows.items()}
    width=max(map(len,short.values()))
    columns=[]
    for b in range(width):
        column={a:row[b] for a,row in short.items() if b<len(row)}
        columns.append(cyclo_reduce(column,p))
    while len(columns)>1 and columns[-1]==(0,):
        columns.pop()
    return tuple(columns)

gauss_cases=0
reciprocity_cases=0
for p in (3,5,7,11,13,17,19):
    generator=next(g for g in range(1,p)
        if len({pow(g,j,p) for j in range(p-1)})==p-1)
    logs={pow(generator,j,p):j for j in range(p-1)}
    for m in range(1,p):
        for k in range(0,2*p+1):
            # Direct sum over all nontrivial characters j=1,...,p-2.
            lhs=defaultdict(int)
            if k%p:
                for j in range(1,p-1):
                    for a in range(1,p):
                        exponent=j*(-logs[a]+logs[k%p]-logs[m])
                        lhs[(a,exponent)]+=1
            # Multiply the desired normalized formula by p.
            rhs=defaultdict(int)
            target=k*pow(m,-1,p)%p
            rhs[(target,0)]+=p-1
            rhs[(0,0)]+=1
            if k%p==0:
                rhs[(0,0)]-=p
            assert tensor_reduce(lhs,p)==tensor_reduce(rhs,p)
            gauss_cases+=1
            if m>1:
                r=Q(pow(m,-1,p),p)+Q(pow(p,-1,m),m)-Q(1,p*m)
                assert r.denominator==1
                reciprocal_phase=Q(k*pow(m,-1,p),p)-Q(k,p*m)+Q(k*pow(p,-1,m),m)
                assert reciprocal_phase.denominator==1
                reciprocity_cases+=1
checks['direct_primitive_character_gauss_sum_exact_cyclotomic'] = True
checks['principal_and_long_nonunit_branches_exact'] = True
checks['additive_reciprocity_and_delta_phase_exact'] = True
counts['exact_gauss_cases'] = gauss_cases
counts['exact_reciprocity_cases'] = reciprocity_cases

# A finite coefficient model with three independent multiplicative phase
# variables; keys multiply componentwise so this is exact symbolic arithmetic.
@lru_cache(None)
def divisors(n):
    return tuple(d for d in range(1,n+1) if n%d==0)

def mu(n):
    sign=1
    d=2
    while d*d<=n:
        if n%d==0:
            n//=d
            sign=-sign
            if n%d==0:
                return 0
        while n%d==0:
            n//=d
        d+=1
    return -sign if n>1 else sign

def chi_value(D,n):
    return ((0,1,-1,-1,1)[n%5] if D==5
        else (0,1,0,-1,0,-1,0,1)[n%8])

def clean(poly):
    return {k:v for k,v in poly.items() if v}

def add_scaled(target,poly,scale):
    for key,value in poly.items():
        target[key]+=value*scale

@lru_cache(None)
def db(D,n):
    out=defaultdict(int)
    for a in divisors(n):
        for n1 in divisors(n//a):
            for n2 in divisors(n//a//n1):
                n3=n//a//n1//n2
                out[(n1,n2,n3)]+=chi_value(D,a)
    return clean(out)

@lru_cache(None)
def upsilon(D,n):
    return sum(mu(d)*mu(n//d)*chi_value(D,n//d) for d in divisors(n))

def profile(v):
    return Q((v%5)-2,2) if 3<=v<=17 else Q(0)

masked_cases=0
nonunit_mollifier_seen=False
for D,X in product((5,8),(4,8,13)):
    for k in range(1,121):
        direct=defaultdict(Q)
        grouped=defaultdict(Q)
        for d in divisors(k):
            if d>X or d%D==0:
                continue
            if gcd(d,D)>1 and upsilon(D,d):
                nonunit_mollifier_seen=True
            for v in divisors(k//d):
                add_scaled(direct,db(D,k//d//v),upsilon(D,d)*chi_value(D,v)*profile(v))
        # Independent grouping into a masked H times four-factor convolution.
        for v in divisors(k):
            if not profile(v):
                continue
            for ell in divisors(k//v):
                d=k//v//ell
                if d<=X and d%D:
                    add_scaled(grouped,db(D,ell),chi_value(D,v)*profile(v)*upsilon(D,d))
        assert clean(direct)==clean(grouped)
        masked_cases+=1
assert nonunit_mollifier_seen
checks['finite_masked_total_coefficients_exact_symbolic'] = True
checks['D_deletion_not_replaced_by_D_coprimality'] = True
counts['masked_convolution_cases'] = masked_cases

print(json.dumps({'checks':checks,'counts':counts,'limits':'Finite exact algebra only; no analytic theorem certification, exceptional-character experiment, Lean certification, or signed gain.'},indent=2))
