#!/usr/bin/env python3
"""Exact finite checks only. Does not call Lean or certify analytic estimates."""
from pathlib import Path
from fractions import Fraction as F
from math import comb, isqrt
import hashlib
import json

checks = {}

def record(name, value):
    assert value, name
    checks[name] = True

def tau(r, j):
    return comb(j+r-1, r-1)

local_count = 0
for c in (-1, 0, 1):
    for exponent in range(251):
        nu = sum(c**j for j in range(exponent+1))
        for power, r in ((1, 4), (2, 9)):
            rhs = (tau(2*r, exponent) if c == 1 else
                   tau(r, exponent) if c == 0 else
                   tau(r, exponent//2) if exponent % 2 == 0 else 0)
            assert nu**2 * (exponent+1)**power <= rhs
            local_count += 1
        r = 54
        rhs = (tau(2*r, exponent) if c == 1 else
               tau(r, exponent) if c == 0 else
               tau(r, exponent//2) if exponent % 2 == 0 else 0)
        assert nu**2*(exponent+1)**2*tau(3,exponent) <= rhs
        local_count += 1
record('prime_local_majorants_2259', local_count == 2259)

# The nonnegative coefficients below are full ratio proofs, not a finite sample.
ratio_polynomials = {
 'r4_split': [0,5,4],
 'r4_inert': [1,4],
 'r4_ramified': [2],
 'r9_split': [2,23,33,13],
 'r9_inert': [0,16,24],
 'r9_ramified': [5,6],
 'r54_split': [60,321,548,390,101],
 'r54_inert': [0,190,528,392],
 'r54_ramified': [42,93,49],
}
for j in range(61):
    formulas = {
      'r4_split': (j+8)*(j+1)**2-(j+2)**3,
      'r4_inert': (j+4)*(2*j+1)-(j+1)*(2*j+3),
      'r4_ramified': (j+4)-(j+2),
      'r9_split': (j+18)*(j+1)**3-(j+2)**4,
      'r9_inert': (j+9)*(2*j+1)**2-(j+1)*(2*j+3)**2,
      'r9_ramified': (j+9)*(j+1)-(j+2)**2,
      'r54_split': (j+108)*(j+1)**4-(j+2)**4*(j+3),
      'r54_inert': (j+54)*(2*j+1)**3-(j+2)*(2*j+3)**3,
      'r54_ramified': (j+54)*(j+1)**2-(j+2)**2*(j+3),
    }
    for key, coeff in ratio_polynomials.items():
        assert formulas[key] == sum(a*j**k for k,a in enumerate(coeff))
        assert all(a >= 0 for a in coeff)
record('ratio_polynomial_identities', True)

LIMIT = 420
divisors = [[] for _ in range(LIMIT+1)]
for d in range(1,LIMIT+1):
    for n in range(d,LIMIT+1,d):
        divisors[n].append(d)

def mu(n):
    if n == 1: return 1
    k, sign, p = n, 1, 2
    while p*p <= k:
        if k % p == 0:
            k //= p
            sign = -sign
            if k % p == 0: return 0
        p += 1
    return -sign if k > 1 else sign

def conv(a,b):
    return [0]+[sum(a[d]*b[n//d] for d in divisors[n])
                for n in range(1,LIMIT+1)]

mu_values=[0]+[mu(n) for n in range(1,LIMIT+1)]
ones=[0]+[1]*LIMIT
alpha=[0]+[(1,1j,-1,-1j)[n%4] for n in range(1,LIMIT+1)]
# Gaussian-integer arithmetic here is exact in Python complex at these sizes.
eta=conv(mu_values,alpha)
cases = {
  5: {1:1,2:-1,3:-1,4:1},
  8: {1:1,3:-1,5:-1,7:1},
 12: {1:1,5:-1,7:-1,11:1},
}
positive_examples=[]
negative_examples=[]
identity_count=0
for modulus, values in cases.items():
    chi=[0]+[values.get(n%modulus,0) for n in range(1,LIMIT+1)]
    nu=conv(ones,chi)
    upsilon=conv(mu_values,[a*b for a,b in zip(mu_values,chi)])
    record(f'chi_upsilon_is_mu_mod_{modulus}',conv(chi,upsilon)==mu_values)
    c_inf=conv(chi,alpha)
    for cutoff in (2,5,11,23,47):
        tail=[a if n>cutoff else 0 for n,a in enumerate(nu)]
        short=[a if 1<=n<=cutoff else 0 for n,a in enumerate(nu)]
        rho=conv(upsilon,tail)
        c_x=conv(eta,short)
        rhs=conv(c_inf,rho)
        for n in range(1,LIMIT+1):
            assert c_x[n]-c_inf[n] == -rhs[n]
            assert abs(rho[n]) <= nu[n]*len(divisors[n])
            assert n>cutoff or rho[n]==0
            if rho[n]>0 and len(positive_examples)<3:
                positive_examples.append([modulus,cutoff,n,rho[n]])
            if rho[n]<0 and len(negative_examples)<3:
                negative_examples.append([modulus,cutoff,n,rho[n]])
            identity_count += 1
record('exact_refactorizations_6300',identity_count==6300)
record('rho_has_no_forced_positive_sign',bool(positive_examples and negative_examples))

record('tail_r4_exponent',2*4-2015==-2007)
record('tail_r9_exponent',2*9-2015==-1997)
record('tail_r54_exponent',2*54-2015==-1907)
record('small_rho_weighted_energy',F(-1997,2)+72==F(-1853,2))
record('D_energy',F(-1853,2)+54==F(-1745,2))
record('per_box_energy',77+162-F(1745,4)==F(-789,4))
record('aggregate_energy',F(-789,4)+72==F(-501,4))
record('stronger_E_energy',72-2007==-1935)
record('stronger_old_box_exponent',77+162-F(1935,2)==F(-1457,2))
record('profile_length_exponent',(3+2*F(201,400))/3==F(267,200))
record('low_rho_base_length',F(267,200)+F(2,3)*F(99,100)==F(399,200))
kappa=F(1,1000)
eps=F(1,10000)
final_length=F(399,200)+F(1,1000)+3*kappa/8+3*eps
record('spectral_and_frequency_length_margin',final_length<F(2)-2*kappa)
record('exact_final_length',final_length==F(79867,40000))

# Exhaustive finite geometry checks supplement the universal min inequality.
geometry_count=0
for r in (1,2,8,32):
 for s in (1,2,8,32):
  for w in (1,2,8,32):
   for m in (1,2,8,32):
    for z in (1,2,8,32):
     assert (min(r,s,w)*min(m,z))**3 <= r*s*w*z*m*m
     geometry_count+=1
record('selected_completion_geometry_1024',geometry_count==1024)

result={
 'status':'all finite checks passed; mathematical acceptance is recorded separately',
 'groups':len(checks), 'checks':checks,
 'ratio_polynomials_ascending_coefficients':ratio_polynomials,
 'rho_positive_examples_modulus_cutoff_n_value':positive_examples,
 'rho_negative_examples_modulus_cutoff_n_value':negative_examples,
 'final_length_exponent':str(final_length),
 'remaining_length_margin':str(F(2)-2*kappa-final_length),
 'warning':'No Lean, exceptional-character instance, analytic certification, or signed gain.'
}
print(json.dumps(result,indent=2))
