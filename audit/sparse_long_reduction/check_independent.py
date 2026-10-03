#!/usr/bin/env python3
"""Portable independent finite algebra and numerical normalization checks.
Analytic uniformity is proved in INDEPENDENT_REVIEW.md, not finite sampling.
Prints JSON only and never invokes Lean or writes files.
"""
from fractions import Fraction as F
from itertools import product
from math import comb, exp, log, pi, sqrt
import cmath,json
import sympy as sp
from scipy.integrate import quad
checks={}
counts={}
def record(name, condition):
    assert condition, name
    checks[name]=True
j = sp.symbols('j', integer=True, nonnegative=True)
ratio_formulas = {
    'split4': (j+8)*(j+1)**2-(j+2)**3,
    'inert4': (j+4)*(2*j+1)-(j+1)*(2*j+3),
    'ramified4': (j+4)-(j+2),
    'split9': (j+18)*(j+1)**3-(j+2)**4,
    'inert9': (j+9)*(2*j+1)**2-(j+1)*(2*j+3)**2,
    'ramified9': (j+9)*(j+1)-(j+2)**2,
    'split54': (j+108)*(j+1)**4-(j+2)**4*(j+3),
    'inert54': (j+54)*(2*j+1)**3-(j+2)*(2*j+3)**3,
    'ramified54': (j+54)*(j+1)**2-(j+2)**2*(j+3),
}
ratio_coefficients = {}
for name, expr in ratio_formulas.items():
    p = sp.Poly(sp.expand(expr), j)
    coeff = [int(p.nth(k)) for k in range(p.degree()+1)]
    assert all(c >= 0 for c in coeff)
    ratio_coefficients[name] = coeff
record('symbolic_local_ratio_polynomial_proofs', True)

def tau_local(r, exponent):
    return comb(exponent+r-1, r-1)

local_count = 0
for c, exponent in product((-1, 0, 1), range(401)):
    nu = sum(c**k for k in range(exponent+1))
    for r, weight in ((4, exponent+1),
                      (9, (exponent+1)**2),
                      (54, (exponent+1)**2*tau_local(3, exponent))):
        rhs = (tau_local(2*r, exponent) if c == 1 else
               tau_local(r, exponent) if c == 0 else
               tau_local(r, exponent//2) if exponent % 2 == 0 else 0)
        assert nu*nu*weight <= rhs
        local_count += 1
    assert nu**2*(exponent+1)**2*tau_local(3, exponent)**2 <= tau_local(144, exponent)
record('local_majorants_and_tau144_samples', True)
counts['local_convolution_majorants'] = local_count

LIMIT = 600
divs = [[] for _ in range(LIMIT+1)]
for d in range(1, LIMIT+1):
    for n in range(d, LIMIT+1, d):
        divs[n].append(d)

def mobius_omega(n):
    k, p, omega, square = n, 2, 0, False
    while p*p <= k:
        exponent = 0
        while k % p == 0:
            k //= p
            omega += 1
            exponent += 1
        square |= exponent > 1
        p += 1
    if k > 1:
        omega += 1
    return (0 if square else (-1)**omega), omega

mu = [0]+[mobius_omega(n)[0] for n in range(1, LIMIT+1)]
one = [0]+[1]*LIMIT
units = [(1,0), (0,1), (-1,0), (0,-1)]
alpha = [(0,0)]+[units[mobius_omega(n)[1] % 4] for n in range(1, LIMIT+1)]

def conv_int(a,b):
    return [0]+[sum(a[d]*b[n//d] for d in divs[n]) for n in range(1, LIMIT+1)]

def conv_gauss_int(a,b):
    return [(0,0)]+[(sum(a[d][0]*b[n//d] for d in divs[n]),
                     sum(a[d][1]*b[n//d] for d in divs[n])) for n in range(1,LIMIT+1)]

eta = conv_gauss_int(alpha, mu)
chi_maps = {
    5: {1:1,2:-1,3:-1,4:1},
    8: {1:1,3:-1,5:-1,7:1},
    12: {1:1,5:-1,7:-1,11:1},
    7: {k:(1 if k in {x*x % 7 for x in range(1,7)} else -1) for k in range(1,7)},
}
identity_count = 0
signs = set()
parities = set()
for modulus, residues in chi_maps.items():
    chi = [0]+[residues.get(n % modulus,0) for n in range(1,LIMIT+1)]
    parities.add(chi[modulus-1])
    nu = conv_int(one,chi)
    upsilon = conv_int(mu,[mu[n]*chi[n] for n in range(LIMIT+1)])
    assert all(x>=0 for x in nu)
    assert conv_int(chi,upsilon)==mu
    cinf = conv_gauss_int(alpha,chi)
    for cutoff in (1,2,3,7,15,31,63,127):
        tail = [nu[n] if n>cutoff else 0 for n in range(LIMIT+1)]
        short = [nu[n] if 0<n<=cutoff else 0 for n in range(LIMIT+1)]
        rho = conv_int(upsilon,tail)
        cx = conv_gauss_int(eta,short)
        refactor = conv_gauss_int(cinf,rho)
        for n in range(1,LIMIT+1):
            assert (cx[n][0]-cinf[n][0],cx[n][1]-cinf[n][1]) == \
                   (-refactor[n][0],-refactor[n][1])
            assert abs(rho[n]) <= nu[n]*len(divs[n])
            assert n>cutoff or rho[n]==0
            signs.add((rho[n]>0)-(rho[n]<0))
            identity_count += 1
record('exact_gaussian_integer_convolutions_support_majorants', True)
record('rho_has_both_signs', -1 in signs and 1 in signs)
record('both_character_parities_tested', parities == {-1,1})
counts['finite_refactorizations'] = identity_count

geometry_count = 0
for r,s,w,z,m in product((1,2,4,16,64), repeat=5):
    r0,c0 = min(r,s,w),min(m,z)
    selected = r*s*w//r0 * max(m,z)
    assert selected*r0*c0 == r*s*w*z*m
    assert (r0*c0)**3 <= r*s*w*z*m*m
    geometry_count += 1
record('selected_three_factor_geometry', True)
counts['geometry_samples'] = geometry_count

record('r4_tail',2*4-2015 == -2007)
record('r9_tail',2*9-2015 == -1997)
record('r54_tail',2*54-2015 == -1907)
record('split_D108_energy',F(-1997,2)+F(144,2) == F(-1853,2))
record('D_energy',F(-1853,2)+2*27 == F(-1745,2))
record('C_energy',9*36 == 324)
record('per_octuple',77+F(324,2)-F(1745,4) == F(-789,4))
record('aggregate',F(-789,4)+72 == F(-501,4))
record('optional_E_energy',72-2007 == -1935)
record('optional_box_energy',77+162-F(1935,2) == F(-1457,2))
record('D_power',F(1+20,3) == 7)
record('profile_endpoint',(3+2*F(201,400))/3 == F(267,200))
base = F(267,200)+F(2,3)*F(99,100)
record('low_rho_base_length',base == F(399,200))
final_exponent = base+F(1,1000)+3*F(1,8000)+3*F(1,10000)
margin = F(2)-F(2,1000)-final_exponent
record('whole_polynomial_length',final_exponent == F(79867,40000) and margin == F(53,40000))
record('fourier_tail_fixed_order',30+(1-400001)*F(1,8000) == -20)
record('auxiliary_tail_fixed_order',30-500000*F(1,10000) == -20)

def bump(v):
    return exp(-1/((v-.5)*(2-v))) if .5<v<2 else 0.0

def cint(fn,lo,hi):
    re = quad(lambda x:fn(x).real,lo,hi,epsabs=1e-11,epsrel=1e-11,limit=400)[0]
    im = quad(lambda x:fn(x).imag,lo,hi,epsabs=1e-11,epsrel=1e-11,limit=400)[0]
    return complex(re,im)

fourier_count = 0
max_error = 0.0
for tau,sigma,q in product((-20,-1,-.5,0,.5,1,20),(-1,1),(7,35)):
    Y,h = 1.7,2
    direct = cint(lambda x:x**complex(-.5,tau)*bump(x/Y)*
                 cmath.exp(-2j*pi*sigma*h*x/q),Y/2,2*Y)/sqrt(q)
    if abs(tau)>=1:
        b,eta_sign = abs(tau),1 if tau>0 else -1
        y = 2*pi*h*Y/(q*b)
        symbol = sqrt(b/(2*pi))*cint(
            lambda z:z**(-.5)*bump(z/y)*
            cmath.exp(1j*b*(eta_sign*log(z)-sigma*z+eta_sign)),y/2,2*y)
        rhs = h**(-.5)*cmath.exp(1j*tau*log(q*b/(2*pi*exp(1)*h)))*symbol
    else:
        y = h*Y/q
        symbol = cint(lambda z:z**complex(-.5,tau)*bump(z/y)*
                      cmath.exp(-2j*pi*sigma*z),y/2,2*y)
        rhs = h**(-.5)*cmath.exp(1j*tau*log(q/h))*symbol
    error = abs(direct-rhs)
    max_error = max(max_error,error)
    assert error <= 5e-10*max(1,abs(direct))
    fourier_count += 1
record('positive_negative_zero_height_fourier_normalizations', True)
counts['numerical_fourier_checks'] = fourier_count

result = {
    'decision':'ACCEPT at source level in INDEPENDENT_REVIEW.md; finite checks are supplementary',
    'groups':len(checks),
    'checks':checks,
    'counts':counts,
    'ratio_polynomials_ascending':ratio_coefficients,
    'length_exponent':str(final_exponent),
    'length_margin_below_2_minus_2kappa':str(margin),
    'max_numerical_fourier_absolute_error':max_error,
    'warning':'No compiler invocation, exceptional-character instance, transitive Lean closure, or signed gain is certified.'
}
print(json.dumps(result,indent=2))
