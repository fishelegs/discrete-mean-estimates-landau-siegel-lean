#!/usr/bin/env python3
"""Exact checks for the source proof; no actual large-D zero data is simulated."""
from pathlib import Path
from fractions import Fraction as Q
import hashlib
import json
import sympy as s

OUT = Path(__file__).resolve().parent
REPO = OUT.parents[1]
checks = {}

# Verify the differential identities for arbitrary smooth-profile terminal data.
t, v, ell, bj, bk, bl = s.symbols('t v ell bj bk bl', nonzero=True)
tau = v-t
R = tau*s.exp(ell*tau)
assert s.simplify(s.diff(R,t,2)+2*ell*s.diff(R,t)+ell**2*R) == 0
assert R.subs(t,v) == 0
assert s.diff(R,t).subs(t,v) == -1
Fkernel = (1+(ell-bj)*tau)*s.exp(ell*tau)
assert s.simplify(-s.diff(R,t)-bj*R-Fkernel) == 0
Rminus = tau*s.exp(-ell*tau)
WRminus = (1-(1+ell*tau)*s.exp(-ell*tau))/ell**2
assert s.simplify(s.diff(WRminus,t)+Rminus) == 0
assert WRminus.subs(t,v) == 0
Gkernel = bk*bl/ell**2 + (1-bk*bl/ell**2-(bk-ell)*(bl-ell)/ell*tau)*s.exp(-ell*tau)
assert s.simplify(-s.diff(Rminus,t)+(bk+bl)*Rminus+bk*bl*WRminus-Gkernel) == 0
checks['superposition_and_both_residue_kernels'] = 'exact differential identities'

# Check the true Pi local collapse for arbitrary chi(q), including 0 and 1.
q, x = s.symbols('q x', real=True)
pi_r1 = (1-x/q)**-1 * (1-1/q-x/q)/(1-1/q)
pi_rq = (1-x/q)**-1
assert s.factor(pi_r1+pi_rq/(q-1)-q/(q-1)) == 0
assert pi_r1.subs({q:2,x:1}) == 0
for qq in [2,3,5,7,11]:
    for xx in [-1,0,1]:
        assert s.simplify((pi_r1+pi_rq/(q-1)).subs({q:qq,x:xx})-s.Rational(qq,qq-1)) == 0
checks['pi_prime_power_collapse'] = 'universal rational identity, including ramification and vanishing Pi'

# Expand the Hermitian polarization after the one integration by parts
# integral f' Wbar(g) = integral f bar(g), for compact f.
# Coefficients stand for integral f'g', f'g, fg', fg, fWg, Wfg.
pi = s.pi
beta = [s.I*pi,2*s.I*pi,3*s.I*pi]
weights = [s.Rational(1,2),s.Integer(2),s.Rational(3,2)]
coeff = [s.Integer(0)]*6
for j,(b,w) in enumerate(zip(beta,weights)):
    others = [beta[k] for k in range(3) if k != j]
    bsum = sum(others)
    prod = s.prod(others)
    raw = [1,-bsum,b,-b*bsum-prod,-b*prod,0]
    adjoint = [s.conjugate(raw[0]),s.conjugate(raw[2]),s.conjugate(raw[1]),
               s.conjugate(raw[3]),s.conjugate(raw[5]),s.conjugate(raw[4])]
    coeff = [s.simplify(c+w/pi*(u+z)) for c,u,z in zip(coeff,raw,adjoint)]
assert coeff == [8/pi,-24*s.I,24*s.I,88*pi,24*s.I*pi**2,-24*s.I*pi**2]
checks['full_complex_polarization'] = [str(z) for z in coeff]

# Every exponent is rational; H = L^(11/10), B = L^9.
Hexp, Bexp = Q(11,10), Q(9)
raw = {
  'actual_first_times_xi_interior': -6-14+9,
  'actual_first_times_xi_moving_layer': -6+(5*Hexp-2*Bexp)+9,
  'first_interior_times_xi_main': -15-7+9,
  'first_moving_layer_times_xi_main': (3*Hexp-2*Bexp)-7+9,
}
assert raw['actual_first_times_xi_moving_layer'] == Q(-19,2)
assert max(raw.values()) == Q(-19,2)
assert Q(-19,2)+Bexp == Q(-1,2)
assert Q(-19,2)+2 == Q(-15,2)
checks['raw_Sj_error_exponents'] = {k:str(z) for k,z in raw.items()}
checks['normalized_arithmetic_error_exponent'] = '-1/2, with fixed polylog and a^-1 retained'

h=Q(1,2000)
left=[Q(502,1000),Q(50275,100000),Q(5035,10000)]
intervals=[(a,a+h) for a in left]
assert intervals[0][0] == Q(502,1000)
assert intervals[-1][-1] == Q(504,1000)
assert all(intervals[i][1] < intervals[i+1][0] for i in range(2))
assert all(Q(1,2) <= a <= b <= Q(504,1000) for a,b in intervals)
assert 8/s.Rational(h.numerator,h.denominator)/pi == 16000/pi
assert 88*pi*s.Rational(h.numerator,h.denominator) == 11*pi/250
checks['three_fixed_profile_supports']=[[str(a),str(b)] for a,b in intervals]
checks['lambda_scaling'] = '16000 I1/pi + 11 pi I0/250'

# Check the ramified density Euler factor; no lower bound on density is assumed.
assert s.factor((1-1/q)/(1-1/q**2)-q/(q+1)) == 0
checks['ramified_density_factor'] = 'q/(q+1), exact'

sources = json.loads((OUT/'SOURCE_HASHES.json').read_text())
for relative, expected in sources.items():
    assert hashlib.sha256((REPO/relative).read_bytes()).hexdigest()==expected, relative
(OUT/'CHECKS.json').write_text(json.dumps(checks,indent=2)+'\n')
print(json.dumps(checks,indent=2))
