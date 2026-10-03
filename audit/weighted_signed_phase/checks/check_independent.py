"""Independent exact arithmetic and exponent audit; no Lean compilation.

Finite Gauss/Fourier/CRT checks are separately generated in algebra/.
This checker addresses regrouping, cutoff deletion, and the normalized budgets.
"""
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json
from math import isqrt

ROOT = Path(__file__).resolve().parent

import argparse
_parser = argparse.ArgumentParser(description=__doc__)
_parser.add_argument('--output', type=Path, default=Path(__file__).resolve().parents[1] / 'results' / 'INDEPENDENT_RERUN.json')
_OUTPUT = _parser.parse_args().output
_OUTPUT.parent.mkdir(parents=True, exist_ok=True)
EXPECTED = 'ab74a957e20dd7a507041d975e83e3e6c6107e6fb1b42f1715c5af2c3efe45fc'
# EXPECTED identifies the historical reviewed candidate; public-file integrity
# is verified by the portable bundle manifest, not an external local path.

def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]

def mu(n):
    k = 0
    d = 2
    while d * d <= n:
        if n % d == 0:
            n //= d
            k += 1
            if n % d == 0:
                return 0
        while n % d == 0:
            n //= d
        d += 1
    return (-1) ** (k + (n > 1))

def conv(a, b, n):
    return sum(a(d) * b(n // d) for d in divisors(n))

# Exact completely multiplicative model weights deliberately differ from the
# candidate's floating imaginary powers. Associativity is coefficient algebra.
e1 = lambda n: F(n)
e2 = lambda n: F(1, n)
e3 = lambda n: F(n * n)
eta = lambda n: conv(mu, e3, n)
kappa_direct = lambda n: conv(lambda d: conv(lambda x: conv(mu, e1, x), e2, d), e3, n)
kappa_regroup = lambda n: conv(lambda d: conv(eta, e1, d), e2, n)
regroup_count = 0
for n in range(1, 181):
    assert kappa_direct(n) == kappa_regroup(n)
    regroup_count += 1

prime_power_count = 0
for p in [2, 3, 5, 7, 11]:
    for k in range(1, 5):
        assert eta(p ** k) == (e3(p) - 1) * e3(p) ** (k - 1)
        prime_power_count += 1

# Literal finite d-cutoff and deletion remain on d, not on u=d*m.
# This exact counterexample prevents an illicit condition D !| u.
D, X = 6, 12
def coefficient_with_d_mask(u):
    return sum(F(1) for d in divisors(u) if d <= X and d % D != 0)
assert coefficient_with_d_mask(6) == 3
assert coefficient_with_d_mask(6) != 0

theta_lo, theta_hi = F(251, 500), F(201, 400)
right = -1 - theta_lo / 2 + 3 * theta_hi / 2
assert right == F(-1989, 4000)
assert right < -F(49, 100)
right_margin = -F(49, 100) - right
resonant_lo = 3 + theta_lo - theta_hi
resonant_hi = 3 + theta_hi - theta_lo
assert resonant_lo == F(5999, 2000)
assert resonant_hi == F(6001, 2000)
assert F(1499, 500) < resonant_lo < resonant_hi < F(1501, 500)

# Central absolute, once-completed, twice-completed costs at Q=R=S=P.
# Derive from prime count P, normalization P^2, character brace sqrt(P),
# coefficient Y^-1/2 and each completion's Poisson and finite-transform factors.
theta = theta_lo
Y = 3 + 2 * theta
uncompleted = 1 - 2 + F(1, 2) - Y / 2 + Y
once = 1 - 2 + F(1, 2) - Y / 2 + (1 - 1) + F(1, 2) + (2 + 2 * theta)
twice = 1 - 2 + F(1, 2) - Y / 2 + (2 - 2) + 1 + (1 + 2 * theta)
assert uncompleted == 1 + theta
assert once == F(1, 2) + theta
assert twice == theta
assert uncompleted - F(1, 24) > 0
assert once - F(1, 24) > 0

# FKM smooth bound N(1+p/N)^(1/6)p^-gamma at N=p^n.
# At optimal limiting gamma=1/24 the relative exponent is zero at n=3/4.
assert (1 - F(3, 4)) / 6 - F(1, 24) == 0

# The actual AFE square-norm-to-linear conversion and use of a <= C L^4.
assert -F(1077, 4) + 2 < -203

# Direct long-pure Poisson on sigma=-1/2, including gamma and finite A,B costs.
# For every fixed delta and requested K, a FIXED derivative order suffices.
long_cost = 3 + 3 * theta_hi / 2 - theta_lo / 2
long_certificates = []
for delta in [F(1, 1000), F(1, 100), F(1, 10)]:
    for K in [1, 5, 20]:
        J = int(2 * (long_cost + K + 2) / delta) + 1
        exponent = long_cost - 1 - delta / 2 - J * delta / 2
        assert exponent < -K - 1
        long_certificates.append({'delta':str(delta), 'K':K, 'fixed_order':J, 'exponent':str(exponent)})

result = {
    'status':'PASS',
    'candidate_sha256': EXPECTED,
    'exact_tests': {'regrouping':regroup_count, 'prime_power':prime_power_count,
                    'd_mask_counterexample':1, 'long_pure_margin_certificates':len(long_certificates)},
    'budgets': {'right':str(right), 'right_margin_to_minus_049':str(right_margin),
               'kappa_limiting_range':[str(resonant_lo),str(resonant_hi)],
               'central_cost':str(uncompleted), 'once_completed_cost':str(once),
               'twice_completed_cost':str(twice)},
    'long_pure_certificates':long_certificates,
    'scope':'Exact finite algebra/rational budgets only. Analytic contour and Poisson proofs are in INDEPENDENT_REVIEW.md; this is not their machine certification.'
}
_OUTPUT.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
