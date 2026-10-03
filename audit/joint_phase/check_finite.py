"""Finite regressions for PROOF.md; not an asymptotic proof or Lean certificate."""
from __future__ import annotations

import cmath
import hashlib
import json
import math
from collections import defaultdict
from fractions import Fraction as F
from pathlib import Path

from sympy import divisors, factorint, kronecker_symbol, mobius, primitive_root

BASE = Path(__file__).resolve().parent
counts = defaultdict(int)
max_errors = defaultdict(float)


def tau(index, n):
    out = 1
    for exponent in factorint(n).values():
        out *= math.comb(int(exponent) + index - 1, index - 1)
    return out


def conv(a, b):
    out = defaultdict(int)
    for x, ax in a.items():
        for y, by in b.items():
            if ax and by:
                out[x * y] += ax * by
    return {n: v for n, v in out.items() if v}


def cpow(a, k):
    out = {1: 1}
    for _ in range(k):
        out = conv(out, a)
    return out


def arithmetic(discriminant, limit):
    ps = lambda n: int(kronecker_symbol(discriminant, n))
    nu, up = {}, {}
    for n in range(1, limit + 1):
        ds = divisors(n)
        nu[n] = sum(ps(int(d)) for d in ds)
        up[n] = sum(int(mobius(d)) * int(mobius(n // d)) * ps(n // d) for d in ds)
    return ps, nu, up


# Exact exponent and Fejer bookkeeping.
assert -F(2011, 4) + 8 == -F(1979, 4)
assert -F(2011, 4) + 440 == -F(251, 4)
assert -F(2011, 4) + 528 == F(101, 4)
assert F(10, 21) / 20 + F(11, 21) / 22 == F(1, 21)
assert F(10, 21) * 440 + F(11, 21) * 528 == F(10208, 21)
assert -F(2011, 4) + F(10208, 21) == -F(1399, 84)
assert 4 * sum((1 - F(k, 22)) * k * k for k in range(1, 22)) == 3542
assert F(3542, 22) == 161
counts['exact_budget_identities'] = 8

# Prime-power arithmetic including ramification.
for value in (-1, 0, 1):
    nu = [sum(value ** j for j in range(e + 1)) for e in range(13)]
    up = [1, -(1 + value), value] + [0] * 10
    for e in range(13):
        assert sum(up[j] * nu[e - j] for j in range(e + 1)) == int(e == 0)
        assert abs(up[e]) <= nu[e] <= e + 1
        counts['local_convolution_and_envelope'] += 1

# Divisor inequalities at prime powers imply their multiplicative versions.
for a in range(1, 49):
    for b in range(1, 49):
        for e in range(13):
            assert math.comb(e+a-1, a-1)*math.comb(e+b-1, b-1) <= math.comb(e+a*b-1, a*b-1)
            counts['divisor_product_prime_powers'] += 1
for a in range(1, 49):
    for i in range(9):
        for j in range(9):
            assert math.comb(i+j+a-1, a-1) <= math.comb(i+a-1, a-1)*math.comb(j+a-1, a-1)
            counts['divisor_submultiplicativity_prime_powers'] += 1

# Finite instances of the general cutoff lemma B^2 <= X. These tests do not
# pretend to numerically instantiate the astronomical X=D^20 asymptotic scale.
for disc in (-3, -4, 5, 8, 12, 13, -7, -8, -11):
    D = abs(disc)
    _, nu, up = arithmetic(disc, 200)
    squarefree = all(e == 1 for e in factorint(D).values())
    for a in range(1, 201):
        if a % D == 0:
            m = a // D
            target = int(mobius(D))*up[m] if squarefree and math.gcd(m, D) == 1 else 0
            assert up[a] == target
            counts['ramified_deletion_coefficients'] += 1
    for X in (12, 18, 25, 36):
        B = math.isqrt(X)
        f = {n: nu[n] for n in range(B+1, X+1) if nu[n]}
        g = {n: nu[n] for n in range(1, X+1) if nu[n]}
        m = {n: up[n] for n in range(1, X+1) if up[n]}
        residual = conv(m, g)
        residual[1] = residual.get(1, 0) - 1
        maj = conv(f, g)
        for n in range(1, X*X+1):
            assert n > X or residual.get(n, 0) == 0
            assert abs(residual.get(n, 0)) <= 2*maj.get(n, 0)
            counts['double_cutoff_residual_coefficients'] += 1

# Exact rational checks of the 2j-variable harmonic convolution energy.
_, nu, up = arithmetic(5, 5)
f = {n: nu[n] for n in range(3, 6) if nu[n]}
g = {n: nu[n] for n in range(1, 6) if nu[n]}
for j in (1, 2, 3):
    c = cpow(conv(f, g), j)
    energy = sum(F(v*v, n) for n, v in c.items())
    aj = sum(F(v*v*tau(2*j, n), n) for n, v in f.items())
    bj = sum(F(v*v*tau(2*j, n), n) for n, v in g.items())
    assert energy <= aj**j * bj**j
    counts['exact_multivariable_energy'] += 1


def character_family(q):
    generator = int(primitive_root(q))
    logarithm = {}
    v = 1
    for exponent in range(q-1):
        logarithm[v] = exponent
        v = (v*generator) % q
    family = []
    for index in range(2, q-1, 2):
        values = {a: cmath.exp(2j*math.pi*index*exponent/(q-1)) for a, exponent in logarithm.items()}
        family.append(values)
    assert len(family) == (q-3)//2
    return family


# Exact formula tested numerically: the principal correction is negative.
for q in (101, 211, 503):
    fam = character_family(q)
    Y = min(17, (q-1)//3)
    coefficients = {n: (-1)**n*(n % 5 - 2) for n in range(1, Y+1)}
    empirical = sum(abs(sum(a*chi[n]/math.sqrt(n) for n, a in coefficients.items()))**2 for chi in fam)/len(fam)
    cq = (q-1)/(q-3)
    expected = cq*sum(a*a/n for n,a in coefficients.items()) - abs(sum(a/math.sqrt(n) for n,a in coefficients.items()))**2/len(fam)
    error = abs(empirical-expected)
    assert error < 1e-10
    max_errors['primitive_even_orthogonality'] = max(max_errors['primitive_even_orthogonality'], error)
    counts['primitive_even_orthogonality'] += 1

# CRT with actual parity factors, then the unit-twisted root moment bound.
for q in (71, 101):
    fam = character_family(q)
    for disc in (-3, 5, 8):
        D = abs(disc)
        ps = lambda n: int(kronecker_symbol(disc, n))
        parity = int(ps(-1) == -1)
        epspsi = sum(ps(a)*cmath.exp(2j*math.pi*a/D) for a in range(1,D+1))/(1j**parity*math.sqrt(D))
        roots = []
        for ix, chi in enumerate(fam):
            gauss = sum(chi[a]*cmath.exp(2j*math.pi*a/q) for a in range(1,q))
            root = chi[D % q]*ps(q)*epspsi*gauss*gauss/q
            assert abs(abs(root)-1) < 1e-11
            roots.append(root)
            if ix < 3:
                composite = sum((chi.get(a % q, 0))*ps(a)*cmath.exp(2j*math.pi*a/(D*q)) for a in range(1,D*q+1))
                direct = (gauss/math.sqrt(q))*composite/(1j**parity*math.sqrt(D*q))
                err = abs(direct-root)
                assert err < 1e-10
                max_errors['root_crt'] = max(max_errors['root_crt'], err)
                counts['root_crt'] += 1
        for k in range(1, 5):
            for u, v in ((1,1),(2,3),(q+2,2*q+5),(q-1,1)):
                empirical = abs(sum(root**k*chi[u%q]*chi[v%q].conjugate() for chi,root in zip(fam,roots))/len(fam))
                bound = 2*q**(-k)/(q-3)+4*k*(q-1)/(q-3)*q**(-0.5)
                assert empirical <= bound + 1e-10
                counts['twisted_root_moments'] += 1

# Exact complex identities include M=0; high powers are compared globally.
for m in (0, 1, -1j, 2+3j, 1e-7+2e-7j, 1e7-2e7j):
    for s in (0, 1, 1j, 1-2j, -0.5+0.25j):
        for root in (1, -1, 1j, cmath.exp(0.37j)):
            u = root*m/m.conjugate() if m else 1
            w = m*s
            z = root*m*s.conjugate()
            assert abs(z-u*w.conjugate()) <= 1e-12*max(1,abs(z))
            for k in (1, 2, 8, 20, 21):
                lhs = abs(u**k-z**k)
                rhs = abs(1-w**k)
                assert abs(lhs-rhs) <= 1e-11*max(1,lhs,rhs)
                counts['global_phase_power_identity'] += 1

for h in (0.001, 0.01, 0.03, 0.05, 0.075):
    for j in range(-100, 101):
        theta = 2*math.asin(h)*j/100
        z = cmath.exp(1j*theta)
        kernel = abs(sum(z**k for k in range(22)))**2/22
        assert kernel >= 22-3542*h*h-1e-10
        counts['fejer_chord_lower_bound'] += 1

roots22 = [cmath.exp(2j*math.pi*j/22) for j in range(22)]
for k in range(1,22):
    error = abs(sum(z**k for z in roots22)/22)
    assert error < 1e-13
    counts['finite_moment_obstruction'] += 1
assert abs(roots22[11]+1) < 1e-14

result = {
    'status': 'PASS',
    'scope': 'Finite regressions only; the asymptotic argument is in PROOF.md. No Lean run.',
    'checks': dict(counts),
    'max_float_errors': dict(max_errors),
    'exact_exponents': {'L2_norm': '-1979/4', 'L20_norm': '-251/4', 'L22_norm': '101/4', 'L21_norm': '-1399/84'},
    'fejer': {'degree': 21, 'peak': 22, 'chord_error_coefficient': 3542, 'limiting_good_mass': '21/22'},
}
(BASE/'finite_checks.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2))
