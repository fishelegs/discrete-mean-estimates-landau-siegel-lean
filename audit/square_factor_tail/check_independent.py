#!/usr/bin/env python3
"""Finite regressions only; REVIEW.md contains the universal proofs."""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations_with_replacement
from math import comb, gcd, isqrt
from pathlib import Path
import hashlib
import json

COUNTS = Counter()

def check(kind, condition):
    assert condition, kind
    COUNTS[kind] += 1

def tau_pp(k, v):
    assert k >= 0 and v >= 0
    return int(v == 0) if k == 0 else comb(v + k - 1, k - 1)

def local_nu_power(r, v, chi_p):
    if chi_p == 1:
        return tau_pp(2*r, v)
    if chi_p == 0:
        return tau_pp(r, v)
    return tau_pp(r, v//2) if v % 2 == 0 else 0

def weak_compositions(n, k):
    if k == 1:
        yield (n,)
    else:
        for i in range(n + 1):
            for rest in weak_compositions(n-i, k-1):
                yield (i,) + rest

for a in range(1, 9):
    for b in range(1, 9):
        for v in range(101):
            check('matrix_margin_counts', tau_pp(a, v)*tau_pp(b, v) <= tau_pp(a*b, v))

for q in range(1, 10):
    r, K = 2*q, max(0, q*(q-3)//2)
    check('degree_order', r + K >= q*(q+1)//2)
    check('strict_threshold', F(19, r) > F(21, 20))
    for v in range(301):
        check('degree_sequence_counts', tau_pp(q, 2*v) <= tau_pp(q*(q+1)//2, v))
        check('larger_K_inert_variant', tau_pp(q, 2*v) <= tau_pp(q, v)**2 <= tau_pp(q*q, v))
        for chi_p in (-1, 0, 1):
            lhs = local_nu_power(1, v, chi_p)**2 * tau_pp(q, v)
            rhs = sum(local_nu_power(r, v-2*h, chi_p)*tau_pp(K, h)
                      for h in range(v//2+1))
            check('full_local_square_convolution', lhs <= rhs)
            if chi_p == -1 and v % 2:
                check('odd_inert_exact_zero', lhs == rhs == 0)

# Enumerate actual graph-degree images; no surjectivity is inferred beyond these cases.
for q in range(1, 6):
    edges = [(i, j) for i in range(q) for j in range(i, q)]
    for v in range(6):
        image = set()
        for edge_multiset in combinations_with_replacement(range(len(edges)), v):
            degrees = [0]*q
            for e in edge_multiset:
                i, j = edges[e]
                degrees[i] += 1
                degrees[j] += 1
            image.add(tuple(degrees))
        check('enumerated_graph_surjection', image == set(weak_compositions(2*v, q)))

CHARACTERS = [
    (3, [0, 1, -1]),
    (4, [0, 1, 0, -1]),
    (5, [0, 1, -1, -1, 1]),
    (8, [0, 1, 0, -1, 0, -1, 0, 1]),
    (8, [0, 1, 0, 1, 0, -1, 0, -1]),
    (12, [0, 1, 0, 0, 0, -1, 0, -1, 0, 0, 0, 1]),
]
NMAX = 4096
divisors = [[] for _ in range(NMAX+1)]
for d in range(1, NMAX+1):
    for n in range(d, NMAX+1, d):
        divisors[n].append(d)

factorizations = [[] for _ in range(NMAX+1)]
for n in range(2, NMAX+1):
    m, p = n, 2
    while p*p <= m:
        v = 0
        while m % p == 0:
            v += 1
            m //= p
        if v:
            factorizations[n].append((p, v))
        p += 1
    if m > 1:
        factorizations[n].append((m, 1))

def tau_n(k, n):
    out = 1
    for _, v in factorizations[n]:
        out *= tau_pp(k, v)
    return out

TAU = {k: [0] + [tau_n(k, n) for n in range(1, NMAX+1)]
       for k in set(range(1, 10)) | {0, 5, 9, 14, 20, 27}}

for D, vals in CHARACTERS:
    chi = lambda n: vals[n % D]
    check('actual_character_period_zero', sum(vals) == 0)
    for a in range(D):
        check('actual_character_nonunit_zero', (chi(a) == 0) == (gcd(a, D) != 1))
        for b in range(D):
            check('actual_character_multiplicative', chi(a*b) == chi(a)*chi(b))
    # A primitive character cannot be induced by a proper divisor of its conductor.
    for d in divisors[D][:-1]:
        values_by_residue = {}
        contradiction = False
        for n in range(D):
            if gcd(n, D) == 1:
                if n % d in values_by_residue and values_by_residue[n % d] != chi(n):
                    contradiction = True
                values_by_residue[n % d] = chi(n)
        check('actual_character_full_conductor', contradiction)
    nu = [0] + [sum(chi(d) for d in divisors[n]) for n in range(1, NMAX+1)]
    for n in range(1, NMAX+1):
        check('actual_nu_nonnegative', nu[n] >= 0)
    power = [0]*(NMAX+1)
    power[1] = 1
    for r in range(1, 19):
        power = [0] + [sum(power[n//d]*nu[d] for d in divisors[n])
                       for n in range(1, NMAX+1)]
        if r % 2:
            continue
        q, K = r//2, max(0, (r//2)*(r//2-3)//2)
        for n in range(1, NMAX+1):
            rhs = sum(power[n//(h*h)]*TAU[K][h]
                      for h in divisors[n] if h*h <= n and n % (h*h) == 0)
            check('actual_integer_square_convolution', nu[n]**2*TAU[q][n] <= rhs)
    prefix_chi = [0]
    prefix_nu = [0]
    for n in range(1, NMAX+1):
        prefix_chi.append(prefix_chi[-1]+chi(n))
        prefix_nu.append(prefix_nu[-1]+nu[n])
        check('period_partial_bound', abs(prefix_chi[-1]) <= D)
    for N in range(D, 513):
        Y = isqrt(D*N)
        if Y*Y < D*N:
            Y += 1
        long_sum = sum(chi(b)*(N//b) for b in range(Y+1, N+1))
        switched = sum(prefix_chi[N//a]-prefix_chi[Y] for a in range(1, N//(Y+1)+1))
        check('asymmetric_hyperbola_exact', long_sum == switched)
        check('asymmetric_long_bound', abs(long_sum) <= F(2*D*N, Y))
        check('sqrt_cutoff_range', 1 <= Y <= N and Y*Y >= D*N and Y*Y <= 4*D*N)
        main_finite = sum((F(N*chi(b), b) for b in range(1, Y+1)), F(0))
        short = sum(chi(b)*(N//b) for b in range(1, Y+1))
        check('floor_error', abs(short-main_finite) <= Y)
        check('exact_nu_hyperbola', prefix_nu[N] == short + long_sum)

for j, expected_d, expected_b in [(1, -1949, F(-1273, 2)),
                                   (2, -1815, F(-1103, 2)),
                                   (3, -1609, F(-861, 2)),
                                   (4, -1331, F(-547, 2))]:
    q = 2*j+1
    d = 4*q-2015+9*q*(q-1)
    b = 81+18*j+77+F(324+d, 2)
    check('HB_energy', d == expected_d)
    check('HB_budget', b == expected_b == 18*j*j+31*j-F(1371, 2))
    check('HB_negative_budget', b < 0)
    check('PV_error_ratio', (4*q-1)-(4*q-2015) == 2014)
    check('preferred_error_ratio', (4*q-2)-(4*q-2015) == 2013)
    check('square_error_ratio', 4*q-(4*q-2015) == 2015)

check('exact_threshold_margin', F(19, 18)-F(21, 20) == F(1, 180))
check('completion_margin', F(3003, 1000)-(F(501, 500)+2+F(2, 8000)+F(2, 10000)) == F(11, 20000))
check('explicit_absorption_base', F(8, 3)**15 > 2000000 and 2015*15 < F(2000000, 40))
check('direct_original_energy', 4*5-2015+9*5*4 == -1815)
check('direct_original_budget', 72+77+F(144-1815, 2) == F(-1373, 2))
check('one_original_completion', 99+77+F(225+(4*4-2015+9*4*3), 2) == -657)

output = {
    'verdict': 'PASS',
    'assertions': sum(COUNTS.values()),
    'counts': dict(COUNTS),
    'scope': 'Finite regressions only; universal proof is REVIEW.md. No compiler was run.',
    'actual_character_conductors': [D for D, _ in CHARACTERS],
    'maximum_tested_integer': NMAX,
    'maximum_local_valuation': 300,
}
root = Path(__file__).resolve().parent
(root/'CHECKS.json').write_text(json.dumps(output, indent=2)+'\n')
print(json.dumps(output, indent=2))
