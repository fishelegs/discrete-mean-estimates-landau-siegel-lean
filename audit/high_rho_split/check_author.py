#!/usr/bin/env python3
"""Finite source-level regression checks; no Lean/compiler calls."""
from fractions import Fraction as F
from math import comb, gcd, isqrt
import json

N = 4000

def factors(n):
    ans = []
    p = 2
    while p * p <= n:
        if n % p == 0:
            j = 0
            while n % p == 0:
                n //= p
                j += 1
            ans.append((p, j))
        p += 1
    if n > 1:
        ans.append((n, 1))
    return ans

FAC = [[], []] + [factors(n) for n in range(2, N + 1)]
DIV = [[] for _ in range(N + 1)]
for d in range(1, N + 1):
    for n in range(d, N + 1, d):
        DIV[n].append(d)

def conv(a, b):
    z = [0] * (N + 1)
    for d in range(1, N + 1):
        if a[d]:
            for m in range(1, N // d + 1):
                z[d * m] += a[d] * b[m]
    return z

def chi(D, n):
    if gcd(D, n) != 1:
        return 0
    if D == 4:
        return 1 if n % 4 == 1 else -1
    if D == 8:
        return 1 if n % 8 in (1, 7) else -1
    if D == 12:
        return 1 if n % 12 in (1, 11) else -1
    return 1 if pow(n % D, (D - 1) // 2, D) == 1 else -1

def mul_local(local):
    a = [0] * (N + 1)
    a[1] = 1
    for n in range(2, N + 1):
        v = 1
        for p, j in FAC[n]:
            v *= local(p, j)
        a[n] = v
    return a

mu = mul_local(lambda p, j: -1 if j == 1 else 0)
tau = mul_local(lambda p, j: j + 1)
Q = [0] * (N + 1)
Qinv = [0] * (N + 1)
for t in range(1, isqrt(N) + 1):
    Q[t*t] = 1
    Qinv[t*t] = mu[t]
delta = [0] * (N + 1)
delta[1] = 1
assert conv(Q, Qinv) == delta

checked = 0
negative_rho_seen = False
ramified_examples = 0
for D in (3, 4, 5, 8, 12, 13):
    def nu_local(p, j):
        c = chi(D, p)
        return (j + 1) if c == 1 else (1 if c == 0 or j % 2 == 0 else 0)
    def ups_local(p, j):
        c = chi(D, p)
        return -(1 + c) if j == 1 else (c if j == 2 else 0)
    def c_local(p, j):
        c = chi(D, p)
        return 2 if c == 1 else (1 if c == 0 and j == 1 else 0)
    def ci_local(p, j):
        c = chi(D, p)
        return 2 * (-1)**j if c == 1 else ((-1)**j if c == 0 else 0)
    nu = mul_local(nu_local)
    ups = mul_local(ups_local)
    cseq = mul_local(c_local)
    ciseq = mul_local(ci_local)
    assert conv(Q, cseq) == nu
    assert conv(Qinv, ciseq) == ups
    assert conv(cseq, ciseq) == delta
    assert conv(nu, ups) == delta
    radD = 1
    for p, j in factors(D):
        radD *= p
    for X in (1, 5, 20, 50, 75):
        tail = [0 if n <= X else nu[n] for n in range(N + 1)]
        head = [nu[n] if n <= X else 0 for n in range(N + 1)]
        rho = conv(ups, tail)
        complement = conv(ups, head)
        for n in range(1, N + 1):
            checked += 1
            assert rho[n] == delta[n] - complement[n]
            assert abs(rho[n]) <= nu[n] * tau[n]
            if n <= X:
                assert rho[n] == 0
            if rho[n] < 0:
                negative_rho_seen = True
            b = 1
            inert = 1
            ram = 1
            odd_inert = False
            for p, j in FAC[n]:
                cp = chi(D, p)
                if cp == -1:
                    inert *= p**j
                    odd_inert |= bool(j % 2)
                else:
                    b *= p**j
                if cp == 0:
                    ram *= p**j
            if odd_inert:
                assert rho[n] == 0
                continue
            t = isqrt(inert)
            assert t*t*b == n
            literal = 0
            for r in DIV[t]:
                u = t // r
                for d in DIV[b]:
                    e = b // d
                    if u*u*e > X:
                        literal += mu[r] * ups[d] * nu[e]
            assert literal == rho[n]
            assert abs(rho[n]) <= nu[b] * tau[b] * tau[t*t]
            if rho[n]:
                assert ram <= X * radD
                if ram > 1:
                    ramified_examples += 1

assert negative_rho_seen
assert ramified_examples > 0

for j in range(501):
    assert 2*j+1 <= comb(j+2, 2)
    assert comb(2*j+2, 2) <= comb(j+5, 5)
    assert (2*j+1)**2 * comb(2*j+2, 2) <= comb(j+53, 53)
    assert (j+1)**4 * comb(j+2, 2) <= comb(j+47, 47)

square_map_checks = []
for p in (3, 5, 7, 11, 13, 17, 19, 23, 29):
    images = {}
    for a in range(1, p-1):
        images.setdefault((2*a) % (p-1), []).append(a)
    assert images.get(0) == [(p-1)//2]
    assert max(map(len, images.values())) <= 2
    square_map_checks.append(p)

def f(k):
    return -F(49,200) + max(F(0), -F(112,125)+F(2,5)*k)/2 + max(F(0), F(1103,1000)-F(3,5)*k)/2
high_points = [F(21,20), F(1103,600), F(56,25), F(301,100)]
high_values = [f(k) for k in high_points]
assert max(high_values) == -F(17,2000)

def g(k):
    return F(1,400) - k/4 + max(F(0), -F(663,1000)+F(2,3)*k)
low_points = [F(99,100), F(1989,2000), F(21,20)]
low_values = [g(k) for k in low_points]
assert max(low_values) == -F(223,1000)
assert F(225,2)+F(324,4)+F(324,4)+77+72+36 == F(919,2)
assert F(324+972,2)+77+72 == 797
assert F(3,5)*(3+F(201,400)) == F(4203,2000)
assert F(267,200)+F(1,1000)+F(3,8000)+F(3,10000) < F(1337,1000)

out = {
    "scope": "Finite arithmetic and exact rational budgets only; not analytic or Lean verification",
    "integers_per_character_cutoff": N,
    "characters": [3,4,5,8,12,13],
    "cutoffs": [1,5,20,50,75],
    "coefficient_checks": checked,
    "negative_rho_seen": negative_rho_seen,
    "nonzero_ramified_examples": ramified_examples,
    "local_divisor_checks_through_exponent": 500,
    "square_map_primes": square_map_checks,
    "high_piecewise_points": [str(k) for k in high_points],
    "high_piecewise_values": [str(v) for v in high_values],
    "high_maximum": str(max(high_values)),
    "low_piecewise_points": [str(k) for k in low_points],
    "low_piecewise_values": [str(v) for v in low_values],
    "low_maximum": str(max(low_values)),
    "high_log_budget": "919/2 < 500",
    "low_log_budget": "797 < 1000",
    "result": "PASS"
}
print(json.dumps(out, indent=2))
