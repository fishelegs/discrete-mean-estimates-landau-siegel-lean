#!/usr/bin/env python3
"""Finite checks only. No Lean, asymptotic proof, or actual-zero experiment."""
from fractions import Fraction as Q
from math import gcd
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent

def factors(n):
    out = []
    p = 2
    while p * p <= n:
        if n % p == 0:
            a = 0
            while n % p == 0:
                n //= p
                a += 1
            out.append((p, a))
        p += 1
    if n > 1:
        out.append((n, 1))
    return out

def divs(n):
    out = [1]
    for p, a in factors(n):
        out = [d * p**j for d in out for j in range(a + 1)]
    return out

def mu(n):
    f = factors(n)
    return 0 if any(a > 1 for p, a in f) else (-1)**len(f)

tables = {
    3: {1: 1, 2: -1},
    4: {1: 1, 3: -1},
    5: {1: 1, 2: -1, 3: -1, 4: 1},
    8: {1: 1, 3: -1, 5: -1, 7: 1},
    12: {1: 1, 5: -1, 7: -1, 11: 1},
}

coefficient_cases = 0
deletion_cases = 0
for D, table in tables.items():
    chi = lambda n: table.get(n % D, 0)
    for Y in (2, 3, 4):
        X = Y**5
        N = X * Y
        ds = [None] + [divs(n) for n in range(1, N + 1)]
        nu = [0] + [sum(chi(d) for d in ds[n]) for n in range(1, N + 1)]
        ups = [0] + [sum(mu(d) * mu(n//d) * chi(n//d) for d in ds[n])
                     for n in range(1, N + 1)]
        assert all(0 <= nu[n] and abs(ups[n]) <= nu[n] for n in range(1, N+1))
        for n in range(1, N + 1):
            assert sum(ups[d] * nu[n//d] for d in ds[n]) == (1 if n == 1 else 0)
            c = sum(ups[a]*nu[n//a] for a in ds[n] if a <= X and n//a <= Y) - (n == 1)
            fg = sum(nu[a]*nu[n//a] for a in ds[n] if Y < a <= X and n//a <= X)
            assert abs(c) <= 2*fg
            if n <= Y:
                assert c == 0
            elif n <= X:
                assert c == -sum(ups[a]*nu[n//a] for a in ds[n] if n//a > Y)
            else:
                assert all(a > Y for a in ds[n] if a <= X and n//a <= Y)
            coefficient_cases += 1
        for m in range(1, N//D + 1):
            if mu(D) == 0:
                assert ups[D*m] == 0
            else:
                assert ups[D*m] == (mu(D)*ups[m] if gcd(D, m) == 1 else 0)
            deletion_cases += 1

# Exact rational complex arithmetic.
def z(a, b=0): return (Q(a), Q(b))
def add(x, y): return (x[0]+y[0], x[1]+y[1])
def neg(x): return (-x[0], -x[1])
def sub(x, y): return add(x, neg(y))
def mul(x, y): return (x[0]*y[0]-x[1]*y[1], x[0]*y[1]+x[1]*y[0])
def conj(x): return (x[0], -x[1])
def div(x, y):
    q = y[0]**2+y[1]**2
    assert q
    t = mul(x, conj(y))
    return (t[0]/q, t[1]/q)

one = z(1)
zero = z(0)
values = [z(a, b) for a in (-2, 0, 1) for b in (-1, 0, 2)]
units = [z(1), z(-1), z(0, 1), z(0, -1), z(Q(3,5), Q(4,5))]
phase_cases = 0
for M in values:
    for F in values:
        for Phi in units:
            e = neg(add(F, mul(Phi, conj(F))))
            assert e == mul(Phi, conj(e))
            Ssrc = add(F, div(e, z(2)))
            assert add(Ssrc, mul(Phi, conj(Ssrc))) == zero
            U = div(mul(Phi, M), conj(M)) if M != zero else one
            WF = mul(M, F)
            R = sub(WF, one)
            assert mul(Phi, mul(M, conj(F))) == mul(U, conj(WF))
            assert add(one, U) == neg(add(add(R, mul(U, conj(R))), mul(e, M)))
            B = sub(mul(M, Ssrc), one)
            assert add(one, U) == neg(add(B, mul(U, conj(B))))
            for SX in (z(0), z(1), z(1,2)):
                WX = mul(M, SX)
                ZX = mul(Phi, mul(M, conj(SX)))
                assert ZX == mul(U, conj(WX))
            phase_cases += 1

e4 = -Q(2011,4) + 4*2**2+4*2
e12 = -Q(2011,4) + 4*6**2+4*6
assert e4 == -Q(1915,4)
assert e12 == -Q(1339,4)
assert Q(1,4)+Q(1,4)+Q(1,6)+Q(1,6)+Q(1,12)+Q(1,12) == 1
base_loss = 9+18+77
trial_loss = base_loss+27
budgets = {
    "base_loss": base_loss,
    "trial_loss": trial_loss,
    "base_inverse_error": str(base_loss+2*e4),
    "trial_inverse_error": str(trial_loss+2*e12),
    "base_AFE_error": base_loss+8-358,
    "trial_AFE_error": trial_loss+24-358,
    "H_cubed_P_exponent": str(Q(504,1000)*3),
    "invalid_H_fourth_P_exponent": str(Q(504,1000)*4),
}
assert budgets["trial_AFE_error"] == -203

N = 22
assert all(k % N != 0 for k in range(1, 22))
toy_samples = 0
for j in range(N):
    for m in range(-20, 21):
        tau = Q(2*m+1, 2)-Q(j,N)  # tau=(log P)t/pi
        assert (tau+Q(j,N)) % 1 == Q(1,2)
        next_tau = Q(2*(m+1)+1, 2)-Q(j,N)
        assert next_tau-tau == 1
        toy_samples += 1

result = {
    "status": "PASS_FINITE_ONLY",
    "coefficient_cases": coefficient_cases,
    "ramified_deletion_cases": deletion_cases,
    "exact_complex_phase_cases": phase_cases,
    "toy_exact_sampling_cases": toy_samples,
    "budgets": budgets,
    "scope": "Finite algebra and exponent arithmetic only; no analytic proof, Lean certificate, Z2, or final contradiction.",
}
(ROOT / "finite_checks.json").write_text(json.dumps(result, ensure_ascii=False, indent=2)+"\n")
print(json.dumps(result, ensure_ascii=False, indent=2))
