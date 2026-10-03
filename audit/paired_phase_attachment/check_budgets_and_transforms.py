#!/usr/bin/env python3
"""Finite regressions for DERIVATION.md; prints results only."""
from fractions import Fraction as F
import cmath
import hashlib
import json
import math
from pathlib import Path


class QC:
    """Exact Gaussian rationals for the defect identity."""
    def __init__(self, re=0, im=0):
        self.re, self.im = F(re), F(im)
    @staticmethod
    def lift(z):
        return z if isinstance(z, QC) else QC(z)
    def __add__(self, z):
        z = QC.lift(z)
        return QC(self.re+z.re, self.im+z.im)
    __radd__ = __add__
    def __neg__(self):
        return QC(-self.re, -self.im)
    def __sub__(self, z):
        return self + -QC.lift(z)
    def __rsub__(self, z):
        return QC.lift(z) + -self
    def __mul__(self, z):
        z = QC.lift(z)
        return QC(self.re*z.re-self.im*z.im, self.re*z.im+self.im*z.re)
    __rmul__ = __mul__
    def __truediv__(self, z):
        z = QC.lift(z)
        n = z.re*z.re+z.im*z.im
        return self*QC(z.re/n, -z.im/n)
    def __eq__(self, z):
        z = QC.lift(z)
        return self.re == z.re and self.im == z.im


def e(q, a):
    return cmath.exp(2j*math.pi*(a % q)/q)


def character(D, n):
    n %= D
    tables = {
        3: {1: 1, 2: -1},
        4: {1: 1, 3: -1},
        5: {1: 1, 2: -1, 3: -1, 4: 1},
        8: {1: 1, 3: -1, 5: -1, 7: 1},
        12: {1: 1, 5: -1, 7: -1, 11: 1},
    }
    return tables[D].get(n, 0)


budgets = {
    "bad_family": F(36,2)+F(81,6)+F(81,6)-F(739,6)+F(77*5,6),
    "W1": F(9)+4*F(36,4),
    "W2": F(9)+2*F(36,4)+F(36,6)+2*F(81,6),
    "delta_error": F(-227)+F(45)+77,
    "AFE_error": F(-179)+F(60)+77,
    "sixth_holder_sum": F(1,4)+F(1,4)+3*F(1,6),
    "Cright_gap": F(9995,10000)+F(502,1000)+F(499,1000)-2,
    "Cleft_gap": F(1005,1000)-F(504,1000)-F(500,1000),
    "Tright_gap": F(1005,1000)+F(502,1000)-1-F(504,1000),
    "Tleft_gap": F(1005,1000)+F(500,1000)-F(504,1000)-1,
    "max_cube_length_exponent": 3*F(504,1000),
    "G_cube_divisor_order": F(2*3),
    "G_sixth_harmonic_power": F(6*6),
    "required_R6_exponent_example": F(-8)-8,
}
assert budgets["bad_family"] == -14
assert budgets["W1"] == 45 and budgets["W2"] == 60
assert budgets["delta_error"] == -105 and budgets["AFE_error"] == -42
assert budgets["sixth_holder_sum"] == 1
assert all(budgets[k] > 0 for k in ["Cright_gap", "Cleft_gap", "Tright_gap", "Tleft_gap"])
assert budgets["max_cube_length_exponent"] < 2

# Check the precise defect identity for arbitrary nonsingular Gaussian rationals.
for k in range(1, 101):
    f = QC(F(k+2,k+1), F(2*k+1,k+3))
    g = QC(F(k+4,k+2), F(-k,k+5))
    fd = QC(F(2*k+3,k+7), F(-3*k,k+4))
    gd = QC(F(k+1,k+8), F(4*k+1,k+3))
    z = QC(F(-k,k+9), F(k+7,k+1))
    err = QC(F(1,k+100), F(-1,k+101))
    delta = f*g-1
    deltad = fd*gd-1
    lp = f+z*fd+err
    actual_A = lp/f
    rem = (z*g*(delta-deltad)-err*g*gd)/(1+delta)
    assert z*g-gd == gd*(actual_A-2)+rem

# All-zero-separation geometry at symbolic-safe sample alpha values.
for alpha in [F(1,10), F(1,100), F(1,1000)]:
    assert F(1,2)-alpha/2 >= alpha/2
    assert F(2) >= alpha/2
    assert 4*alpha < 1

max_fourier_error = 0.0
max_crt_error = 0.0
fourier_cases = 0
crt_cases = 0
for p in [7, 11]:
    inv = {u: pow(u, -1, p) for u in range(1,p)}
    kl2 = {
        a: sum(e(p, u+a*inv[u]) for u in range(1,p))/math.sqrt(p)
        for a in range(1,p)
    }
    kl3 = {
        a: sum(e(p, x+y+a*inv[x]*inv[y])
               for x in range(1,p) for y in range(1,p))/p
        for a in range(1,p)
    }
    for a in range(1,p):
        plus = {u:e(p,a*inv[u]) for u in range(1,p)}
        minus = {u:kl3[a*u % p] for u in range(1,p)}
        for h in range(p):
            hp = sum(plus[u]*e(p,h*u) for u in range(1,p))
            hm = sum(minus[u]*e(p,h*u) for u in range(1,p))
            rp = -1 if h == 0 else math.sqrt(p)*kl2[a*h % p]
            rm = -1/p if h == 0 else math.sqrt(p)*kl2[-a*inv[h] % p]-1/p
            max_fourier_error = max(max_fourier_error,abs(hp-rp),abs(hm-rm))
            fourier_cases += 2
    for D in [3,4,5,8,12]:
        assert math.gcd(D,p) == 1
        tau = sum(character(D,u)*e(D,u) for u in range(D))
        for kind in ["inverse_additive", "Kl3"]:
            fvals = {0:0j}
            fvals.update({u:e(p,3*inv[u]) if kind == "inverse_additive"
                         else kl3[3*u % p] for u in range(1,p)})
            for h in range(D*p):
                lhs = sum(character(D,u)*fvals[u % p]*e(D*p,h*u)
                          for u in range(D*p))
                b = h*pow(D,-1,p) % p
                fh = sum(fvals[u]*e(p,b*u) for u in range(p))
                rhs = tau*character(D,p)*character(D,h)*fh
                max_crt_error = max(max_crt_error,abs(lhs-rhs))
                crt_cases += 1
assert max_fourier_error < 1e-10
assert max_crt_error < 1e-10

historical = json.loads((Path(__file__).resolve().parent / 'HISTORICAL_SOURCE_HASHES.json').read_text())
result = {
    "status": "PASS",
    "budgets": {k:str(v) for k,v in budgets.items()},
    "exact_gaussian_rational_defect_cases": 100,
    "fourier_cases": fourier_cases,
    "max_fourier_error": max_fourier_error,
    "CRT_completion_cases": crt_cases,
    "max_CRT_completion_error": max_crt_error,
    "conductors": [3,4,5,8,12],
    "primes": [7,11],
    "historical_input_sha256": historical,
    "historical_fingerprint_note": "Historical mathematical-source fingerprints are recorded, not recomputed by this portable finite check.",
    "limitations": "Finite checks only; no assumption (A), large-D mean, actual Gram lower bound, or Lean verification.",
}
print(json.dumps(result, indent=2, sort_keys=True))
