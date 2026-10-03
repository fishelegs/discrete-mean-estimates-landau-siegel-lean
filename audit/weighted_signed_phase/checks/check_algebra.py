"""Independent finite verification; does not import or run the evaluated checker.

Cubic Fourier identities are checked exactly in Z[X]/Phi_p, with denominators
cleared. Gauss/CRT/root identities are additional floating-point regressions.
No repository or source-artifact writes; output is confined to this directory.
"""
import cmath
import itertools
import json
import math
from pathlib import Path

import mpmath as mp
from sympy import kronecker_symbol

HERE = Path(__file__).resolve().parent

import argparse
_parser = argparse.ArgumentParser(description=__doc__)
_parser.add_argument('--output', type=Path, default=Path(__file__).resolve().parents[1] / 'results' / 'ALGEBRA_RERUN.json')
_OUTPUT = _parser.parse_args().output
_OUTPUT.parent.mkdir(parents=True, exist_ok=True)
counts = {}
worst = {}


def numerical(lhs, rhs, kind, tol=3e-9):
    error = float(abs(lhs - rhs))
    counts[kind] = counts.get(kind, 0) + 1
    worst[kind] = max(worst.get(kind, 0), error)
    assert error < tol, (kind, lhs, rhs, error)


def exact(lhs, rhs, kind, label):
    # A degree <= p-1 integer polynomial vanishes at zeta_p exactly when
    # all its coefficients coincide (it is a multiple of Phi_p).
    diff = [x-y for x, y in zip(lhs, rhs)]
    assert len(set(diff)) == 1, (kind, label, diff)
    counts[kind] = counts.get(kind, 0) + 1


def root(p):
    for g in range(2, p):
        if len({pow(g, j, p) for j in range(p-1)}) == p-1:
            return g
    raise AssertionError(p)


def character_table(p):
    g = root(p)
    table = []
    for j in range(p-1):
        values = [0j]*p
        for exponent in range(p-1):
            values[pow(g, exponent, p)] = cmath.exp(
                2j*math.pi*((j*exponent) % (p-1))/(p-1))
        table.append(values)
    return table


def additive(x, p):
    return cmath.exp(2j*math.pi*(x % p)/p)


def kl_vectors(p):
    # Count all triples first, by product and additive residue.
    data = {c: [0]*p for c in range(1, p)}
    for x, y, z in itertools.product(range(1, p), repeat=3):
        data[x*y*z % p][(x+y+z) % p] += 1
    return data


for p in [3, 5, 7, 11, 13]:
    kv = kl_vectors(p)
    # Work with K3=p*Kl3. Every mode and every nonzero c is tested.
    for c, h, k in itertools.product(range(1, p), range(p), range(p)):
        lhs = [0]*p
        for r, s in itertools.product(range(1, p), repeat=2):
            shift = (h*r+k*s) % p
            for n, value in enumerate(kv[c*r*s % p]):
                lhs[(n+shift) % p] += value
        rhs = [0]*p
        if h and k:
            rhs[c*pow(h*k, -1, p) % p] += p*p
            rhs[0] += p+1
        elif h or k:
            rhs[0] = 1
        else:
            rhs[0] = -(p-1)
        exact(lhs, rhs, 'cubic_fourier_exact', (p, c, h, k))

        for a in [0, 1]:
            # H_a=2*p*sqrt(p)*G_(3,a) has integer cyclotomic coefficients.
            brace_lhs = [0]*p
            for r, s in itertools.product(range(1, p), repeat=2):
                shift = (h*r+k*s) % p
                crs = c*r*s % p
                for n in range(p):
                    brace_lhs[(n+shift) % p] += (p-1)*(
                        kv[crs][n]+(-1)**a*kv[-crs % p][n])
                if a == 0:
                    brace_lhs[shift] += 2
            brace_rhs = [0]*p
            if h and k:
                v = c*pow(h*k, -1, p) % p
                brace_rhs[v] += p*p*(p-1)
                brace_rhs[-v % p] += (-1)**a*p*p*(p-1)
                if a == 0:
                    brace_rhs[0] += 2*p*p
            exact(brace_lhs, brace_rhs, 'primitive_brace_fourier_exact',
                  (p, a, c, h, k))

for p in [3, 5, 7, 11, 13, 17, 19, 29]:
    chars = character_table(p)
    gauss = [sum(ch[x]*additive(x, p) for x in range(p)) for ch in chars]
    eps = [gauss[j]/((1j)**(j % 2)*math.sqrt(p)) for j in range(p-1)]
    kv = kl_vectors(p)

    def kl(d, c):
        if d == 1:
            return additive(c, p)
        return sum(v*additive(n, p) for n, v in enumerate(kv[c % p]))/p

    def brace(d, a, c):
        return (p-1)/(2*math.sqrt(p))*(kl(d, c)+(-1)**a*kl(d, -c)) + (
            p**(-d/2) if a == 0 else 0)

    for d, a, t in itertools.product([1, 3], [0, 1], range(1, p)):
        lhs = sum(eps[j]**d*chars[j][t] for j in range(1, p-1) if j % 2 == a)
        rhs = (1j)**(-d*a)*brace(d, a, pow(t, -1, p))
        numerical(lhs, rhs, 'primitive_gauss_moments')

    discriminants = [-3, -4, 5, -7, 8, -8, 12, 13, -15, 17, -20, -24,
                     24, 28, -40, 40, 60]
    for delta in discriminants:
        D = abs(delta)
        if D % p == 0:
            continue
        chi = [int(kronecker_symbol(delta, n)) for n in range(D)]
        parity_chi = int(delta < 0)
        tau_chi = sum(chi[n]*additive(n, D) for n in range(D))
        eps_chi = tau_chi/((1j)**parity_chi*math.sqrt(D))
        for j in range(1, p-1):
            a = j % 2
            b = (a+parity_chi) % 2
            direct = sum(chi[n % D]*chars[j][n % p]*additive(n, D*p)
                         for n in range(D*p))/((1j)**b*math.sqrt(D*p))
            crt = (-1)**(a*parity_chi)*chi[p % D]*chars[j][D % p]*eps_chi*eps[j]
            numerical(direct, crt, 'crt_root_numbers')

        # Test both exact good-family formulas with arbitrary omitted primitive
        # characters, including u or v divisible by D (but still p-units).
        good = [j for j in range(1, p-1) if j % 3 != 1]
        bad = [j for j in range(1, p-1) if j % 3 == 1]
        for a in [0, 1]:
            C = (-1)**(a*parity_chi)*chi[p % D]*eps_chi
            for ell, u, v in [(2, D, 1), (1, 1, D), (D, D, D)]:
                if ell*u*v % p == 0:
                    continue
                tr = D*ell*u*pow(v, -1, p) % p
                tl = D*u*pow(ell*v, -1, p) % p
                for d, t in [(1, tr), (3, tl)]:
                    lhs = C*sum(eps[j]**d*chars[j][t]
                                for j in good if j % 2 == a)
                    rhs = C*((1j)**(-d*a)*brace(d, a, pow(t, -1, p)) -
                             sum(eps[j]**d*chars[j][t]
                                 for j in bad if j % 2 == a))
                    numerical(lhs, rhs, 'good_family_and_bad_correction')

# The branch is tested through log Gamma, with a continuously chosen analytic
# root and both global signs, at off-line and central s. This is an algebraic
# regression, not a check of the report's contour extension or estimates.
mp.mp.dps = 70
betas = [mp.j*mp.mpf('0.031'), mp.j*mp.mpf('0.064'), mp.j*mp.mpf('0.097')]
for a, sigma, phase, branch_sign in itertools.product(
        [0, 1], ['-0.5', '0.5', '1.5'], ['0.2', '1.3'], [-1, 1]):
    s = mp.mpc(sigma, '47.125')
    p = 101
    log_eps = mp.j*mp.mpf(phase)

    def log_h(z):
        return (mp.mpf('0.5')-z)*mp.log(p/mp.pi) + \
            mp.loggamma((1-z+a)/2)-mp.loggamma((z+a)/2)

    def Z(z):
        return mp.exp(log_eps+log_h(z))

    def Y(z):
        return branch_sign*mp.exp(-(log_eps+log_h(z))/2)

    B = Z(s)*mp.fprod(Y(s+b) for b in betas)/Y(s)
    B_common = mp.exp((3*log_h(s)-sum(log_h(s+b) for b in betas))/2)
    numerical(B, B_common, 'branch_common_factor', tol=1e-55)
    numerical(B**(-2), mp.fprod(mp.exp(log_h(s+b)) for b in betas)/
              mp.exp(log_h(s))**3, 'branch_square_identity', tol=1e-55)
    numerical(mp.fprod(Z(s+b) for b in betas)/Z(s), Z(s)**2/B**2,
              'functional_equation_multiplier', tol=1e-55)

result = {
    'status': 'PASS',
    'counts': counts,
    'max_absolute_errors': worst,
    'exact_check_ring': 'Z[X]/(1+X+...+X^(p-1)); denominators cleared',
    'scope': 'Finite algebra and branch-product regression only; no analytic '
             'bounds, repository edits, Lean compilation, or publication.'
}
_OUTPUT.write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2))
