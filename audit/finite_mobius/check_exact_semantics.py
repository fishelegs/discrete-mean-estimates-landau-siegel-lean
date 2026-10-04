#!/usr/bin/env python3
"""Exact finite semantic regressions; these do not establish Lean certification.

All calculations use integers. One route uses divisor convolution; a separate route
sums literal short Mobius variables and counts ordered smooth factorizations using
prime exponents. Full defect identities are checked beyond the vanishing interval.
"""
from itertools import product
from math import comb, prod
import json


def mu_sieve(n):
    mu = [1] * (n + 1)
    mu[0] = 0
    prime = [True] * (n + 1)
    for p in range(2, n + 1):
        if prime[p]:
            for k in range(p, n + 1, p):
                prime[k] = False
                mu[k] *= -1
            for k in range(p * p, n + 1, p * p):
                mu[k] = 0
    return mu


def conv(a, b):
    n = len(a) - 1
    out = [0] * (n + 1)
    for d in range(1, n + 1):
        if a[d]:
            for q in range(1, n // d + 1):
                out[d * q] += a[d] * b[q]
    return out


def ordered_factorizations(n, k):
    if k == 0:
        return int(n == 1)
    answer, p = 1, 2
    while p * p <= n:
        e = 0
        while n % p == 0:
            e += 1
            n //= p
        answer *= comb(e + k - 1, k - 1)
        p += 1
    if n > 1:
        answer *= k
    return answer


def literal_short_variables(n, u, j, mu):
    answer = 0
    for short in product(range(1, u + 1), repeat=j):
        a = prod(short)
        if n % a == 0:
            answer += prod(mu[x] for x in short) * ordered_factorizations(n // a, j - 1)
    return answer


def main():
    checks = 0
    cases = 0
    literal_checks = 0
    endpoint_checks = 0
    one_checks = 0
    outside_nonzero = []
    for u in range(1, 9):
        for J in range(1, 5):
            nmax = max(128, (u + 1) ** J)
            mu = mu_sieve(nmax)
            zeta = [0] + [1] * nmax
            delta = [0, 1] + [0] * (nmax - 1)
            m = [mu[n] if n <= u else 0 for n in range(nmax + 1)]
            mz = conv(m, zeta)
            defect = [x - y for x, y in zip(delta, mz)]
            mpow, zpow, apow = delta[:], delta[:], delta[:]
            hb = [0] * (nmax + 1)
            terms = []
            for j in range(1, J + 1):
                mpow = conv(mpow, m)
                term = conv(mpow, zpow)
                terms.append(term)
                coefficient = (-1) ** (j - 1) * comb(J, j)
                hb = [x + coefficient * y for x, y in zip(hb, term)]
                zpow = conv(zpow, zeta)
                apow = conv(apow, defect)
            full_defect = conv(mu, apow)
            for n in range(nmax + 1):
                assert mu[n] - full_defect[n] == hb[n], (u, J, n, 'full-defect')
                checks += 1
            for n in range(u ** J + 1):
                assert apow[n] == full_defect[n] == 0, (u, J, n, 'support')
                assert mu[n] == hb[n], (u, J, n, 'inclusive')
                checks += 2
            assert mu[u ** J] == hb[u ** J]
            endpoint_checks += 1
            assert mu[1] == hb[1] == 1
            one_checks += 1
            if u <= 4:
                sample = set(range(1, min(32, nmax) + 1)) | {u ** J, nmax}
                for j, term in enumerate(terms, 1):
                    for n in sorted(sample):
                        assert term[n] == literal_short_variables(n, u, j, mu), (u, J, j, n)
                        literal_checks += 1
            if u == 1:
                assert full_defect[2 ** J] != 0
                outside_nonzero.append({'U': u, 'J': J, 'n': 2 ** J,
                    'mu_minus_HB': full_defect[2 ** J]})
            cases += 1
    assert [(-1) ** (j - 1) * comb(4, j) for j in range(1, 5)] == [4, -6, 4, -1]
    # Mutation witnesses: dropping n=1, a strict truncation at U=1, and reversed
    # coefficient signs would all destroy the indispensable unit coefficient.
    assert sum((-1) ** (j - 1) * comb(4, j) for j in range(1, 5)) == 1
    assert sum((-1) ** j * comb(4, j) for j in range(1, 5)) == -1
    result = {'kind': 'exact integer semantic regressions, not Lean certification',
        'cases': cases, 'full_and_support_checks': checks,
        'literal_variable_checks': literal_checks,
        'inclusive_endpoint_checks': endpoint_checks, 'n_one_checks': one_checks,
        'J4_coefficients': [4, -6, 4, -1],
        'nonzero_defect_outside_asserted_range': outside_nonzero}
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
