#!/usr/bin/env python3
"""Independent finite regressions for the one-completion Gauss operator.

Python standard library only. This does not import or execute the candidate's
checker, and never writes to the candidate or repository. Numerical tests are
regressions, not proofs of the universal identities or analytic estimates.
"""

from __future__ import annotations

import cmath
import json
import math
import random
from collections import defaultdict


TOL = 5e-9
PRIMES = (3, 5, 7, 11, 13, 17, 19)
CONDUCTORS = (3, 4, 5, 8, 12)
COUNTS = defaultdict(int)
ERRORS = defaultdict(float)
RNG = random.Random(202610032203)


def check(group, actual, expected, scale=1.0):
    error = abs(actual - expected) / max(1.0, abs(scale))
    COUNTS[group] += 1
    ERRORS[group] = max(ERRORS[group], error)
    if not math.isfinite(error) or error > TOL:
        raise AssertionError((group, actual, expected, error))


def demand(group, condition):
    COUNTS[group] += 1
    if not condition:
        raise AssertionError(group)


def additive(q, x):
    return cmath.exp(2j * math.pi * (x % q) / q)


def divisors(q):
    return [d for d in range(1, q + 1) if q % d == 0]


def gauss(values):
    q = len(values)
    return sum(value * additive(q, x) for x, value in enumerate(values))


def verify_character(values, group):
    q = len(values)
    check(group + ".identity", values[1], 1)
    for n, value in enumerate(values):
        check(group + ".unit_support", abs(value), int(math.gcd(n, q) == 1))
    for x in range(q):
        for y in range(q):
            check(group + ".multiplicativity", values[(x * y) % q], values[x] * values[y])


def verify_primitive(values, group):
    """A character factors through d|q iff it is constant on unit fibers mod d."""
    q = len(values)
    for d in divisors(q)[:-1]:
        first = {}
        witness = False
        for x in range(q):
            if math.gcd(x, q) != 1:
                continue
            residue = x % d
            if residue in first and abs(values[x] - first[residue]) > TOL:
                witness = True
                break
            first[residue] = values[x]
        demand(group + ".proper_divisor_witness", witness)


def real_primitive_chi(D):
    residues = {
        3: {1: 1, 2: -1},
        4: {1: 1, 3: -1},
        5: {1: 1, 2: -1, 3: -1, 4: 1},
        8: {1: 1, 3: -1, 5: -1, 7: 1},
        12: {1: 1, 5: -1, 7: -1, 11: 1},
    }
    return [complex(residues[D].get(n, 0)) for n in range(D)]


def prime_characters(p):
    generator = next(g for g in range(2, p) if len({pow(g, k, p) for k in range(p - 1)}) == p - 1)
    logs = {pow(generator, k, p): k for k in range(p - 1)}
    result = []
    for k in range(p - 1):
        values = [0j] + [cmath.exp(2j * math.pi * k * logs[n] / (p - 1)) for n in range(1, p)]
        result.append({"k": k, "parity": k % 2, "values": values, "tau": gauss(values)})
    return result


def inner(x, y):
    """The prescribed inner product is linear in its FIRST argument."""
    return sum(a * b.conjugate() for a, b in zip(x, y))


def norm2(x):
    return sum(abs(a) ** 2 for a in x)


def mv(A, x):
    return [sum(a * b for a, b in zip(row, x)) for row in A]


def adjoint(A):
    return [[A[j][i].conjugate() for j in range(len(A))] for i in range(len(A))]


def mm(A, B):
    n = len(A)
    return [[sum(A[i][k] * B[k][j] for k in range(n)) for j in range(n)] for i in range(n)]


def matrix_check(group, A, B):
    for row_a, row_b in zip(A, B):
        for a, b in zip(row_a, row_b):
            check(group, a, b)


def arbitrary_coefficients(length):
    return [0j] + [complex(RNG.randint(-3, 3), RNG.randint(-3, 3)) if RNG.randrange(4) else 0j for _ in range(length)]


def fold(coefficients, p):
    result = [0j] * (p - 1)
    for n in range(1, len(coefficients)):
        if n % p:
            result[n % p - 1] += coefficients[n] / math.sqrt(n)
    return result


def polynomial(coefficients, values):
    p = len(values)
    return sum(coefficients[n] * values[n % p] / math.sqrt(n) for n in range(1, len(coefficients)))


def run():
    families = {p: prime_characters(p) for p in PRIMES}
    for p, family in families.items():
        for char in family:
            verify_character(char["values"], "prime_character")
            if char["k"]:
                verify_primitive(char["values"], "prime_primitive")
            check("prime_parity", char["values"][-1], (-1) ** char["parity"])
        check("principal_gauss_sign", family[0]["tau"], -1)

    composite_rows = []
    for D in CONDUCTORS:
        chi = real_primitive_chi(D)
        verify_character(chi, "chi_character")
        verify_primitive(chi, "chi_primitive")
        chi_tau = gauss(chi)
        for p, family in families.items():
            if math.gcd(D, p) != 1:
                continue
            q = D * p
            for char in family[1:]:
                values, a, tau = char["values"], char["parity"], char["tau"]
                theta = [chi[n % D] * values[n % p] for n in range(q)]
                theta_bar = [z.conjugate() for z in theta]
                # Multiplicativity is inherited from separately verified factors.
                verify_primitive(theta, "composite_primitive")
                demand("composite_character_support", all((abs(theta[n]) > 0.5) == (math.gcd(n, q) == 1) for n in range(q)))
                b = 0 if theta[-1].real > 0 else 1
                t_theta, t_bar = gauss(theta), gauss(theta_bar)
                eps = tau / ((1j) ** a * math.sqrt(p))
                eps_theta = t_theta / ((1j) ** b * math.sqrt(q))
                check("composite_gauss_norm", abs(t_theta) / math.sqrt(q), 1)
                check("composite_gauss_product", t_theta * t_bar / q, (-1) ** b)
                check("composite_CRT_factor", t_theta / math.sqrt(q), chi[p % D] * values[D % p] * chi_tau * tau / math.sqrt(q))
                check("composite_completion_root", t_bar / math.sqrt(q), (1j) ** b / eps_theta)
                check("residual_one_completion_root", eps ** 2 * eps_theta * t_bar / math.sqrt(q), (1j) ** b * eps ** 2)
                check("residual_squared_gauss", eps ** 2, (-1) ** a * tau ** 2 / p)
                check("retained_negative_frequency", theta_bar[-1], (-1) ** b)
                quadratic = char["k"] == (p - 1) // 2
                if quadratic:
                    check("quadratic_gauss_square", tau ** 2 / p, (-1) ** a)
                    check("quadratic_epsilon_square", eps ** 2, 1)
                composite_rows.append({"D": D, "p": p, "psi_exponent": char["k"], "psi_parity": a, "product_parity": b, "quadratic": quadratic})

    all_fibers = []
    mask_rows = []
    principal_sign_mutations = 0
    ratio_product_mutations = 0
    for p, family in families.items():
        kl = {z: sum(additive(p, x + z * pow(x, -1, p)) for x in range(1, p)) for z in range(1, p)}
        for a in (0, 1):
            eligible = [char for char in family[1:] if char["parity"] == a]
            # Rows indexed by output residue n; columns by input residue c.
            complete_kernel = [[0j for _ in range(p - 1)] for _ in range(p - 1)]
            for c in range(p):
                for n in range(p):
                    lhs = sum(char["tau"] ** 2 / p * char["values"][c] * char["values"][n].conjugate() for char in eligible)
                    if not c or not n:
                        check("kernel_nonunit_zero", lhs, 0)
                        continue
                    ratio = n * pow(c, -1, p) % p
                    main = (p - 1) / (2 * p) * (kl[ratio] + (-1) ** a * kl[-ratio % p])
                    correction = (-1 / p) if a == 0 else 0
                    rhs = main + correction
                    check("double_gauss_ratio_kernel", lhs, rhs)
                    complete_kernel[n - 1][c - 1] = rhs
                    if a == 0:
                        demand("detect_wrong_principal_sign", abs(lhs - (main + 1 / p)) > 1 / p)
                        principal_sign_mutations += 1
                    product = n * c % p
                    wrong = (p - 1) / (2 * p) * (kl[product] + (-1) ** a * kl[-product % p]) + correction
                    if abs(lhs - wrong) > 1e-5:
                        ratio_product_mutations += 1

            indices = tuple(char["k"] for char in eligible)
            masks = {(), indices, indices[::2], indices[1::2]}
            for k in indices:
                masks.add((k,))
            for _ in range(4):
                masks.add(tuple(k for k in indices if RNG.randrange(2)))
            for mask in sorted(masks):
                chosen = [char for char in eligible if char["k"] in mask]
                other = [char for char in eligible if char["k"] not in mask]
                dimension = p - 1
                basis = {char["k"]: [z.conjugate() / math.sqrt(dimension) for z in char["values"][1:]] for char in chosen}
                U = [[sum(char["tau"] ** 2 / p * basis[char["k"]][y] * basis[char["k"]][x].conjugate() for char in chosen) for x in range(dimension)] for y in range(dimension)]
                projection = [[sum(basis[char["k"]][y] * basis[char["k"]][x].conjugate() for char in chosen) for x in range(dimension)] for y in range(dimension)]
                Ustar = adjoint(U)
                matrix_check("partial_isometry_UstarU", mm(Ustar, U), projection)
                matrix_check("partial_isometry_UUstar", mm(U, Ustar), projection)
                matrix_check("projection_idempotence", mm(projection, projection), projection)
                matrix_check("projection_selfadjoint", adjoint(projection), projection)
                if not chosen:
                    matrix_check("empty_mask_zero_operator", U, [[0j] * dimension for _ in range(dimension)])

                c_raw, d_raw = arbitrary_coefficients(3 * p + 2), arbitrary_coefficients(5 * p + 3)
                c_vec, d_vec = fold(c_raw, p), fold(d_raw, p)
                C = {char["k"]: polynomial(c_raw, char["values"]) for char in eligible}
                D = {char["k"]: polynomial(d_raw, char["values"]) for char in eligible}
                def pair(chars):
                    return sum(char["tau"] ** 2 / p * C[char["k"]] * D[char["k"]].conjugate() for char in chars)
                direct_pair = pair(chosen)
                uc, pc = mv(U, c_vec), mv(projection, c_vec)
                scale = dimension * math.sqrt(norm2(c_vec) * norm2(d_vec))
                check("folded_bilinear_orientation", dimension * inner(uc, d_vec), direct_pair, scale)
                complete_pair = inner(mv(complete_kernel, c_vec), d_vec)
                check("good_bad_subtraction", complete_pair - pair(other), direct_pair, scale)
                check("norm_projection_identity", norm2(uc), norm2(pc), max(norm2(c_vec), 1))
                demand("operator_bound", abs(inner(uc, d_vec)) <= math.sqrt(norm2(c_vec) * norm2(d_vec)) + TOL)
                check("fiber_polarization", 2 * inner(uc, d_vec).real, norm2(pc) + norm2(d_vec) - norm2([x - y for x, y in zip(uc, d_vec)]), norm2(c_vec) + norm2(d_vec))
                energy_d = sum(abs(d_raw[n]) ** 2 / n for n in range(1, len(d_raw)))
                demand("folding_energy_bound", norm2(d_vec) <= (1 + (len(d_raw) - 1) / p) * energy_d + TOL)

                for char in chosen:
                    v = basis[char["k"]]
                    omega = char["tau"] ** 2 / p
                    uv = mv(U, v)
                    target = [omega * x for x in v]
                    for actual, expected in zip(uv, target):
                        check("retained_character_eigenvector", actual, expected)
                    check("saturation_positive", inner(uv, target), 1)
                    check("saturation_negative", inner(uv, [-x for x in target]), -1)

                zeta = cmath.exp(1j * RNG.uniform(-math.pi, math.pi))
                density_phase = cmath.exp(1j * RNG.uniform(-math.pi, math.pi))
                positive_mass = RNG.uniform(0.01, 1.0)
                all_fibers.append((p, positive_mass, zeta * density_phase, direct_pair, uc, pc, d_vec))
                mask_rows.append({"p": p, "parity": a, "good_exponents": list(mask), "bad_exponents": [char["k"] for char in other]})

    demand("product_kernel_mutation_detected", ratio_product_mutations > 0)
    demand("arbitrary_nonconjugation_closed_mask", any(any((row["p"] - 1 - k) not in row["good_exponents"] for k in row["good_exponents"]) for row in mask_rows))
    for a in (0, 1):
        demand("quadratic_parity_coverage", any(row["quadratic"] and row["psi_parity"] == a for row in composite_rows))
    a_norm, prime_mass = 0.71, sum(PRIMES)
    original_integral = 0j
    hilbert_pair = 0j
    squared_projection = squared_y = squared_defect = 0.0
    for p, mass, phase, original_pair, uc, pc, d_vec in all_fibers:
        original_integral += mass * phase * original_pair / (a_norm * prime_mass)
        weight = mass * (p - 1) / (a_norm * prime_mass)
        u_phase = [phase * x for x in uc]
        hilbert_pair += weight * inner(u_phase, d_vec)
        squared_projection += weight * norm2(pc)
        squared_y += weight * norm2(d_vec)
        squared_defect += weight * norm2([x - y for x, y in zip(u_phase, d_vec)])
    check("direct_integral_exact_normalization", hilbert_pair, original_integral, squared_projection + squared_y)
    check("direct_integral_polarization", 2 * hilbert_pair.real, squared_projection + squared_y - squared_defect, squared_projection + squared_y)

    return {
        "status": "PASS",
        "scope": "Independent finite floating-point algebra regressions only; universal proofs require the accompanying independent mathematical review. No asymptotic or exceptional-character claim.",
        "implementation": "Python standard library; independent of candidate checker; prescribed linear-first inner product; zeros retained at nonunits.",
        "normalized_absolute_tolerance": TOL,
        "prime_moduli": list(PRIMES),
        "real_primitive_conductors": list(CONDUCTORS),
        "assertion_count": sum(COUNTS.values()),
        "counts": dict(sorted(COUNTS.items())),
        "maximum_normalized_errors": dict(sorted(ERRORS.items())),
        "composite_root_cases": len(composite_rows),
        "composite_quadratic_cases": sum(row["quadratic"] for row in composite_rows),
        "operator_mask_cases": len(mask_rows),
        "direct_integral_fibers": len(all_fibers),
        "wrong_principal_sign_cases_detected": principal_sign_mutations,
        "product_in_place_of_ratio_cases_detected": ratio_product_mutations,
        "composite_case_inventory": composite_rows,
        "mask_inventory": mask_rows,
    }


def main():
    print(json.dumps(run(), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
