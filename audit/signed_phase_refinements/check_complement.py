#!/usr/bin/env python3
"""Independent exact arithmetic/provenance checks; never imports candidate code or Lean."""
from fractions import Fraction as F
from pathlib import Path
from math import comb
import hashlib
import json
import subprocess

OUT = Path(__file__).resolve().parent
REPO = Path(__file__).resolve().parents[2]

checks = {}

def check(name, condition):
    assert condition, name
    checks[name] = True

# Reconstruct all twelve reported arithmetic checks independently.
kappa = F(1, 1000)
check('original_square_tail_constant', 2*(2+19)*(2+28) == 1260)
check('extended_square_tail_constant', 2*(4+19)*(4+28) == 1472)
check('sparse_error_energy', F(72)-F(2011,2)+F(9*16,2) == -F(1723,2))
check('per_box_exponent', F(77)+F(324,2)-F(1723,4) == -F(767,4))
check('refined_box_count_exponent', 5*9 == 45)
check('boundary_100_error', -F(767,4)+45+100 == -F(187,4))
check('right_infinity_absolute_P_exponent', F(1)+F(3,2)*F(201,400)-F(251,1000) == F(6011,4000))
check('core_first_margin', 2 <= 2**20 and 2-2*kappa < 2-F(13,8)*kappa)
check('core_F_triple_margin', 64**3 <= 2**20 and 2-2*kappa+3*kappa/8 == 2-F(13,8)*kappa)
check('quintuple_support_ratio', F(1,2)**4/2 == F(1,32) and 2**4/F(1,2) == 32)
check('constant_resonance_label_ratio', F(1,4)/32 == F(1,128) and 4/F(1,32) == 128 and 2*128*64**3 == 256*64**3)
check('generalized_n_bound', F('3.0008') < F('3.002') < 4)

check('linear_tail_exponent', -2022+9 == -2013)
check('square_tail_exponent', -2013+2 == -2011)
check('global_long_budget', -F(767,4)+45 == -F(587,4))
check('boundary_main_only_crude', 77+162+18+45+100 == 402)
check('core_error_absorption', -F(623,4) < -F(187,4) < 0)
check('uniform_stirling_margin', 2*9 < 519)
check('gaussian_horizontal_margin', 2*9 < 2*400 and 9 < 2*(405-400))

def g2(yc, yd, p2):
    return max(F(1), yc/p2)*max(F(1), yd/p2)

shell_checks = 0
for yc in [F(1,64), F(1), F(3), F(64), F(8192)]:
    for yd in [F(1,32), F(1), F(10), F(2048)]:
        for p2 in [F(1), F(25), F(1024)]:
            for theta in [F(1), F(2), F(16), F(1024)]:
                assert g2(theta*yc, yd, p2) <= theta*g2(yc, yd, p2)
                shell_checks += 1
            for h in [F(1,2), F(1,16), F(1,1024)]:
                A = 21
                assert h**(2*A-1)*g2(yc/h, yd, p2) <= h**(2*A-2)*g2(yc,yd,p2)
                shell_checks += 1
check('shell_length_and_subunit_scale_tests', shell_checks == 420)
check('shell_decay_exponent', F(1,2)-21+F(1,2) == -20)

divisor_checks = 0
for e in range(401):
    t2, t6, t8, t16, t36 = e+1, comb(e+5,5), comb(e+7,7), comb(e+15,15), comb(e+35,35)
    assert t2**3 <= t8
    assert t2**4 <= t16
    assert t6**2 <= t36
    divisor_checks += 3
check('prime_power_divisor_envelopes', divisor_checks == 1203)

def factors(n):
    result = []
    p = 2
    while p*p <= n:
        k = 0
        while n % p == 0:
            n //= p
            k += 1
        if k:
            result.append((p,k))
        p += 1
    if n > 1:
        result.append((n,1))
    return result

def mu(n):
    fs = factors(n)
    return 0 if any(k>1 for _,k in fs) else (-1)**len(fs)

def chi(n):
    return [0,1,-1,-1,1][n % 5]

def alpha(n):
    return [1,1j,-1,-1j][sum(k for _,k in factors(n)) % 4]

def divisors(n):
    return [d for d in range(1,n+1) if n % d == 0]

limit = 300
nu = {n: sum(chi(d) for d in divisors(n)) for n in range(1,limit+1)}
eta = {n: sum(mu(d)*alpha(n//d) for d in divisors(n)) for n in range(1,limit+1)}
infty = {n: sum(chi(d)*alpha(n//d) for d in divisors(n)) for n in range(1,limit+1)}
convolution_checks = 0
for n in range(1, limit+1):
    assert sum(eta[n//e]*nu[e] for e in divisors(n)) == infty[n]
    assert infty[n].conjugate() == sum(chi(d)*alpha(n//d).conjugate() for d in divisors(n))
    for X in [1,2,4,10,30,100]:
        cx = sum(eta[n//e]*nu[e] for e in divisors(n) if e <= X)
        tail = sum(eta[n//e]*nu[e] for e in divisors(n) if e > X)
        assert cx-infty[n] == -tail
        convolution_checks += 1
check('convolution_error_sign_and_opposite_shift', convolution_checks == 1800)

# Exact exponent arithmetic for epsilon(theta)*tau(conj theta)/sqrt(q)=i^parity.
phase_checks = 0
for a in [0,1]:
    for b in [0,1]:
        for sr in [0,1]:
            for ss in [0,1]:
                for sm in [0,1]:
                    gauss_exp = 2*((2*a-a) % 4)+(2*b-b) % 4
                    expected = 2*a+b
                    assert (gauss_exp-expected) % 4 == 0
                    assert (expected+2*(a*sr+a*ss+b*sm)) % 4 == (2*a+b+2*a*sr+2*a*ss+2*b*sm) % 4
                    phase_checks += 1
check('both_parities_all_frequency_signs', phase_checks == 32)


print(json.dumps({'all_passed':all(checks.values()),'check_groups':len(checks),'checks':checks,'counts':{'reconstructed_candidate_checks':12,'shell_inequalities':shell_checks,'prime_power_divisor_inequalities':divisor_checks,'truncated_convolution_sign_checks':convolution_checks,'parity_and_frequency_sign_cases':phase_checks},'scope':'Exact finite arithmetic only; not an analytic or Lean proof.'},indent=2))
