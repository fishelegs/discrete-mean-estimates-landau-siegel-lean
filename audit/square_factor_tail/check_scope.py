#!/usr/bin/env python3
"""Exact finite scope regressions; the universal arguments remain in the proofs."""
from collections import Counter
from fractions import Fraction as F
from math import comb
from pathlib import Path
import json

counts = Counter()


def check(category, condition):
    if not condition:
        raise ValueError(category)
    counts[category] += 1


def tau(order, valuation):
    return int(valuation == 0) if order == 0 else comb(valuation + order - 1, order - 1)


for q in range(1, 65):
    sharp = max(0, q * (q - 3) // 2)
    larger = max(0, q * q - 2 * q)
    check('integer_sharp_order', q * (q - 3) % 2 == 0)
    check('sharp_order_sufficient_at_two', 2 * q + sharp >= q * (q + 1) // 2)
    check('larger_order_dominates', larger >= sharp)
    if sharp:
        check('sharp_order_necessary_at_two', 2 * q + sharp - 1 < tau(q, 2))
    for h in range(81):
        for label, order in [('sharp', sharp), ('larger', larger)]:
            check(label + '_inert_comparison', tau(q, 2 * h) <= tau(2 * q + order, h))

for q in range(1, 10):
    check('strict_convolution_cutoff', F(21, 20) * (2 * q) < 19)
check('q_ten_cutoff_fails', F(21, 20) * 20 > 20)
check('strict_threshold_margin', F(19, 18) - F(21, 20) == F(1, 180))
check('small_square_exact_exponent', 19 + 2 * F(1, 2) == 20)
check('large_square_rankin_exponent', F(1, 2) * (F(3, 2) - 2) == -F(1, 4))
check('linear_error_exact_exponent', F(1, 2) - F(21, 40) == -F(1, 40))

rows = []
for j in range(1, 5):
    q = 2 * j + 1
    tail = 4 * q - 2015
    energy = tail + 9 * q * (q - 1)
    labels = 81 + 18 * j
    bound = labels + 77 + F(324 + energy, 2)
    check('all_e_budget', bound == 18 * j * j + 31 * j - F(1371, 2))
    check('strong_pair_negative_log', bound < 0)
    rows.append(dict(j=j, q=q, sharp_K=max(0, q*(q-3)//2),
                     larger_K=max(0, q*q-2*q), tail=tail, energy=energy,
                     labels=labels, paired_log=str(bound)))

examples = [
    (2, F(1, 2), [F(1, 2)]*2, [F(1, 2)], [F(1, 3)]*3, F(5, 6), F(7, 3)),
    (3, F(1, 2), [F(1, 2)]*3, [F(1, 5)]*2, [F(1, 5)]*3, F(2, 5), F(13, 5)),
    (4, F(3, 10), [F(9, 20)]*4, [F(3, 20)]*3, [F(3, 20)]*3, F(3, 10), F(27, 10)),
]
weak_rows = []
for j, e, mu, smooth_b, original, expected_pair, expected_long in examples:
    smooth = sorted(smooth_b + original, reverse=True)
    pair = sum(smooth[:2])
    long_exponent = e + sum(mu) + sum(smooth_b) + original[0]
    check('weak_geometry_factor_count', len(mu) == j and len(smooth_b) == j - 1)
    check('weak_geometry_total', e + sum(mu) + sum(smooth_b) + sum(original) == 3)
    check('weak_geometry_mu_cutoff', all(x < F(1501, 2000) for x in mu))
    check('weak_geometry_pair', pair == expected_pair < F(1003, 1000))
    check('weak_geometry_original_Long', long_exponent == expected_long > 2)
    check('weak_geometry_positive_e', e > 0)
    weak_rows.append(dict(j=j, pair=str(pair), original_Long=str(long_exponent)))

receipt = dict(status='PASS_FINITE_SCOPE_CHECKS_SOURCE_ONLY', assertions=sum(counts.values()),
               counts=dict(counts), HB_rows=rows, weak_pair_examples=weak_rows,
               scope='Exact finite regressions only. No compiler, asymptotic certification or signed gain.')
(Path(__file__).resolve().parent / 'SCOPE_CHECKS.json').write_text(json.dumps(receipt, indent=2)+'\n')
print(json.dumps(receipt, indent=2))
