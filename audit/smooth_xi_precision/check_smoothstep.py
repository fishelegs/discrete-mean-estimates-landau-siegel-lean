from fractions import Fraction as F
from math import comb, factorial
from pathlib import Path
import json

m = 32
C = F(factorial(65), factorial(32) ** 2)
p = [F(0) for _ in range(66)]
q = [F(0) for _ in range(66)]
for r in range(33):
    k = 33 + r
    p[k] = C * (-1) ** r * F(comb(m, r), k)
    q[k] = C * F(comb(m, r), k)

shifted = [sum(p[k] * comb(k, j) for k in range(j, 66)) for j in range(66)]
reflected = [(-1) ** j * shifted[j] for j in range(66)]
unit = [F(1)] + [F(0)] * 65

# p(1+y)-q(y)=1: checks the two truncated-power tails join to the constant 1.
join = all(shifted[j] - q[j] == unit[j] for j in range(66))
# p(x)+p(1-x)=1: checks the reflected smoothstep partition.
reflection = all(p[j] + reflected[j] == unit[j] for j in range(66))

a, b = F(501, 1000), F(503, 1000)
delta = b - a
principal = {}
for n in range(1, 67):
    coeff = F(0)
    for r in range(33):
        k = 33 + r
        h = k + 1 - n
        if h >= 0:
            coeff += C * comb(32, r) * factorial(k - 1) / delta**k * (
                (-1)**r * b**h - a**h
            ) / factorial(h)
    principal[n] = coeff

checks = {
    "normalization_integral": sum(p) == 1,
    "left_join_constant_identity": join,
    "reflection_partition_identity": reflection,
    "simple_pole_residue_one": principal[1] == 1,
    "higher_poles_cancel_exactly": all(principal[n] == 0 for n in range(2, 67)),
    "C_integer": C.denominator == 1,
}
result = {
    "arithmetic": "exact rational, no floating-point tolerances",
    "m": m,
    "normalization_C": str(C),
    "checks": checks,
    "all_pass": all(checks.values()),
}
Path(__file__).with_name("smoothstep-checks.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
