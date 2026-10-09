# Formal dependency audit — 2026-10-09

Base checkout: KEYISHEN-MC6, original clean
`codex/pi-weighted-colon-20261008`, HEAD
`cae0ad9b2069acf3c8814b31af36a1842519ce9e`.
Development uses a separate checkout and `codex/pi-fixed-quadratic-20261009`.
No tracked repository `AGENTS.md` or `.agents/skills/SKILL.md` was present.

The existing isolated upstream workspace was found at
`../2026-10-08/task/openai-math-w2-verification`. Its recorded ordinary verification
uses Lean 4.34.1 and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
It successfully checked 869 original proof modules and three audit/type fixtures.
The current task revalidates all 872 source, log and output hashes and freshly
prints six upstream axiom reports; it does not count that as 872 new builds.

The source is openai/math at
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. API facts are checked from the actual
Lean source and compiled declarations, not inferred from the paper:

| Interface | Actual scope | Consequence for this port |
|---|---|---|
| `InterpolationMatrix.truncatedLog_full_row_minor` | arbitrary complex `r`, but assumes surjectivity of `linearEvaluation` | reusable extraction after surjectivity is proved |
| `MatrixArithmetic.selectedMinor_arithmetic_lower_bound` | integer numerators `p`, natural denominators `q`, weights `ceil(log q)` | cannot apply to algebraic centers |
| `DeterminantContradiction.FixedData` | abbreviation for `AdmissibleParameters`; fields `p`, `q`, `x_log`, rational approximations | must be generalized or replaced |
| `AdmissibleMatrixInterpolation.globalInterpolation` | `GlobalInterpolationStatement` quantifies over rational `FixedData` | its full proof has not been generalized to quadratic data |
| `LiteralAnalytic.actual_minor_analytic_bound` / `analyticAggregate` | actual matrix and packet from rational `FixedData` | paper analytic transfer requires a genuine formal port |
| `OAI.PiExponent.main` | the original literal rational irrationality-exponent statement | does not imply the fixed-field quadratic theorem |

The changed norm step is not discharged by upstream nonzero Gaussian-integer
modulus >=1: first the exact cleared simultaneous norm must actually be shown
Gaussian integral. The new `Resultant.lean` proves this for one split quadratic
and one-variable `P`, while `Conjugation.lean` handles simultaneous nonvanishing.
The third checkpoint now proves multivariate Gaussian integrality in an
abstract degree-two Galois tower over the fraction field of Gaussian integers.
It combines the primitive finite-place argument with an actual two-embedding
norm descent and integral closedness. The actual fixed real quadratic field
and its minpoly/height tower have not yet been constructed to instantiate it. All remaining hypotheses and construction gaps are listed in
README.md and visible in `checks/Audit.lean`.

The paper's `Lambda=4 log 2` must also be checked against the available **formal**
lcm bound. Upstream `Arithmetic.log_lcmUpto_le` uses the larger proved constant
`Real.log 4 + 4`. A later parameter port can retain this constant: the required
limits still have a fixed positive coefficient. This checkpoint claims neither
the paper's sharper numeric lcm constant nor the full enlarged error closure.

The root 4.30 project, six A7 vendor modules, sqrt(2)/Log-Pade sources and old
receipts remain byte-identical to the base commit. Old aggregate verification
is run separately against the existing 4.30 cache. No merge, PR, package, or
website action is part of this task.
