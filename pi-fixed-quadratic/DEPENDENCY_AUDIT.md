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
norm descent and integral closedness. The actual primitive integer minpoly, coefficient maximum height and real
root-pair identities are now proved. Checkpoint 7 constructs the actual fixed
quadratic field/compositum tower and instantiates every arithmetic obligation. All remaining hypotheses and construction gaps are listed in
README.md and visible in `checks/Audit.lean`.

The paper's `Lambda=4 log 2` must also be checked against the available **formal**
lcm bound. Upstream `Arithmetic.log_lcmUpto_le` uses the larger proved constant
`Real.log 4 + 4`. A later parameter port can retain this constant: the required
limits still have a fixed positive coefficient. Checkpoint 6 proves the enlarged arithmetic error and its dimension/height
limits with this actual formal constant; it does not claim the sharper numeric
lcm constant or a generalized analytic bound.

The root 4.30 project, six A7 vendor modules, sqrt(2)/Log-Pade sources and old
receipts remain byte-identical to the base commit. Old aggregate verification
is run separately against the existing 4.30 cache. No merge, PR, package, or
website action is part of this task.

Checkpoint 5 supplies the actual log clearing and a uniform coefficient
envelope, then connects them to the proved same-field norm. It uses the
coarser uniform log bound 2 (center constant `2k+2`), valid for all truncations.
The required later parameter limits are unchanged in kind because the
additional logarithmic constants are fixed before approximation weights.
The lcm constant remains the larger proved `log 4+4` until separately improved.
Checkpoint 6 now proves the changed dimension limits, height selection and
factorial remainder; generalized geometry, analytic transfer and the final pi
finiteness theorem remain unproved.

Checkpoint 7 constructs the Gaussian fraction field explicitly with common
rational denominators, and `F(i)` as `QuadraticAlgebra F (-1) 0`. Tower degrees
prove `[F(i):Q(i)]=2`; separability/normality and cardinality of the actual
Galois group give a nonidentity simultaneous conjugation. Its restriction
matches the other primitive-minpoly root because degree-two elements are not
fixed. The actual complex embedding fixes Gaussian integers. The normalized
minor theorem now takes only the actual degree-two field/coordinates, a
nonzero actual formal minor and explicit geometric budgets; there is no
arithmetic structure gap.

The generic upstream `CurveInequality.weighted_curve_inequality` already accepts
arbitrary complex centers and rational degree/jet weights. It requires
coordinatewise injectivity, positive weights, inflated volume/fibre-volume,
separated-weight products and coordinate ratios. Its proof is kernel-verified
upstream; the remaining adaptation is the weighted compactification/blowup
and jet-surjectivity chain currently parameterized by `AdmissibleParameters`
with rational approximations, followed by the actual analytic aggregate.
No missing deep theorem is asserted merely from this interface mismatch.

The executable contact bridge is `checks/UpstreamGeometryBridge.lean`.
Its complete printed remaining-interface types and allowed-axiom reports are
in `audit/UpstreamGeometryBridge.log`:

- `AdmissibleJetSurjectivity.blowupBundle_ample`: for
  `d : AdmissibleParameters ν Λ D`, ampleness of the actual blowupBundle of
  `centerIdeal d` and `hyperplane d`.
- `AdmissibleJetSurjectivity.eventually_jetRestriction_surjective`: for that
  same rational-data `d`, eventually every actual jetRestriction is surjective.
- `LiteralAnalytic.actual_minor_analytic_bound`: for `d : FixedData ν`,
  `0<=ν`, `H>0`, an actual selected minor and its nonvanishing, the actual
  normalized log determinant is bounded by the explicit analytic error,
  remainder and maximum of collision/displacement savings.

These exact interfaces are verified, but their data cannot yet be replaced
by the height-linked fixed-field centers. No assumed-surjectivity pi theorem
is exported as a workaround. The actual contact theorem is a proved geometric
step; the compactification/blowup port, actual packet budgets/counts, analytic
transfer and final comparison are the remaining implementation work.
