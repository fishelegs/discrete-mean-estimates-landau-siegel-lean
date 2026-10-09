# Checkpoint 7 — actual fixed quadratic field arithmetic

Partial formalization; no fixed-field pi finiteness theorem is exported.

Four new proof modules construct the actual Gaussian fraction field and F(i),
prove the relative degree two and Galois involution, identify simultaneous
conjugate primitive roots, and instantiate the norm/Mahler and normalized
actual-minor arithmetic with actual primitive max heights. The remaining
hypotheses are the real field degree, actual coordinate degrees, nonzero
actual formal minor and explicit legal-packet budgets. No integrality, norm,
tower-degree, root-pair or Mahler-to-weight conclusion is assumed.

All public definitions, abbreviations and named instances are included in the
actual type/axiom audit, as well as theorems. Full ordinary Lean replay:
30 proof modules, aggregate, positive regressions, audit and 17 separately
matched expected failures = 50 compiler checks and 265 declaration reports.
Only propext, Classical.choice and Quot.sound are permitted. The added
regressions construct Q(sqrt(2))(i), prove relative degree two/Galois and compute
the simultaneous repeated-coordinate norm as -8. Expected failures reject
relative degree four and substituting the identity for nonidentity conjugation.

The existing source-entry/minor bridge is freshly checked against the exact
upstream pin; 872 prior source/log/olean receipts are rehashed and six actual
upstream type/axiom reports freshly compiled. This is not a full fresh build
of the upstream closure or a Comparator run.

CP6 focused CI succeeded (37892853066), as did the old-pi aggregate
(37892853070); their artifacts were checked against local reports and logs.
CP4 whole kernel CI succeeded (37887002564), including 1565 trusted Spec
modules, Spec aggregate, lake build and audit regressions. Pending later
whole-kernel runs are not counted as passed.

Remaining: instantiate actual packet counts and budgets, generalize weighted
complex-center compactification/blowup/jet surjectivity from rational
AdmissibleParameters, port the actual analytic estimate, and close the
exceptional-set contradiction. The generic arbitrary-complex-center curve
inequality already exists upstream; no unproved deep theorem is substituted.

Executable continuation beyond arithmetic: `checks/UpstreamGeometryBridge.lean`
proves the actual fixed-field center injectivity and weighted curve contact
inequality using the pinned upstream arbitrary-complex-center theorem. It
assumes the explicit positive/separated geometric weights and volume/ratio
conditions, not jet surjectivity. It additionally prints the exact types and
axioms of the still-rational-data blowup ampleness, jet-surjectivity and actual
analytic bound interfaces. Its independent audit compiles three new declarations
and prints three remaining dependency interfaces against the revalidated cache.
The bridge has not instantiated a generalized weighted compactification or
proved the global interpolation theorem.
