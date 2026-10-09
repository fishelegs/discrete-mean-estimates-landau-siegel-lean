# CP11: end-to-end fixed real quadratic field pi finiteness

## Final exact statement

`FixedQuadratic.ParameterPort.fixed_real_quadratic_pi_finite_explicit`:

```lean
(F : IntermediateField ℚ ℝ) [FiniteDimensional ℚ F]
(hF : Module.finrank ℚ F = 2) (nu : ℝ) (hnu : 2 < nu) :
Set.Finite {b : F | (minpoly ℚ (b : ℝ)).natDegree = 2 ∧
  |Real.pi-(b : ℝ)| ≤ (primitiveMinpolyHeight (b : ℝ) : ℝ)^(-nu)}
```

`primitiveMinpolyHeight` is the maximum absolute coefficient of the actual
positive-leading primitive integer minimal polynomial. The final theorem has
no interpolation, norm-integrality, analytic-bound, exceptional-set or
parameter-margin hypothesis. Its exact elaborated type and transitive axioms
are printed in `finiteness-logs/checks.FinitenessAudit.log`.

## Construction and order

Fix F and nu > 2. Source rational geometric constants and eta give a positive
exponent gap. Fix epsilon and F0, then a finite dimension using the changed
coefficient/conjugate error budget and collision growth. Fix a small rational
sigma and a common height threshold. Assuming an infinite exceptional set,
actual primitive heights supply a successive sequence meeting that threshold
and the separated multiplicative growth. Construct every coordinate in the
same F, with actual ceil(log H) weights. Prove the exact inflated volumes,
Fin-indexed separated products, ceiling tail budget, total error gap and
collision margin. Invoke the proved geometric cofinal minor existence and the
same-minor arithmetic/complete analytic estimates. The real-degree remainder
thresholds are fixed together first, and cofinality supplies H beyond all of
them. This contradicts infinitude and proves the displayed finiteness result.

## Ordinary Lean validation

Eight fresh compiler checks: three parameter modules; public aggregate
`FixedQuadraticFixedFieldPi`; actual Q(sqrt(2)) positive specialization;
six-declaration type/axiom audit; two separately checked expected failures.
All pass. All six axiom sets are exactly the standard allowed subset
propext/Classical.choice/Quot.sound. No sorry, admit, project axiom,
native_decide, unsafe or proof hook. The negative fixtures reject removing
nu > 2 and passing relative field degree four where degree two is required.

`finiteness-audit.json` records every compiler exit and source/log/olean hash.
The prerequisites revalidate the passed core 50/265, CP8 actual-packet bridge,
CP9 geometry 22/155 and CP10 complete analytic 11/61 receipts; these reused
checks are not claimed freshly rebuilt in CP11. The upstream source remains
pin adc7f1241b42e322a6451854ab7e4b4c146bf78a. Its 872 prior receipt hashes are
revalidated and six exact upstream APIs/axioms freshly printed. Full upstream
869-module ordinary replay was already performed in its isolated environment;
CP11 reuses that checked closure rather than claiming a new full replay.

## CI and preservation

CP10 focused arithmetic CI 37902549627 and original pi CI 37902549663 both
passed. Downloaded source/log/axiom receipts match local replay (paths
normalized). CP5 whole-repository CI 37889982449 also passed: 1565 individually
compiled trusted Spec modules, Spec aggregate, lake build, audit regressions
and Gaussian closure. Its full artifacts are checked in the committed
validation file. Later root CI remain pending at this checkpoint; do not claim
them passed. The new OAI-dependent ports and final theorem are a separate local
ordinary Lean verification, not included in focused Linux arithmetic CI.

All 274 protected hashes still match the old 4.30 pins and verified A7, W2,
sqrt(2), weighted-colon and Log-Pade work. Original checkout is clean at
cae0ad9b2069acf3c8814b31af36a1842519ce9e. No old branch reset, merge, PR,
package publishing or website edit occurred.

## Scope

This proves the fixed real quadratic field upper statement at primitive max
coefficient height. It makes no claim about varying quadratic fields, a
Roy sequence, a degree-exactly-two lower exponent, pi BA/non-BA, Weil-height
normalization, novelty or the K1--K3 research obstacles. It completes the
fixed-field auxiliary formalization only. Latest aggregate CI terminal states
remain an operational verification follow-up.
