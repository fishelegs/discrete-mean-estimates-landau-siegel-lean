# Step 103 — Actual complex-character foundations for Lemma 5.6

The complete original Lemma 5.6 remains **in progress**. Its faithful
`Lemma56Target` retains actual character values and complex powers, the
strict prime window, `r<T`, character distinction, (A), closed height
endpoints, and the primitive modulus-one character. Constants and the
modulus threshold are quantified before all moduli, characters and heights.

## Proved interfaces

Nine trusted modules now supply 60 public proved interfaces:

- [Mangoldt positivity](../ZhangLS/Spec/Lemma56MangoldtPositivity.lean):
  actual all-order logarithmic derivative series and nonpositive
  Fejér-weighted real sums for χ, ζ, θ and χθ.
- [Twist classification](../ZhangLS/Spec/Lemma56TwistClassification.lean):
  principal χθ forces equality of the actual primitive characters and
  their conductors. Distinct primitive θ gives an entire actual χθ
  L-function without coprimality or product-primitivity assumptions.
- [Principal boundary](../ZhangLS/Spec/Lemma56PrincipalBoundary.lean):
  modulus-one primitivity, character distinction, and the exact t=0
  finite prime mass identity.
- [Character Abel summation](../ZhangLS/Spec/Lemma56CharacterAbel.lean),
  [integral bound](../ZhangLS/Spec/Lemma56AbelIntegralBound.lean), and
  [analytic continuation](../ZhangLS/Spec/Lemma56AbelContinuation.lean):
  actual nonprincipal complex characters have complete-period
  cancellation, partial-sum bound r, and
  `|L(s,θ)|≤r|s|/Re s` throughout Re s>0. This uses an actual Mellin
  integral and the identity theorem, without primitivity or real values.
- [Center bound](../ZhangLS/Spec/Lemma56NearTwoBound.lean):
  `|L(s,θ)-1|≤3/4` and `|L(s,θ)|≥1/4` for Re s≥2.
- [Faithful target and prime window](../ZhangLS/Spec/Lemma56.lean):
  exact prime membership, mass, T=exp(L^1.1), decay exp(-L^4.5), and
  the principal boundary for the actual paper window.
- [Jensen bounds](../ZhangLS/Spec/Lemma56JensenBounds.lean):
  the closed radius-3/2 disk has bound `2r(7/2+|t|)`. Its closed
  radius-5/4 divisor count is at most `6log(8r(7/2+|t|))`.
  When r≤D T and |t|≤2D, the count is at most 24L^1.1.
  This applies to both θ and the possibly imprimitive product χθ;
  both height endpoints and overlapping moduli are retained.

## Validation

All nine module builds pass. The
[expanded regression](Step103Lemma56FoundationsRegression.lean) has
17 examples, including faithful target equivalence, strict prime-window
membership, actual Abel continuation, critical-line and closed-disk
boundaries, overlapping moduli, both height endpoints, and the principal
paper-window identity. Target equivalence checks its definition; it does
not prove the target. All 60
[axiom reports](step103_regression_axioms.txt) contain only `propext`,
`Classical.choice` and `Quot.sound`.

All 375 Lean sources pass placeholder and structure checks. The Spec
aggregate imports 242 modules; the full project imports 320. There are
52 audit regressions. Their source fingerprints are frozen in
[step103_source_fingerprints.json](step103_source_fingerprints.json).

Repository-wide kernel verification **PASS**: all 242 trusted Spec
modules, the Spec aggregate, the complete 320-import project, and all
52 audit regressions passed. All 375 source fingerprints stayed unchanged.
Verification interval: 2026-10-01 13:25:59–13:46:27 Asia/Shanghai.
See [step103_kernel_verification.txt](step103_kernel_verification.txt),
[authoritative report](lean_kernel_verification.txt), and
[full gate log](step103_full_verification.log).

The strict static scan reports 103 review candidates, including four new
local-variable returns. All four have been reviewed:

- Jensen `h` is the proved elementary log(6/5)≥1/6 inequality.
- Center-bound `h` is the proved actual n=2 L-series term bound.
- Twist-classification `h` is the product-character equality after
  multiplying by χ and using χ²=1; its conclusion is character
  classification, not the paper's prime-sum estimate.
- Twist-classification `hc` is actual conductor equality obtained from
  the proved equality of character lifts and conductor preservation.

The static heuristic status is separate from the kernel gate; see
[step103_spec_audit.txt](step103_spec_audit.txt).

## Remaining original obligations

General-character zero repulsion and the actual finite prime-window
exponential estimate remain open. The literal modulus-one case also
remains in the target. At t=0 its sum equals the prime mass, so positive
mass would require `1≤C exp(-L^4.5)`. This does not disprove the
conditional theorem under (A); it requires its own consequence of (A)
or a justified paper convention before the full target can be promoted.
The nonprincipal analytic auxiliaries do not silently restrict the target.

Ledger: **17/51 complete, 1 in progress, 33 unstarted**. The full
51-result goal stays active.

Paper: [arXiv:2211.02515v1, Lemma 5.6 and the T parameter](https://arxiv.org/html/2211.02515v1).

## Verified independent next-step draft

During the frozen gate, a separate [actual zero-factor draft](step104_lemma56_zero_factors_draft.txt)
passes with **57 standard-axiom interfaces and four expanded examples**;
see its [kernel output](step104_lemma56_zero_factors_draft.log) and
[exact source metadata](step104_lemma56_zero_factors_draft_metadata.json).
It supplies arbitrary nonprincipal complex-character actual finite zero
sets and natural multiplicities, entire factorization at removed zeros,
normalized analytic logarithms, all-order actual inverse-power formulas,
J-independent weighted error ≤36000log(8r(7/2+|t|)), actual local Fejér
detection and near-one normalization geometry.

The actual mixed χ/ζ-at-zero and θ/χθ-at-t remaining power sum is bounded
above by 187200log D plus 36000 times each of the two actual character
logarithmic size budgets, plus the exceptional-pole difference
2(1−β)J(J+1)exp(4J/U). The normalization parameter U is independent of
the character-size budget; a regression checks U=(log D)^4, preserving
the scale needed for the eventual weak zero-repulsion argument.

This draft is not a project module, is not included in the current full
gate, and does not prove the complete original prime-window estimate.
Common-maximum detection across the four mixed families and a uniform
strict budget are the next zero-repulsion obligations.
