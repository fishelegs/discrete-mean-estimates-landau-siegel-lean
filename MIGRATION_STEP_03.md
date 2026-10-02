# Migration Step 03 — paper-level specification correction

## What changed

1. `RealPrimitiveCharacter` now carries the direct semantic condition
   `∀ a, (χ a).im = 0`.  Code is no longer allowed to infer “real-valued” merely from a
   structure name.
2. Added `conj_eval` and `evalNat_im`, the first bridge facts needed to show L-values on
   the real axis are real.
3. Replaced the trusted small-value hypothesis with `AssumptionAWithConstant χ c₁`.
   The old normalized threshold with coefficient `1` is retained only under the explicit
   name `NormalizedAssumptionA` and must eventually be justified by a reduction lemma.
4. Added `Spec/PaperTheorems.lean`, freezing the actual quantitative shapes of Theorems 1
   and 2 as specification targets.
5. The mathematical target records existence of positive absolute constants.  The phrase
   “effectively computable” is not faked as a bare proposition: the project still needs a
   deliberate representation for effective real constants before that metadata can be
   kernel-checked.

## Blocking next lemma

The next analytic bridge is:

* prove that `dirichletLFunction χ (x : ℂ)` is real for real `x` when `D > 1`;
* in particular prove `(LAtOne χ).im = 0`;
* then prove the same reality statement for `LDerivAtOne` using conjugation and
  differentiability.

A proof by direct series manipulation only works for `x > 1`; extending it to `x = 1`
needs analyticity/continuity or a conjugation identity for the analytic continuation.
That bridge must be proved rather than assumed.
