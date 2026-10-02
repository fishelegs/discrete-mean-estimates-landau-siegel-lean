# Kernel-verified numerical incompatibility in literal Section 8

**Lean proves `7 < Section8.c1.re` from the actual interval-integral definitions in (8.13)–(8.23), with iota2 from (2.26).** Thus those definitions are incompatible with the printed numerical bound (8.24), c1<6.9955. There is no character hypothesis, assumption(A), external numerical enclosure, or postulated integral value in the theorem.

The exact proved lower bound is

`4790274002065539332881844226677501 / 679562729429049362531250000000000`

which is greater than7.04905. The theorem also proves that c1 has zero imaginary part. This lower bound is intentionally conservative; the separate reproducible numerical audit estimates c1≈7.05010466979205.

## Source fidelity and proof route

All twelve f/g functions use literal exact-rational coefficients and actual complex exponentials. The four b values are mathlib interval integrals with Lebesgue volume, not formal symbols. The diagonal endpoints are .504 and .5. Both off-diagonal integrals retain all three +.004 shifts, the same .5 endpoint, and .504*.5*pi denominator. The orientation is c12=b12+conj(b21), and c1 retains both conjugate cross terms and the genuine norm-square of iota2.

The proof expands the four integrands into polynomial-exponential functions; proves their actual antiderivatives, continuity and integrability; reduces endpoint phases to pi/4 multiples plus3*pi/500; and obtains a real closed form. Rational bounds for pi, sqrt2, sin and cos are proved inside Lean from mathlib, then ordinary ordered-field arithmetic proves the lower bound. No floating-point computation enters the proof.

See the [source correspondence](CLOUD_SECTION8_KERNEL_SOURCE_MAP.md), [independent semantic review](CLOUD_SECTION8_KERNEL_REVIEW.md), and [actual definitions](../ZhangLS/Spec/Section8NumericalObjects.lean).

## Central validation

- Eight production modules,88 named declarations: only propext, Classical.choice, Quot.sound
- 24 expanded source-definition regressions and2 end-to-end regressions
- Focused dependency build3327 jobs PASS; complete project5189 jobs PASS
- 1312 Lean source files; placeholder and structure guards PASS
-935 SPEC and1200 full aggregate imports; strict audit unchanged at389 review candidates/nonzero exit
- Production proof text unchanged from frozen delivery except import paths; no new axiom, sorry, unsafe or native_decide

[Verification record](cloud_section8_kernel_verification.json), [axioms](cloud_section8_kernel_axioms.log), [source fingerprints](cloud_section8_kernel_source_hashes.json). Reproduce using `lake build ZhangLS.Spec.Section8NumericalLower`, `lake env lean audit/CloudSection8NumericalRegression.lean`, and `lake build`.

## Exact conclusion and limits

This is an unconditional incompatibility among the displayed concrete Section8 definitions and their numerical estimate. It is **not** a counterexample to the Landau–Siegel main theorem, not a character satisfying(A), and not a proof that no repair is possible. The actual-character-mean-to-model asymptotic bridge remains separate unfinished mathematics. Source transcription is independently human-reviewed; Lean does not parse the PDF typography. The current argument through Proposition2.5 cannot use the printed numerical value without a justified correction.

This unnumbered verification does not increase the51-node local lemma ledger: **34 original +2 repaired =36/51**. Final theorem verification remains incomplete.
