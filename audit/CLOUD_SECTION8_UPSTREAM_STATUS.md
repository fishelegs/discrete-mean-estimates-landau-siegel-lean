# Verified origin of the Section8 f/g tables

The original actual F/G kernels, exact beta shifts and cutoff normalizations reproduce all twelve printed f/g functions. No source-supported sign, missing shift, swapped conjugation or denominator correction was found that would change the limiting Section8 numerical value.

Lean proves:

- Exact finite-D F/G identities with epsilon=c-prime*alpha*logD retained
- For every fixed c-prime, epsilon tends to0 and actual kernels at P^z converge pointwise to the printed tables
- Exact finite cutoff geometry: logP2/logP=1/2-delta and log(P1/P2)/logP=1/250+delta, delta=10/L^(79/10) tends to0
- alpha*logT tends to0; the normalization is precisely1/pi
- The cross expansion forces c12=b12+conj(b21) with the printed iota orientation

The G calculation uses the genuine two-pole rational contour model already proved in Lemma84PaperResidue. No(A) or eventual-not-(A) assumption is used. [Full derivation and source locators](CLOUD_SECTION8_UPSTREAM_DERIVATION.md).

## Central checks

Three production modules,36 new public declarations including30 lemmas, plus one existing contour theorem checked: only standard three axioms. Four extra regressions;4061 dependency jobs and5215 whole-project jobs PASS. All1341 Lean sources pass placeholder/structure guards.961 SPEC/1226 full imports; strict audit unchanged392 candidates/nonzero exit.

[Verification](cloud_section8_upstream_verification.json), [axioms](cloud_section8_upstream_axioms.log), [hashes](cloud_section8_upstream_source_hashes.json). Reproduce `lake build ZhangLS.Spec.Section8UpstreamGeometry`, `lake env lean audit/CloudSection8UpstreamRegression.lean`, and `lake build`.

## Limits

The Lean limit statements are pointwise kernel limits. Uniform integral convergence, first-factor boundary replacement, arithmetic identity8.10 and full character-sum passage to8.11 are not proved here. The resulting kernel provenance strengthens the diagnosis of the printed numerical evaluation; it does not disprove the main theorem or exclude a redesigned construction. Full-ratio and admissible-parameter repair analysis is separate. Numbered completion remains36/51.
