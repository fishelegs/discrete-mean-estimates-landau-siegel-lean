# Verified Lemma 10.2 analytic components and actual mixed-sum ξ replacement

Original Lemma102Target remains unproved and is not counted as a numbered completion. Its definition is unchanged from the pre-proof freeze. The package preserves the actual ξ coefficients, original tent, β/c′, Π, all three main terms, and every source endpoint. No counterexample to the original conditional pointwise statement is claimed.

## Pointwise analytic components

The first 20 modules prove the genuine complex-frequency-zero logarithmic Perron identity; the actual L quotient/ξ-series bridge; third-order Cauchy residue; real contour deformation and boundary integrals; and the closed x=T transfer. No use of Nat μ=0 substitutes for zero frequency. The exact tent is the second difference of three actual unshifted logarithmic ξ sums, and its finite definition equals the literal all-n source sum.

The three original interior main terms are proved with error

  2000 (2+C_T ‖Π(d,r)‖) L^-15.

The original uniform additive L^-15 is not recovered by hiding Π in a constant. A separate actual Perron bound controls every original boundary band by

  (2000/L^9)[C_ξ(1+9 log L)^Kξ(log T)^4
             +16e(1+6π+9π²/2)L²‖Π‖
             +(2+C_T‖Π‖)L^-6].

This is explicitly weaker than the source pointwise O(L^-7). Exact details and the original freeze are in FINAL-STATUS.md and FROZEN-TARGET.sha256; that earlier pointwise-only report is intentionally retained as the record for its separately frozen package.

## Genuine actual Section 10 weighted result

Eight additional modules preserve the actual μ/χ/λ/φ arithmetic weights and the actual κ₁+ι₂κ₂ companion. The literal-source identity is lemma102_mixed_source_exact. The replacement main term is the source's three-piece main term, with specified knot choices covered by the boundary estimates.

- lemma102_mixed_interior_quantitative:
  actual interior error ≤ C_I WeightScale(L^9)(1+9 log L)^KΠ L^-12.
- lemma102_transition_weight_mass:
  the three original knot layers have actual weight mass ≤24 WeightScale(L^9) log T. The inclusive upper endpoints are retained by proving a closed-layer bound through [Q/T,QT), with thickness T²; no endpoint is discarded.
- lemma102_mixed_boundary_quantitative:
  actual boundary replacement error ≤ C_B(1+9 log L)^K_B(log T)^5 L^-15.
- lemma102_source_full_xi_replacement_little_o:
  for every fixed positive c′ and every ε>0, one modulus threshold works uniformly for χ satisfying original (A) and all three j, and

  ‖literal Section10 κ/ξ/tent mixed sum − actual three-piece ξ-main replacement‖ ≤ εα.

The boundary scale is proved to be o(α) using (log T)^10=L^11 and fixed-polylog absorption; no desired weighted estimate is assumed. All ξ, Π, companion, arithmetic weights and three boundary bands remain actual. No finite-model ratio calculation substitutes for this theorem.

## Scope and unresolved work

The weighted result closes the effect of replacing the tent-ξ factor in the S_j(a11,a13) Section 10 display. The first inner factor remains its actual κ source sum. Subsequent first-factor replacement, arithmetic summation, phase-polynomial/integral evaluation, other shifted-tent mixed terms, and final Proposition 2.4/MixedMoment mean asymptotics are not claimed. This does not complete Proposition 7.1 or rely on its completion.

The original pointwise Lemma 10.2 target remains open at both the uniform L^-15 interior exponent and O(L^-7) boundary assertion. Numbered completion count change: zero.

## Central verification

28 production modules,89 standard-only public declaration axiom checks,9 standalone semantic regressions and5365 whole-project jobs PASS. All1511 Lean sources pass guards;1111 SPEC/1376 full imports. Every promoted source is byte-identical to the frozen package; all366 prerequisite source hashes match. The strict audit remains nonzero with414 candidates; its one new direct-hypothesis flag returns a locally derived scalar inequality, not the requested weighted result.

[Verification](cloud_lemma102_full_verification.json), [axioms](cloud_lemma102_full_axioms.log), [source hashes](cloud_lemma102_full_source_hashes.json), [source and endpoint review](CLOUD_LEMMA102_SOURCE_AND_BOUNDARIES.md). Reproduce `lake build ZhangLS.Spec.Lemma102MixedLittleO ZhangLS.Spec.Lemma102Boundary`, `lake env lean -j1 audit/CloudLemma102FullRegression.lean`, and `lake build`.

Numbered completion remains34 original +2 repaired=36/51. This component proves a sufficient weighted xi-replacement estimate without declaring the original stronger pointwise target proved. The final numerical/main-chain obstruction is unchanged.
