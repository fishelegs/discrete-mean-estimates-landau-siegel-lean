# Sources and verification boundary

Primary published sources read from the downloaded author TeX:

1. Čech–Matomäki, [arXiv:2303.05277v2](https://arxiv.org/abs/2303.05277v2), `Annalen_preprint_2.tex`: literal M and same-side B at lines 141–171; CRT, primitive-even subtraction and hyper-Kloosterman bound at lines 248–304
2. Bui–Pratt–Zaharescu, [arXiv:2012.04392v2](https://arxiv.org/abs/2012.04392v2), `source.tex`: conductor/parity scope and literal local coefficients at lines 148–190; orthogonality at 201–207; product AFE at 215–253; actual same-side B and second-moment theorem range at 323–358

Previously verified actual arithmetic used as an input:

* Repository `ZhangLS/Spec/Lemma31.lean`, especially `lemma31_actual_square_paper_tail_le` and `lemma31_proved`: the uniform 1260 L⁻²⁰¹¹ square-tail bound under the original (A)
* Repository `ZhangLS/Spec/ShortUpsilonArithmetic.lean`: literal inverse convolution and |υ|≤ν, including ramified primes
* Repository `ZhangLS/Spec/ShortUpsilonEnergy.lean`: the already verified weighted divisor-Cauchy pattern; the present higher even moments are new source-level applications and are not claimed to be existing Lean declarations
* `audit/CLOUD_SHORT_UPSILON_STATUS.md`: published finite-energy scope and explicit separation from the missing signed weighted-zero gain

These inputs and their hashes are recorded in `finite_checks.json`. These recorded source fingerprints describe the reviewed mathematical inputs.

Additional external deep input: the hyper-Kloosterman estimate used in CM Lemma 4, cited there as Smith, Theorem 6. This source-level theorem is not formalized in the present repository. The new bridge is not a theorem obtained solely from the existing Lean library.

The new mathematical content is Sections 3–8 of `PROOF.md`, including the exact ramified deletion, fixed 20/22-to-21 moment interpolation, the global surrogate identity rM·conj(S)=U·conj(MS), the complete coefficient budget and the Fejér estimate. Section 10 supplies the uniform deterministic-height extension. Finite regressions test these identities and budgets on small examples; they do not prove the asymptotic theorem.
