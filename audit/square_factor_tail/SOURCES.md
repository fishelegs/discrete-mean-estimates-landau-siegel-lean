# Public mathematical source inputs

All eleven inputs are pinned at repository commit `cbcfbcbc7ceafaafcf3e711b7216d2f059da192d`. The verifier checks byte count and SHA256, so a later checkout is usable only if the listed bytes agree.

The new arithmetic proof is self-contained in PROOF.md and REVIEW.md. The repository files record the existing analytic/divisor statements and the inherited smooth-completion framework; reading these files does not establish a new compiler or axiom-closure result.

- [audit/multilinear_completion/PROOF.md](https://github.com/fishelegs/discrete-mean-estimates-landau-siegel-lean/blob/cbcfbcbc7ceafaafcf3e711b7216d2f059da192d/audit/multilinear_completion/PROOF.md)
- [audit/multilinear_completion/REVIEW.md](https://github.com/fishelegs/discrete-mean-estimates-landau-siegel-lean/blob/cbcfbcbc7ceafaafcf3e711b7216d2f059da192d/audit/multilinear_completion/REVIEW.md)
- [ZhangLS/Spec/Lemma31HyperbolaInputs.lean](https://github.com/fishelegs/discrete-mean-estimates-landau-siegel-lean/blob/cbcfbcbc7ceafaafcf3e711b7216d2f059da192d/ZhangLS/Spec/Lemma31HyperbolaInputs.lean)
- [ZhangLS/Spec/Lemma31HyperbolaError.lean](https://github.com/fishelegs/discrete-mean-estimates-landau-siegel-lean/blob/cbcfbcbc7ceafaafcf3e711b7216d2f059da192d/ZhangLS/Spec/Lemma31HyperbolaError.lean)
- [ZhangLS/Spec/Lemma31CumulativeBound.lean](https://github.com/fishelegs/discrete-mean-estimates-landau-siegel-lean/blob/cbcfbcbc7ceafaafcf3e711b7216d2f059da192d/ZhangLS/Spec/Lemma31CumulativeBound.lean)
- [ZhangLS/Spec/Lemma31NuIntegralBound.lean](https://github.com/fishelegs/discrete-mean-estimates-landau-siegel-lean/blob/cbcfbcbc7ceafaafcf3e711b7216d2f059da192d/ZhangLS/Spec/Lemma31NuIntegralBound.lean)
- [ZhangLS/Spec/Lemma31LinearTail.lean](https://github.com/fishelegs/discrete-mean-estimates-landau-siegel-lean/blob/cbcfbcbc7ceafaafcf3e711b7216d2f059da192d/ZhangLS/Spec/Lemma31LinearTail.lean)
- [ZhangLS/Spec/Lemma31TotalWeight.lean](https://github.com/fishelegs/discrete-mean-estimates-landau-siegel-lean/blob/cbcfbcbc7ceafaafcf3e711b7216d2f059da192d/ZhangLS/Spec/Lemma31TotalWeight.lean)
- [ZhangLS/Spec/Proposition71DivisorWeights.lean](https://github.com/fishelegs/discrete-mean-estimates-landau-siegel-lean/blob/cbcfbcbc7ceafaafcf3e711b7216d2f059da192d/ZhangLS/Spec/Proposition71DivisorWeights.lean)
- [ZhangLS/Spec/DivisorSmallPowerBudget.lean](https://github.com/fishelegs/discrete-mean-estimates-landau-siegel-lean/blob/cbcfbcbc7ceafaafcf3e711b7216d2f059da192d/ZhangLS/Spec/DivisorSmallPowerBudget.lean)
- [ZhangLS/Spec/Lemma34TauProduct.lean](https://github.com/fishelegs/discrete-mean-estimates-landau-siegel-lean/blob/cbcfbcbc7ceafaafcf3e711b7216d2f059da192d/ZhangLS/Spec/Lemma34TauProduct.lean)

The asymmetric-hyperbola proof uses only complete-period cancellation; Pólya–Vinogradov is an optional independent route. Completion budgets retain the exact supports, masks, actual family and conductors of the pinned multilinear source proof. Only its coefficient-energy input is replaced.

Historical mathematical source hashes and the precise public-edition changes are recorded in PROVENANCE.json. Historical input files are preserved separately and are not distributed or required by the portable checker. No third-party full text or HTML is included.
