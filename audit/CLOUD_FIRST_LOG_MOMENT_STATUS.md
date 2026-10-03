# Actual first logarithmic moment and curvature

The actual strict moment M1 = sum_{1 <= n < D^4} |nu_chi(n)|^2 log(n)/n is now centrally verified. With L=log D, d=L'(1,chi), e=L''(1,chi)/2, a the original arithmetic normalizer, and J_D the logarithmic derivative of the actual correction factor, the proof gives

    M1 = -a (2e/d + 2 gamma_E + J_D) + o(1),
    J_D = -2 zeta'(2)/zeta(2) + sum_{q|D} log(q)/(q+1).

The conductor threshold precedes both D and the actual primitive real character satisfying the original assumption (A), with exponent -2022. The existing eventual a>1/2 converts the absolute error to o(a). Actual complex jets and the complete correction quotient are proved real; d is proved nonzero only in its required eventual scope.

The source chain proves the Gaussian double-Perron inversion, fourth-order residue, finite and infinite contour shifts, genuine infinite series/integral interchange, and all unsmoothing ranges. The middle tail uses the original Lemma 3.1 through P^2. The strict D^4 endpoint is included explicitly. A conductor-only quantitative budget tends to zero; no desired error estimate is a premise.

Consequences include uniform e/d=O(log D) and e/(d log P)=O((log D)^-8). The n=4 term gives M1 >= log(4)/4 for D>=2. Combining the proved a <= C_a L^4 with this term gives fixed positive c such that M1/a >= c L^-4 and M1/(a log P) >= c L^-13. These are arithmetic curvature and mass statements. They do not establish a favorable signed correction, the disputed mean matrix, or the main theorem.

All 23 proof/regression modules were relocated by changing import identifiers only and re-elaborated. The central audit checks all 159 named public declarations and all 310 owned declarations, including private and generated declarations, and requires 23 nonempty owners. This prevents an empty audit after module renaming. Only propext, Classical.choice, and Quot.sound occur. Seven expanded regressions, the 5658-job full project, 1851 source guards, and both generated import registries pass. The strict heuristic remains nonzero; its new candidates are individually reviewed.

The ledger remains 36 original plus 2 explicitly repaired statements, 38/51. This auxiliary result adds no newly completed numbered statement.

- [Uniform moment](../ZhangLS/Spec/LogMomentUniform.lean)
- [Actual curvature](../ZhangLS/Spec/ActualCurvatureConstraint.lean)
- [Positive arithmetic mass](../ZhangLS/Spec/FirstLogMomentLower.lean)
- [Expanded regressions](../ZhangLS/Spec/FirstLogRegressions.lean)
- [Independent review](first_log_moment/INDEPENDENT_REVIEW.md)
- [Verification record](cloud_first_log_moment_verification.json)
- [Public axiom inventory](cloud_first_log_moment_axioms.log)
- [Complete owner inventory](cloud_first_log_moment_owned.json)
- [Source fingerprints](cloud_first_log_moment_source_hashes.json)
- [Heuristic-candidate review](cloud_first_log_moment_strict_review.json)

Reproduce with `lake build ZhangLS.Spec.FirstLogRegressions`, the two `audit/CloudFirstLogMoment*.lean` drivers using `lake env lean -j1`, then `lake build` and the existing import/source/structure checks.
