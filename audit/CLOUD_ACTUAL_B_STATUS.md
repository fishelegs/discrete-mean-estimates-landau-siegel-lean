# Verified actual B coefficient bridge

The original source B product has now been connected to its genuine character-weighted coefficients and the pre-(15.5) shifted L-function convolution. This closes an exact arithmetic input required for the Section15 application of Proposition14.1; full Lemma15.1 and the final mean asymptotics remain open.

## Exact conclusions

- B is independently defined from the original finite H14/H12/H13 sums, then proved equal to both the chi*psi expansion with b0 and the psi expansion with bpsi=chi*b0
- On Re(s)>1, actual L(s+beta1,psi)L(s+beta2,psi)/L(s,psi) times B has coefficients psi*(kappa1*bpsi). Absolute convergence is proved, not supplied as a target-shaped hypothesis
- These genuine convolution coefficients satisfy C tau5 uniformly, with C=(1+norm(iota2))*(norm(iota3)+norm(iota4)) independent of D,c,chi,n
- The exact strict B support is bounded by max(P^0.998,P T^(-10)), including zero at the endpoint. Original P2 and both beta shifts are retained
- The four original iota combinations and B itself are unchanged by the basis conversion. At chi(n)=0, the natural convolution extension is explicit and coefficient uniqueness is not claimed

## Scope

Feeding b0 directly into a psi-basis convolution is unjustified; the operand must be bpsi. This correction alone leaves a finite model already derived from the actual B product unchanged. It does not establish the contested AppendixB tail phase/cutoff, uniform rough-domain asymptotic, final leading mean matrix or final numerical margin. [Source derivation and remaining obligations](CLOUD_ACTUAL_B_SOURCE_AUDIT.md).

## Validation

Six production modules, 87 public declarations (71 proof declarations, including actual-object regressions), one standalone axiom audit; only propext, Classical.choice and Quot.sound. All six module targets pass serially, followed by the 5337-job whole-project build. 1482 Lean sources pass guards; 1083 SPEC and 1348 full aggregate imports. Strict heuristic audit remains 413 candidates, no new candidate. [Evidence](cloud_actual_b_verification.json), [axioms](cloud_actual_b_axioms.log), [source hashes](cloud_actual_b_source_hashes.json).

Reproduce `lake build ZhangLS.Spec.BSourceRegressions`, `lake env lean -j1 audit/CloudActualBCoefficientAxioms.lean`, and `lake build`. Numbered completion stays34 original +2 repaired=36/51.
