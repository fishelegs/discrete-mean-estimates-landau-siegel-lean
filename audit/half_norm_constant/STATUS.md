# Actual right-term half-norm constant

**Accepted at source level on 2026-10-03.** The complete proof is in [PROOF.md](PROOF.md), with the final [independent review](INDEPENDENT_REVIEW.md) and [review scope](REVIEW_SCOPE.md).

Under the unchanged original assumption `(A): L(1,chi)<(log D)^-2022`, the actual completed right term satisfies

    Re J_right^infinity = Im R_D = (1/2)m_H + o(1),
    Im R_pr = (1/2)m_H + o(1),
    R_np = o(1).

The first line is equality up to o(1); the final estimate is complex. Its proof uses the separate complex comparisons `J_right^infinity=Theta_H/(a*Mcal)+o(1)` and `-i R_pr=PrincipalMean_P7/(a*Mcal)+o(1)`, followed by the original complex P7 reduction. The actual Lemma 8.1 gives `Re(Theta_H/(a*Mcal))=m_H/2+o(1)`. No complex estimate is inferred from real parts alone.

The finite mollifier cutoff and full D-deletion are paid explicitly. The full quotient remains on safe lines `Re(s)>=3/2`; only the finite coefficient difference is moved to `Re(s)=1/2`. Both profile masks, the positive prime phase, compatible shifts, actual family and normalization are preserved.

This determines the right-term constant. It is not a percentage of proof completion, a strict saving, or a proof of the final exponent-2024 target. After the accepted sparse-long reduction, the exact remaining signed estimate is

    Re Delta_rho,high <= (1/2-epsilon)m_H + o(1),

for fixed epsilon>0, retaining the original whole-label condition `2K>P^(99/100)`. That inequality remains open.

The original assumption exponent 2022 and final target exponent 2024 are unchanged. This package is source-only and supplies no Lean certification or transitive axiom-closure certificate. Finite check fixtures are not claimed to satisfy (A). No AFE is used to assign the constant.

Run `python3 verify_bundle.py --require-accepted` for package integrity and both portable checkers. Add `--repo PATH` to verify the exact referenced repository sources and public dependencies. See [REPRODUCE.md](REPRODUCE.md).
