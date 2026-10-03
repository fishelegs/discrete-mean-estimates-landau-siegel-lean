# Status: SOURCE_ONLY, independently reviewed

Date: 2026-10-03. The proof is a mathematical source argument with a separate independent mathematical review and finite regression evidence. It is not a Lean theorem or a kernel certificate. No strict signed gap, target gain, full Z2 estimate, or final Landau–Siegel conclusion is claimed.

Original `(A)` remains `L(1,chi)<L^(-2022)`, with `L=log D`; the distinct target scale remains `L^(-2024)`. All actual character families, branches, zero weights, profile coefficients, cutoff deletions, and normalizations retain their source meanings.

## Accepted mathematics

- Exact finite-box two-completion bridge (T2), with aggregate sparse error `O(a_norm^-1 L^(-551/4))+O(a_norm^-1 P^-K)`
- Exact finite-box three-completion bridge (T3), with aggregate sparse error `O(a_norm^-1 L^(-623/4))+O(a_norm^-1 P^-K)`
- All three root factors cancel exactly in T3; the resulting unit scalar, signs, parities and common Mellin measures remain in the signed pairing
- Common coefficients, both finite polynomial lengths below `P^2`, and the independent review's explicit high-frequency-tail payment precede the second large sieve

Both inequalities in the selected T2/T3 version are mandatory, including D, T_*, M, U and all fixed support constants. The rough RS region and the `P^1.8` example are illustrations only; the latter retains the fixed `P^.0005` profile-width factor. In the convention `power_gamma(n)=n^(-gamma)`, the raw reflected main is `chi*power_(-beta3)` and the D coefficient in `C conjugate(D)` is `chi*power_(+beta3)`.

The comparison retains the actual `Psi1` whole quadratic form and its genuine complement. Cauchy enlarges only nonnegative square sums; no signed `Psi2` deletion or conjugation closure is asserted. The full signed estimate at constant `m_H` precision remains open.

Global completion shows only that the completed observable and the original observable have a non-negligible global difference. The globally completed right-contour contribution must be retained in that comparison. It does not prove that the original long left complement alone equals `m_H`.

## Files and reproduction

`PROOF.md` contains the full public proof; `INDEPENDENT_REVIEW.md` contains the full source review. The review's original verdict applies to the historical candidate hash recorded in `PROVENANCE.json`. Editorial scope clarifications are explicitly listed there. This edition is not represented as a newly independently reviewed mathematical theorem.

`results/*_ORIGINAL.json` preserves the original receipts byte for byte. `results/*_RERUN.json` records reruns of the portable scripts. Finite exact identities, rational accounting, and numerical Fourier/branch checks have different scopes; none certifies an asymptotic contour argument or a signed gain.

From any working directory, use a path to this folder:

    python verify_bundle.py
    python verify_bundle.py --rerun

The first command needs only Python's standard library. The second requires the versions in `requirements.txt` or compatible installed versions, writes temporary receipts outside the package, and makes no network request. Run individual scripts with `--output FILE` to retain a fresh receipt. No command invokes Lean. See `REPRODUCE.md` for the exact checks and trust boundary.
