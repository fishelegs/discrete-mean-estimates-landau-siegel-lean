# Status: SOURCE_ONLY, independently reviewed

Date: 2026-10-03. The proof is a mathematical source argument with a separate independent mathematical review and finite regression evidence. It is not a Lean theorem or a kernel certificate. No strict signed gap, target gain, full Z2 estimate, or final Landau–Siegel conclusion is claimed.

Original `(A)` remains `L(1,chi)<L^(-2022)`, with `L=log D`; the distinct target scale remains `L^(-2024)`. All actual character families, branches, zero weights, profile coefficients, cutoff deletions, and normalizations retain their source meanings.

## Accepted mathematics

- Exact sampled-zero residue formula and safe right-minus-left contour representation
- The fixed profile's actual norm `m_H=lambda+o(1)`, with fixed `lambda>0`
- Whole original right contribution `O(a^-1 P^(-.49))`
- Cubic left kernel, exact parity/CRT/principal corrections, and the genuine `P^(3+o(1))` resonance
- Smooth long-pure blocks `R>=P^(1+delta)` or `S>=P^(1+delta)` are `O(a^-1 P^-K)` for every fixed K

The remaining theorem is an independently proved strict bound `Re I_left<=(1-epsilon)m_H+o(1)` with fixed epsilon>0 on the actual good family. The accepted AFE instead gives `Re I_left=m_H+o(1)` under `(A)`; reproducing that identity supplies no new sign information. The old R4 problem and all omitted signed matrix entries remain open at their stated scopes.

The independent review supplies the detailed safe-line and long-pure proofs. Its separate algebra supplement preserves all zero modes and shows eta's q variable is in the numerator of the double-completed phase. A `Psi2` correction is retained exactly whenever full-family completion is used.

## Files and reproduction

`PROOF.md` contains the full public proof; `INDEPENDENT_REVIEW.md` contains the full source review. The review's original verdict applies to the historical candidate hash recorded in `PROVENANCE.json`. Editorial scope clarifications are explicitly listed there. This edition is not represented as a newly independently reviewed mathematical theorem.

`results/*_ORIGINAL.json` preserves the original receipts byte for byte. `results/*_RERUN.json` records reruns of the portable scripts. Finite exact identities, rational accounting, and numerical Fourier/branch checks have different scopes; none certifies an asymptotic contour argument or a signed gain.

From any working directory, use a path to this folder:

    python verify_bundle.py
    python verify_bundle.py --rerun

The first command needs only Python's standard library. The second requires the versions in `requirements.txt` or compatible installed versions, writes temporary receipts outside the package, and makes no network request. Run individual scripts with `--output FILE` to retain a fresh receipt. No command invokes Lean. See `REPRODUCE.md` for the exact checks and trust boundary.
