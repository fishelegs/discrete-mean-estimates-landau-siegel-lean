# Migration Step 08 — Reconstructing Zhang Lemma 5.7

Step 08 replaces the legacy pseudo-proof of Lemma 5.7 with a faithful quantitative specification.

The paper's Lemma 5.7 states, under the contradiction hypothesis (A),

`L'(1, χ) ≫ D / φ(D)`.

Its proof has three genuine components:

1. **Arithmetic lower bound.** The smoothed divisor sum on the right of the Mellin identity is bounded below by a positive absolute constant times `D / φ(D)`; Zhang uses that `ν(n)=1` for `n | D`.
2. **Contour shift.** The Mellin integral is shifted left, picking up the residue involving `L'(1,χ)` and `L(1,χ)`.
3. **Error control under (A).** The `L(1,χ)` contribution and shifted contour are negligible, yielding `mainSum = L'(1,χ) + o(D/φ(D))` in the quantitative form required for the lower bound.

The new module `ZhangLS/Spec/Lemma57.lean` introduces explicit structures for components (1) and (2), an explicit small-error predicate for (3), and proves only the legitimate final real-inequality transfer.

In particular, the new proof does **not** use the legacy `Lemma_5_7_Proved_Int`, which merely assumes a lower bound on `L_prime + err` and then closes an integer inequality with `omega`.

## Status

- Paper statement: SPECIFIED.
- Real/complex derivative compatibility: source-level proof present from Step 07.
- Final quantitative transfer: PROVED in Lean source.
- Arithmetic divisor-sum lower bound: OPEN.
- Mellin inversion / contour-shift identity: OPEN.
- Shifted-contour and `(A)` error estimate: OPEN.
- Kernel compilation: BLOCKED by the current container's missing Lean toolchain/network access.
