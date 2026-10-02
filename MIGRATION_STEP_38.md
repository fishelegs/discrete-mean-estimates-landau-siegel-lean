# Step 38 — Rectangle orientation and winding integral

Step 38 formalizes the exact finite rectangle used in Zhang's contour shift.
The trusted implementation is
`ZhangLS/Spec/Lemma57RectangleWinding.lean`.

## Proved in Lean

The module defines the positively oriented boundary functional for
`[-1/2,1] × [-T,T]` and proves:

1. the top, bottom, left, and right edges have the signs required by positive
   orientation;
2. the two horizontal `s⁻¹` integrals reduce to real integrals of
   `(T²+x²)⁻¹`;
3. each vertical integral reduces to an odd rational term, whose symmetric
   integral vanishes, and an arctangent term;
4. the arctangent reciprocal identities give the exact winding formula
   `∮_∂R ds/s = 2πi` for every `T > 0`;
5. `Lemma57FiniteRectangleShift` is equivalent to the standard unnormalized
   identity
   `∮_∂R F(s) ds = 2πi · lemma57ResidueValue χ`.

The calculation avoids any hidden choice of a complex logarithm branch.

## Mathematical frontier

The rectangle's orientation and winding around zero are now kernel-checked.
The remaining finite-contour task is to decompose the actual integrand into
its `s⁻²` principal part, its residue multiple of `s⁻¹`, and an entire
remainder.  Cauchy–Goursat should then kill the entire remainder, while the
`s⁻²` boundary integral telescopes to zero and this step evaluates the
`s⁻¹` term.

Left-line integrability, horizontal decay, and the final Assumption-(A) error
bound remain separate global estimates.

## Verification

The authoritative `tools/verify_all_lean.sh` run completed successfully on
2026-09-13:

- trusted `Spec/All.lean` coverage: 26 modules;
- full `All.lean` coverage: 104 modules;
- full project kernel build: 3537 jobs;
- audit regression modules: 10, all passed;
- placeholder and source-structure checks: 117 Lean files, no failures.

The signed-off result is `LEAN_KERNEL_VERIFICATION=PASS`; machine-readable
details are recorded in `audit/lean_kernel_verification.txt`.
