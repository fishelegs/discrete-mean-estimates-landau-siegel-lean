# Paired phase attachment: reviewed analytic error control

The actual phase-contour pairing can replace H=(Z_psi Z_chipsi)G-Gdual by Gdual(A_normalized-2) with added normalized errors O(a^-1 L^-105)+O(a^-1 L^-42). The total representation error remains O(a^-1 L^-14). This is an independently reviewed source-level derivation, not a new Lean proof or an evaluated signed main term.

The proof retains the raw approximate-functional-equation error until after Holder, uses genuine conductor-p fourth moments and a short-G sixth moment, and moves only the analytic error to Re(s)=1/2+alpha/2. It handles bad characters through the original kappa plus the already controlled short-upsilon difference. No new conductor-Dp high moment or false pointwise equality for a truncated series is assumed.

The new signed main integral remains explicit and unevaluated. Actual Gram/Schur nondegeneracy and the complete relative error after normalization remain open. A nonzero numerical or formal phase factor is not a strict gain, and the scalar M1 bound does not provide an actual Gram lower bound. The original final exponents have not changed.

- [Derivation and exact remaining obligation](DERIVATION.md)
- [Independent review](INDEPENDENT_REVIEW.md)
- [Finite candidate checks](CANDIDATE_CHECKS.json)
- [Independent checks](INDEPENDENT_CHECKS.json)
- [Fingerprints and scope](MANIFEST.json)

The portable Python checks use exact rational/symbolic algebra, finite Fourier/CRT identities and numerical Dirichlet-functional-equation regressions. Numerical cases use their stated tolerances; they are not interval certificates or substitutes for the uniform analytic proof. The independent script executes the candidate tests, compares exact algebra/counts, and rechecks numerical tolerances. Neither script executes Lean.
