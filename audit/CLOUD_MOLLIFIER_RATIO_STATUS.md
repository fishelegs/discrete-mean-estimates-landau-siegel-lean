# Reviewed full mixed-moment ratio obstruction in fixed models

For all12 explicitly specified fixed-support/frequency Hermitian models, and **every nonzero z in C^4**, the exact model ratio satisfies

`|ell(z)|^2 / (R z* M z) < 1/2`.

All four coefficients vary, including H11's coefficient and its zero case. This is a standard-library rational interval certificate, centrally replayed and independently reviewed; it is not a Lean theorem or an actual-character impossibility theorem.

## Correct objective and sharp J norm

The source Cauchy reduction requires |ell|<=sqrt(QR)+sqrt(SE). If E tends to0 and S remains bounded, a contradictory pair of estimates needs |ell|²/(QR)>1 with a strict margin. Minimizing Q alone can miss changes to the mixed moment.

The original real tent has h=.004 and exact residue-model norm R=32/(pi*h)+88*pi*h/3≈2546.847703, rather than treating the coarse3000 bound as equality. The mixed functional is(T(H11,J1),T(H12,J1),T(J2,H13),T(J2,H12)), with T first-linear and second-conjugate-linear. Reflected J2, all conjugates and below-support integral terms are retained.

The representative .5:exact:upstream maximum is in[.40716299028789405383,.40716299028789405384]; the largest of all branches is in[.41452913819742913056,.41452913819742913057]. A positive5x5 augmented Hermitian LDL decomposition, with final Schur pivot>217, proves the all-vector bound without relying on an optimizer.

## Verification

- Central isolated standard-library replay reproduced the full certificate byte-for-byte
- Independent review replayed both the ratio and prior matrix certificates
- One separate direct-integration program at70 and100 digits is enclosed by the intervals
- A third program transcribed the original(10.12)-(10.17) integrals directly at85 digits; all four ell coefficients are enclosed
- The sharp R formula was independently rederived by integration by parts

[Report and admissible-family analysis](mollifier_ratio/REPORT.md), [independent review](mollifier_ratio/REVIEW.md), [replay instructions](mollifier_ratio/README.md).

## Scope boundary

Coefficient-only repair fails inside these twelve fixed models. This does not identify the models with actual character means, resolve the B coefficient-basis propagation, prove all uniform analytic errors, or exclude a changed true matrix after such reconstruction. Different beta constructions, support/frequency profiles or proofs remain open and require new positivity/residue/duality/support analysis. No claim against the main number-theoretic theorem follows. Numbered completion stays36/51.
