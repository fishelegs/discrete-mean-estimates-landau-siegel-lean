# Required corrected Mellin poles and remaining budget

This is a mathematical formulation for the next component, not a claim of formal proof.

Write gamma=beta_j (nonzero, j=1,2), Z(w)=w*zeta(1+w) with its analytic value Z(0)=1, and G(w)=T^w*omega_1(w), using the actual Section 16 smoothing transform. The corrected integrand, including ds/s, is

I(w) = V(1+w) zeta(1+w)^2 zeta(1+w-gamma)
       L(1+w,chi) L(1+w-gamma,chi)^2 G(w) / w.

Set

H(w) = V(1+w) Z(w)^2 Z(w-gamma)
       L(1+w,chi) L(1+w-gamma,chi)^2 G(w).

Where the pole-removed zeta factors and V are analytic, the meromorphic integrand is exactly

I(w) = H(w) / [w^3 (w-gamma)].

The two possible poles are w=0 (order at most 3) and w=gamma (order at most 1). Zeros of H can reduce these orders, so an unconditional exact-order assertion is unnecessary. Since gamma is nonzero at the original finite-D shifts, their residues must be computed separately before estimating their sum:

Res at 0 = -H''(0)/(2 gamma) - H'(0)/gamma^2 - H(0)/gamma^3,
Res at gamma = H(gamma)/gamma^3.

Their sum is the third divided difference

[H(gamma)-H(0)-gamma H'(0)-(gamma^2/2)H''(0)]/gamma^3.

This identity explains why separately bounding the four displayed singular-size terms loses the needed cancellation. A proof can use the analytic third Taylor remainder along the segment from 0 to gamma. The error analysis must retain all derivatives of the actual L factors, V, Z, and G, and must apply the actual Section 16 coefficient/smoothing and contour bounds. The new all-order V derivative estimate at 1 supplies one component only. Bounds at nearby points can be obtained from the same sector/disk with a smaller concentric disk, but are not separately stated in this freeze.

Required next outcomes:

1. Formal pole removal and meromorphic identity for the actual gamma and G
2. Both residue formulas, then their combined divided difference
3. Source-compatible approximation of that divided difference, with all log powers shown and the actual finite-D shifts retained
4. Corrected smoothing/unsmoothing and finite-cutoff bounds
5. Multiplication by the actual Section16 rho factors and p, preserving the error needed for o(p)

Neither the printed L'(1,chi)^3 U(1) residue shortcut nor a final o(p) conclusion follows from the center comparison alone. This freeze proves none of those next items.
