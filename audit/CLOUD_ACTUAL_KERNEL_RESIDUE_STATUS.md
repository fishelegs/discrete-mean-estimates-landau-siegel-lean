# Actual Appendix B kernels and corrected Section 16 residues

This component release connects actual arithmetic kernels to their leading constants and evaluates the corrected Section 16 local contour. It does not complete Lemma 15.1, Lemma 16.2, either main mean, or the main theorem. The numbered ledger stays at 37/51: 35 original statements, including the disclosed 8.1 notation clarification, and two explicitly repaired statements.

## Actual rough kernels

`AppendixBActualKernelAsymptotics.lean` combines the actual rho-star-to-rho replacement with the full-kernel Perron and contour estimates. Under the original assumption (A), for fixed c>0 one conductor threshold works for every actual character, all three original finite-D beta shifts, every cutoff P2/P3/full P1, and all positive integers n1<T. The error is the explicitly defined

`appendixBActualRoughError(D,c) = C_R L^-8 + E(D,c)`,

where `C_R=189+36*pi*log(4)*exp(18*pi*log(4))` and

`E(D,c)=[4*(ContourBudget(D)+275*exp(5*pi))+(5*pi+40)*c*L+(412+960/pi+132*pi)*log(T)]/L^9`.

The existing component estimates prove that this tends to zero and is eventually O_c(L^(-79/10)). The full P1 kernel remains distinct from the strictly truncated H14 kernel. No definition is assigned to the paper's undefined alpha1, and these estimates do not prove an arbitrarily prescribed O(alpha1) rate.

The B.1 proof uses the genuine linear nu tail through P^2 from Lemma 3.1. This repairs the printed use of Lemma 3.2 beyond its D^8 range. The B.2 proof includes every prime power, q=2, ramified primes, and strict p<D^4. It derives genuine O(log D) prime logarithmic mass, rather than absorbing a growing logarithm into a constant. The actual rough replacement error is O(L^-8); for repair research at precisely that scale, its first-order arithmetic contribution must be retained rather than discarded as negligible.

## Corrected local Mellin residues

The six `Lemma162Mellin*`, `Lemma162TwoPoleCircle`, `Lemma162CauchyCancellation`, and `Lemma162ActualMellinResidues` modules use the corrected Euler factor V and the actual integrand H(w)/[w^3(w-gamma)]. They prove its equality to the actual convergent Dirichlet series, analyticity after pole removal, and both local residue contributions:

- at zero: `-H''(0)/(2*gamma)-H'(0)/gamma^2-H(0)/gamma^3`
- at gamma: `H(gamma)/gamma^3`

The combined enclosing-circle expression is the third divided difference of H. Both original finite-D shifts and one uniform conductor threshold are retained. The separate model obtained by setting the L factor to its linear Taylor term has exact circle value `d^3*(A(0)-gamma*A'(0))`. The derivative A'(0) retains V', the regularized zeta derivatives, Euler's constant, and log T. Thus the old printed single-center expression cannot be recovered by silently deleting the shifted pole or the derivative terms.

The quantitative local budget contains `60000*pi*C_sector*B/L^5`, the actual cubic-jet discrepancy, and `C_center*pi*|d|^3/L^9`. Here B explicitly bounds all remaining analytic factors. It is a hypothesis of this general local estimate, not an established absolute constant: T^w grows with D on the radius 1/(10L) circle. A global Section 16 asymptotic still requires the actual inversion, exterior factors, contour sides and tails, unsmoothing, and uniform arithmetic estimates.

## Remaining arithmetic and semantic bridges

For a repaired full 15.1 and its application, one still needs the strict sqrt(P) complement, the nu-weighted divisor-coefficient error, complete finite product reindexing, collision attachment, uniform n1 divisor assembly, and the downstream weighted N(Q) sum. The genuine B source has coefficient bpsi=chi*b0 in the psi basis, so the actual Section 15 convolution is kappa1*bpsi. It cannot be replaced by kappa1*b0 by definitional rewriting.

The literal printed B.3 cutoff P^12 lies outside P1 support. The intended sqrt(P) complement must include its equality endpoint. The limiting terminal residue also differs from the printed e1-double-prime: if P_j denotes the printed quantity and T_j the actual terminal residue, the independently checked identity is `T_j=exp(.756*pi*i)*conj(P_j)`. A repaired tail theorem must state its actual constant. These issues remain visible rather than being hidden in the completed count.

## Verification

Central build, source fingerprint, regression, axiom and structural evidence is recorded in `cloud_actual_kernel_residue_verification.json`. All 27 modules, the 202-declaration axiom audit, 12 expanded Mellin regressions and the complete project build passed centrally. Only propext, Classical.choice and Quot.sound occur. The source and structure guards pass; the strict heuristic audit has 430 candidates, comprising 429 historical entries and one reviewed false positive. The new local hn bound is derived from Complex.abs_re_le_norm and the left-contour geometry, rather than assumed. Its nonzero heuristic exit is retained. Source paths were relocated and imports qualified; the reviewed frozen proof bodies were preserved. The new one-kernel assembly is a triangle inequality with the maximum of the already proved uniform thresholds.

The independent source review is in `appendix_b_components/INDEPENDENT_REVIEW.md`; it accepts the two Appendix B packages at the component scope above. Separately reviewed smooth-profile precision research, if included, remains an analytical derivation rather than a Lean theorem or an established actual main-mean identity.
