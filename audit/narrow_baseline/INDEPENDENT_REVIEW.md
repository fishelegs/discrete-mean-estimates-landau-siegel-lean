# Independent review: fixed smooth narrow baseline

Verdict: ACCEPT at source level, with the stated fixed smooth chi-profile scope. The reviewed candidate is `BASELINE_OBSTRUCTION.md`, SHA256 `26ea1c8751b743781f0a9d70bbe1b1a9b26a568dd346ec0c51d9c59bc481e21b`. This is not a Lean theorem. Its actual-mean argument uses the newly privately kernel-checked uniform BV theorem; central publication of that input is still pending.

## Scope and common constant

The result fixes two smooth complex functions before D and chi. Their supports are [.502,.504] and [.499,.500], and the coefficients are the literal chi times those profiles. Arbitrary bounded coefficient sequences with the same support, or uncontrolled D-dependent functions, are outside this theorem. Either fixed function may be zero; the proof removes zero generators before using a Gram inverse.

The compatible c is common to the actual positive zero measure, original mean formula, BV norm and all trial profiles. The final Lemma81Target wrapper is existential, but the three helpers in Lemma81.lean are valid for every positive compatible c: residue-deformation little-o and the two right-contour little-o bounds. Repeating the final triangle inequality attaches the original mean formula at the c selected by the proved BV construction. Original P7 is already available at every positive constant. The candidate's amended same-c explanation is therefore valid; no arbitrary existential witnesses are identified.

## Smooth reflection transfer

The source `lemma112_actual_approximation_bound` genuinely quantifies over all real z in [.5,.504], in the actual critical-line zero window and with the actual D*p product character. Integrating its defect against -f'(z) cancels the L-function term because both endpoint values of f vanish. Integration by parts gives the even Gaussian convolution K_A*f, A=L^24, and the exact reflected profile conjugate(f(1+delta-u)). The sign of the dual term is negative. Reality of chi and criticality convert the inverse-character dual sum to literal complex conjugation; the conductor shift delta remains exact.

The centered Gaussian has second moment1/(2A^2). Its vanishing first moment gives the uniform error ||f-K_A*f||_infinity<=||f''||_infinity/(4A^2). Applying the same second-difference identity to f' in L1 gives TV(f-K_A*f)<=||f'''||_1/(4A^2). Sampling at any monotone logarithmic subsequence does not increase variation. Defining the zero coefficient separately and imposing the actual strict cutoff contributes only endpoint/supremum jumps, with the same fixed constant. Multiplication by L^48 therefore gives a fixed admissible BV bound.

The genuine BV energy is O(M L^20), so unsmoothing costs O(M L^-76). The E2 estimate costs L^-136 times two Gaussian mass factors L^15 and the same L^20 norm, giving O(M L^-86). The true Gaussian tails above P^.505 are exponentially small since the support ends at most .504; the exponential quadratic L^48 term dominates the linear L^9 log-index growth uniformly. The actual weight mass follows from the n=1 polynomial in the same BV norm. Thus the normalized reflected-transfer norm is O(a^-1/2 L^-38), with no P^2/M substitution.

## Tent and joint-Gram extension

The measure f''+2ell f'+ell^2 f is finite for the continuous piecewise-C2 tent. Its f'' includes all three jumps, including the support endpoints. The Green kernel (v-t)exp(ell(v-t)) vanishes at v=t, so inclusive and exclusive conventions there do not alter the exact ramp identity. Independent symbolic integration reproduces the literal tent on all four regions using its three jump atoms and both density pieces, for an arbitrary nonzero complex ell.

The main operators contain f' and may jump. Assigning a one-sided value at such a point is legitimate only with an endpoint correction. The proposed proof supplies one. The existing `lemma84_actual_weight_layer` has exactly the stated arbitrary-subset real cutoff scope X/T<=dr<X. At dr=X the pointwise actual weight bound and the finite reciprocal-square sum give the extra2 WeightScale(B). Hence the closed layer mass is at most2 WeightScale(B)(3+H), H=log T, with every actual lambda/chi/mu/phi factor retained.

Finite-sum Fubini against the positive total-variation measure then pays the atomic layer after outer summation. The four raw error terms are precisely L^-11, H^5 L^-15, L^-13 and H^3 L^-16. With H=L^(11/10) their exponents are -11,-19/2,-13,-127/10. In particular, there is no replacement of the localized H mass by the full logP mass. The pointwise companion bound uses the total-variation norm, so |F_actual|=O(L^-6) remains valid. No inverse Pi is used.

The main arithmetic uses the exact ramified Pi collapse, relative lambda replacement and coprime-totient summation from the accepted smooth report. The resulting profile product is BV with finitely many jumps. Stieltjes partial summation depends on its fixed total variation; changing endpoint values affects only finitely many n=P^v, each with exponential 1/n decay. The normalization and original P7/L8 errors are unchanged: the worst new normalized arithmetic error is polylog(L)L^-1/2/a, which tends to zero because a>1/2. It is not an L^-8 error estimate.

The only varying functions are explicit translations/reflections of fixed smooth profiles. Their supports stay in a common compact subset of (0,1), their derivative, measure and variation bounds are unchanged, and their number of breakpoints is bounded. All the preceding bounds are uniform on that family. This supplies the required joint-Gram convergence, not merely pointwise convergence for separately fixed functions.

## Coercivity, minimization and normalization

The independent calculation includes the full skew and Volterra terms, bounded respectively by48d and48pi^2 d^3 times the derivative squared norm. On support length1/250 it gives B0(q,q)>=(4/pi)||q'||_2^2. In the fixed interval [.50125,.50175], both old reflected profiles vanish while the original tent derivative is500. Therefore the limiting residual squared norm is at least500/pi for every complex pair of coefficients.

For nonzero fixed old functions their derivative supports are disjoint. Coercivity bounds the old Gram below by (4/pi) min(||f'||_2^2,||g'||_2^2) times coefficient norm squared. The same bound holds uniformly under the small translation. Actual joint-Gram convergence and the strong reflection estimate give a positive actual old-Gram lower bound. The target norm and correlations are bounded, so the minimizing coefficients are uniformly bounded. Only then may the finite-entry o(1) error pass through the projection minimum. Removing zero generators handles all degenerate fixed choices.

Both the gap and target norm use exactly c-star*omega/(a*M). The real tent has derivative energy1000 and squared L2 mass1/750, so its limiting norm is8000/pi+44pi/375. Consequently the eventual actual gap250/pi is in the correct normalized squared-norm units. Using a target upper bound of this limit plus1 gives an eventual relative deficit greater than29/1000. The rational checker uses only3<pi<22/7 and verifies all constants exactly.

## Consequence and limits

For this fixed smooth narrow subfamily, a lower bound merely of size L^-8 for an additional projection component does not establish enough improvement to close the baseline's fixed deficit. It does not upper-bound that component; a genuinely constant-size gain remains a separate unproved possibility. The result does not rule out arbitrary narrow-window coefficients, wider supports, changed frequencies, other methods, or the original main theorem.

The current R5 positive-norm result remains valid. What fails is the proposed inference that this norm result plus a small new projection gain would make the existing narrow old span nearly optimal. Further work must evaluate the complete augmented deficit with its actual target norm and errors, or first supply a different legally attached baseline. No numerical coefficient or log exponent in the original conclusion has been silently changed.
