# Actual short-upsilon reduction and the remaining repair obligations

Status: the finite actual arithmetic and full primitive-character-family error bridge have passed central Lean verification. The actual C1/T1 contour attachment remains independently reviewed source-level mathematics. R3 is partially Lean-proved; no strict gain or main theorem follows.

## Newly verified Lean portion

Five proof/regression modules prove the actual ramified convolution identities, the closed d<=D^4 cutoff, all N<=floor(P^2) energy bound S_N^2<=1260*3^80*L^-1291, and its explicit consequence S_N<=36*3^40*L^-640. One absolute conductor threshold is chosen before the character, all pure shift triples and N. Actual L3.1, L3.3 and L8.1 inputs yield the full primitive-family trilinear error O(B1 B2 P^2 L^-302), at every critical-line height, with its conjugate version. The complete product constraints and genuine residual polynomial are preserved.

Central verification checked56 public declarations, all80 owned declarations in five nonempty owners, five Lean regression theorems, all6067 external source/object pins,5709 full-project build jobs and1905 source guards. Only propext, Classical.choice and Quot.sound occur. Strict heuristic candidates remain442 with zero added. The56 finite arithmetic endpoint checks were independently replayed. See [exact scope](short_upsilon/MATHEMATICAL_SCOPE.md), [inventories](short_upsilon/AXIOM_INVENTORY.json), [reproduction](short_upsilon/REPRODUCE.md) and [verification record](cloud_short_upsilon_verification.json).

The normalized contour exponent -225 discussed below is source-level, not a newly proved Lean endpoint. R2 must still attach the actual finite contours, unit gamma factors and Gaussian integration.

Let L=log D and P=exp(L^9). For the actual real primitive character and original assumption (A), set nu=1*chi and upsilon=mu*(mu chi), with Dirichlet convolution. Complete multiplicativity, including ramified primes, gives mu=upsilon*chi. The split/inert/ramified local values prove |upsilon|<=nu<=tau2. For purely imaginary beta,

    kappa_beta = upsilon * (chi * power_beta1 * power_beta2 * power_beta3).

Replace upsilon(d) by upsilon(d)1[d<=D^4], preserving every total product cutoff. Write delta_kappa for the difference and S_N=sum_{n<=N}|delta_kappa(n)|^2/n. Divisor Cauchy and tau submultiplicativity give

    S_N <= (sum_{D^4<d<=N}|upsilon(d)|^2 tau2(d)/d)
           (sum_{m<=N}tau4(m)^2 tau2(m)/m).

Using |upsilon|<=nu, Cauchy again, tau2^4<=tau16, tau4^2 tau2<=tau32, and harmonic convolution bounds gives S_N<=sqrt(T_N) H_N^40. The actual proved Lemma3.1 supplies T_N<=1260 L^-2011 through floor(P^2), while H_N<=3L^9. Thus for every N<=floor(P^2), beyond one uniform conductor threshold,

    S_N <= sqrt(1260) 3^40 L^(-1291/2) = O(L^-645.5).

This uses the full P^2 square-tail theorem, never the D^8-limited Lemma3.2. The statement includes all ramified terms and does not require beta3=beta1+beta2.

On each already attached actual finite central C1/T1 contour, masks are independent of the prime/character. Lemma3.3 bounds the delta polynomial's family second moment by P^2 L^-640; the actual fourth moments of the two bounded-coefficient polynomials are O(P^2 L^36). Holder 2/4/4 gives P^2 L^-302. All inherited gamma/root/conductor/branch multipliers have modulus one on the central line, and the Gaussian has normalized mass at most one. The actual M>=P^2/(4L^77) then yields an added normalized error O(a^-1 L^-225) in each of the four operators. Keeping fractional exponents gives the stronger L^-227.75 rate.

The new coefficient has the correct envelope tau6, not tau4. Redoing principal corrections with log^5 instead of log^3 preserves the existing power savings. The four remaining factors retain their product constraint; configurations with factors equal to one are not discarded. Total representation error is still O(a^-1 L^-14), inherited from the [finite-window attachment](annular_covariance/STATUS.md).

## Why the paired phase terms do not cancel automatically

The structured degree-four product is Q_beta(s)=L(s,chi psi) product_j L(s+beta_j,psi). Its exact functional equation includes Z_chipsi(s) product_j Z_psi(s+beta_j). The paired contour multiplier accounts for product_j Z_psi(s+beta_j)/Z_psi(s), leaving the full factor Z_psi(s) Z_chipsi(s), including chi's conductor/gamma factor.

Writing G for the actual short-upsilon polynomial and Gdual for its reflected dual, a legal resummation would therefore factor the paired expressions through

    H = (Z_psi Z_chipsi) G - Gdual,

not through zero. The existing actual good-family product approximation and approximate functional equation imply on the common central segment

    H/Gdual = A_normalized - 2 + O(L^-100),
    A_normalized = L(s,psi)L(s,chi psi)/F(s,psi).

At actual good-family zeros this gives H=-2 Gdual*(1+O(L^-100)). This range is the good family only. The [independently reviewed weighted attachment](paired_phase_attachment/STATUS.md) now supplies the legal resummation, weighted norm/error and bad-family control at source level, preserving total error O(a^-1 L^-14). The signed resulting main integral remains unevaluated; a zero identity alone does not establish gain. Finite Fourier completion of one pure-power variable brings inverse-additive and Kl3 terms to a common Kl2 family, but does not remove the missing gamma factor or prove a saving.

The remaining obligation is an actual evaluated matrix/target residual with a favorable sign, actual Gram/Schur nondegeneracy, and a complete relative error budget. If all new entries were merely o(1), the chosen zero-leading-moment trial would have no leading gain. A valid repair needs a nonzero actual target residual or a quantified next-order margin. These conditions are recorded as separate [critical-path nodes](cloud_repair_critical_path.json).

## Evidence and limits

The source derivation and an independent review agree on all exponents, ramification, finite contour factors, constrained operators and principal corrections. The supplied arithmetic regressions reproduce exactly. Independent checks cover 1360 primitive-kernel cases, 40 full-operator cases and 1272 finite Fourier transforms. These finite checks are regressions, not asymptotic proofs or Lean certificates. The full mathematical derivation is represented above; formal attachment of the analytic operators remains open.

Source-level derivation SHA256: b5584906c40bc2447e45fc300d502eee23fe8a816b89987c3bae54a1e935266b.
Independent review SHA256: 1bd6033619e906f81dcd6fd31be5f18f8312c0b2e1c64787bdb76f62c7644cce.

Primary source: [Zhang, arXiv:2211.02515v1](https://arxiv.org/abs/2211.02515v1). Actual proved inputs include Lemma31, Lemma33, Lemma81PolynomialFourthMoment, Lemma81PrimeMassLower, Lemma23CoefficientBounds, Lemma23ProductApproximation and Lemma44ApproximateFunctionalEquation in ZhangLS/Spec. This audit does not use a supposed unconditional counterexample or an assumed nonexistence of characters satisfying (A).
