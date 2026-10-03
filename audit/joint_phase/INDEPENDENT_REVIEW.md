# Independent review: corrected joint root–mollifier phase

Verdict: ACCEPT at source level for the precisely stated unweighted family theorem. Reviewed PROOF.md SHA256: `6853d48a231acc5e69f6546ecdb53cb38360045964fa662dcc677c7e4aee2e77`. This is not a Lean theorem. In particular the uniform hyper-Kloosterman estimate is an external deep theorem used through the cited CM Gauss-sum argument; this repository has not formalized that input.

The conclusion is a finite positive-mass statement for the corrected unit phase r*M/conjugate(M), not the printed bare phase, under the original exceptional-character assumption and original modulus scale. It leaves at least21/22-O(L^-2) of primitive even characters with M nonzero and distance greater than2/L from the cancelling phase. It does not prove almost-all nonvanishing, a full BPZ second-moment extension, or a statement about Zhang's character-dependent weighted zeros.

## Actual arithmetic and two cutoffs

I checked the inversion and the ramified cases separately. The literal upsilon=mu*(mu psi) is the convolution inverse of nu=1*psi, and its norm is bounded by nonnegative nu<=tau2. For n<=X the coefficient of M0*S-1 vanishes exactly because both hard cutoffs are vacuous. For n>X a contributing pair a,b<=X has one factor exceeding sqrt(X)=D^10>D^4. Positivity and symmetry then give the stated coefficientwise majorant2*(nu restricted to(D^4,X])*(nu restricted to[1,X]). No product restriction is erased from the actual residual; an enlargement appears only in a nonnegative bound.

At a ramified prime p, upsilon(p)=-1 and upsilon(p^j)=0 for j>=2. Thus deletion of multiples of a nonsquarefree conductor contributes exactly zero. For squarefree D, the exact deleted part is mu(D)*chi(D)/sqrt(D) times the restricted shorter upsilon polynomial with(m,D)=1. Its product with S has envelope tau4 after the scalar factor. There is no hidden tau(D) loss, and chi(D) is a unit since q does not divide D.

## Moment bounds and interpolation

For j<=11, the2j-variable divisor Cauchy inequality and tau2j submultiplicativity yield the two factors A_j and B_j in the candidate. The pointwise inequalities are precisely nu^2*tau2j^2<=tau(16j^2) and nu^2*tau2j<=tau(8j). Therefore A_j<=T^(1/2)*H^(8j^2), B_j<=H^(8j), and the2j norm of the residual is bounded by2*cq^(1/(2j))*T^(1/4)*H^(4j^2+4j). I independently reproduced these exponents.

All resulting polynomials have length at mostX^22. The common assumption2X^22<q rules out both ordinary and negative aliases in the even-character orthogonality. The principal subtraction is an exact negative squared term, so dropping it in an upper bound is legitimate. The correction factor is cq=(q-1)/(q-3), with no replacement of an average by a sum.

The deleted part's2j norm is at mostD^-1/2*cq^(1/(2j))*J^(8j). Interpolating20 and22 norms uses weight10/21 on the20 norm. The first bound has exponent-251/4, the second+101/4, and their combination is exactly-1399/84. The growing22nd bound does not invalidate interpolation. The corrected display(5.5) adds, rather than multiplies, the two residual contributions. The independent rational checker confirms this calculation.

At j=1 the inverse-error2 norm has exponent-1979/4; Markov consequently controls M=0 by O(L^-1979/2). All moment orders are fixed independently of D. The stated threshold conditions follow from log q>=L^9 versus440L, and X<=P^2. No varying-C analytic theorem is invoked in this finite arithmetic part.

## Twisted roots, the exact phase identity and all tails

The CRT identity for primitive characters gives r_chi=chi(D)*psi(q)*epsilon(psi)*tau(chi)^2/q for even chi. The parity factors agree also for odd psi. Expanding the2k Gauss factors and applying even-primitive orthogonality gives the two nonzero hyper-Kloosterman arguments plus the exact principal subtraction. The cited uniform bound applies at those nonzero arguments. Dividing by(q-3)/2 gives the displayed b(q,k); the factor4k*cq is retained.

Define U*=1 at M=0. Then Z=r*M*conjugate(S)=U*conjugate(MS) is exact even there, and U* always has norm one. For k<=21, the global identity reduces the phase error to |1-(MS)^k|. Expanding around1 and using the single21st norm bound controls every large-value and small-value event. No argument divides by small M, extends an annulus approximation to an uncontrolled tail, or assumes phase independence.

The spectral coefficient norm is bounded by4XH^2, using sum tau2(n)/sqrt(n)<=2sqrt(X)H. Every character monomial in its kth power is a unit ratio: its individual factors are below q, even if the full integer product is larger. The twisted-root bound is uniform in such ratios. Thus the full costD^420 times a fixed power of L is dominated by exp(-L^9/2); no coefficient or Fourier mode is omitted.

Independent exact complex-rational checks cover784 phase-power identities, including M=0 and k=21. These are regression checks, not numerical simulations of the exceptional-character hypothesis or substitutes for the source proof.

## Fejer constant and exact scope

The Fejer polynomial has degree21 and peak22. On |1+U*|<=2h, the geometric-series inequality gives Re((-U*)^k)>=1-2k^2h^2. The exact weighted square sum is1771/2, so the lower bound is22-3542h^2. Its expectation is at most1+21*delta. Nonnegativity proves the stated mass estimate whenever h<1/sqrt(161). Subtracting the separately controlled M=0 event is necessary and was done. At h=L^-1, the inverse-error contribution is smaller than L^-2, giving the stated21/22-O(L^-2) lower mass.

The same proof is uniform for every common deterministic real t: n^-it leaves inversion, coefficient energies and spectral norms unchanged. A common unit gamma factor only rotates the root moments. The displayed gamma ratio has unit norm on the critical line and is independent of the running even character. This does not justify selecting t separately at each character's zero; that selection can correlate completely with the corrected phase.

Any nonvanishing consequence additionally requires the actual full AFE error theorem. The repaired Y truncation alone is not that theorem. The discrete good-family c-star*omega measure and a strictly favorable R4/R7 gain remain separate open obligations. In particular this finite bridge does not restore the original main conclusion, alter its exponents, or turn the new trial into a proven independent direction at the original zeros.
