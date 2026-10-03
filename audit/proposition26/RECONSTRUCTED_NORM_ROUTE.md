# Reconstructed weighted norm for original Proposition 2.6

This is an independent sufficient route to Proposition 2.6 of [arXiv:2211.02515v1](https://arxiv.org/abs/2211.02515). It uses the literal source objects in `Proposition26OriginalObjects.lean`. It does not assert what the missing cross-references (8.25)/(8.26) were intended to say.

Write L=log D, P=exp(L^9), alpha=pi/L^9, and M=sum of the actual primes in the original strict short interval. The fixed positive shift c is compatible with the actual C-star positivity theorem. All subsequent constants/thresholds are uniform in the real primitive chi, original (A), good family, genuine zero set, and genuine square-root branches.

## The finite arithmetic input

For any purely imaginary three shifts beta, put b_{d,r}=mu*xi_{d,r}. At zero shift the local coefficients of xi are:

- q not dividing dr: xi(q^k)=1
- q dividing r: xi(q^k)=k+1
- q dividing d but not r: xi(q^k)=1-k/(q-1)

Thus the local absolute harmonic factors for b are respectively 1, q/(q-1), and 1+1/(q-1)^2. The actual finite-beta local perturbation is controlled by delta_q=sum_i|q^(-beta_i)-1|. On a finite support n<=P, only primes q<=P occur; Chebyshev summation bounds sum_q log(q)/q by log(4)(2+log P). Since |beta_i|<=3alpha, the accumulated perturbation costs an absolute constant. This gives the actual finite bound

sum_{n<=P} |b_{d,r}(n)|/n <= C r/phi(r),

and a constant bound for the actual Lambda factor on the relevant finite d,r box. It is essential that this is a finite prime bound. For nonzero shifts no global all-prime absolute convergence at real part one is asserted.

The actual finite chi-harmonic polynomial has the uniform bound

|sum_{n<=x} chi(n)n^(-s)| <= (14 exp(16)+2)L,  Re s=1, |s|<=D.

The proof uses the already proved actual L-function bound and periodic-character Abel tail, splitting at D^2. Finite complex Abel summation then costs exactly an endpoint plus the successive variation of the coefficient profile. This controls both original S_j inner sums, retaining their chi(dr) factors. Expanding xi=1*b in the second sum is an exact finite divisor reindexing.

The factor r/phi(r) combines with the original outer 1/(dr phi(r)) to leave 1/(d phi(r)^2). No totient denominator is discarded. The concrete series sum_r phi(r)^(-2) converges: 1/phi(r)<=tau_2(r)/r, tau_2(r)^2<=tau_4(r), and the genuine tau_4 Dirichlet series converges at 2. The d sum costs log P=L^9. Therefore every fixed-BV profile has actual

|S_j| <= C V^2 L^11.

The coefficient support and the family are still the original strict ones. The source chi(dr) factors may be bounded above by one explicitly; this coarse route does not need to recover a phi(D)/D main-term asymptotic.

## The actual zero norm

Completed original Lemma 8.1 and Proposition 7.1 give the actual energy bound

Energy(a) <= M ((4/alpha+C L^2) sum_j |S_j(a,conj a)|+epsilon).

The constant is fixed before epsilon and all bounded sequences. After the finite arithmetic bound, this is O(M L^20), uniformly for chi-weighted BV profiles and |v|<=L^20. The logarithmically growing frequency range is proved to lie below conductor height, not inserted as an assumption of uniformity.

For small smoothing errors it is crucial to apply this estimate to L^24 times the error profile. Its BV bound is a fixed absolute constant. Exact quadratic homogeneity then restores L^-48. Applying the mean formula directly to unnormalized small coefficients would leave an arbitrary o(M) remainder, which is insufficient after multiplication by the coarse H2 norm.

## Original transfer budget

The actual tent-minus-Gaussian profiles have variation at most 16000 L^-24 on every positive monotone finite sample. A strict initial cutoff preserves the same last-endpoint variation bound: the terminal jump replaces that endpoint. The auxiliary cutoff may be P^.505, eventually below PT^-2. Beyond it the actual Gaussian series tail is bounded by 2*sum_n n^-2*exp(-L^10). Constant-polynomial energy controls this tail over the actual zeros.

Consequently, each of the two unsmoothing errors has energy O(M L^-28). The genuine E2 has the sharp proved Gaussian transfer factor L^-121 times an integral of short-polynomial energies. The Gaussian mass is 2 sqrt(pi)L^15, so the actual smoothed defect has energy O(M L^-86).

The H2 components are exactly their original phases times chi-twisted linear ramps; after putting the phase into the frequency, each ramp is nonnegative and decreasing with BV norm at most one. Thus H2 has energy O(M L^20), with its exact P2/P3 cutoffs and exact iota3/iota4 constants retained.

The actual chi*psi functional-equation factor has modulus one on the critical line, and the real Gaussian coefficients obey exact conjugate reflection. Hence the original J1-Z*conj(J2) splits into the two actual unsmoothing errors and the actual smoothed defect. Weighted Cauchy on the literal Xi3 now gives Xi3=O(M L^-4).

Finally the proved original Lemma 17.1 gives the actual a>1/2 uniformly under (A). This converts the last bound to the original uniform Xi3=o(a M). The route neither requires the unfinished sharper Section 9 bound Xi12=O(a M), nor uses a disputed numerical main constant, a surrogate C-star estimate in terms of F, or a contradiction from not-(A).

## Proof status

All thirty-two candidate modules are kernel checked, including the genuine finite-beta Euler input, normalized Gaussian attachments, same-c uniform BV norm and the final original Proposition26Target. The final source theorem was successfully compiled at 2026-10-03 14:59:41 UTC. Its separate actual J-defect package supplies the same positive compatible c and the full BV norm before all fixed profile bounds.

All fifteen expanded-source regressions passed. Complete actual owner enumeration checked 422 production declarations across the thirty-two modules and all 15 regression declarations, including private/generated ownership without name filtering. Only propext, Classical.choice and Quot.sound occur. Exact successful compiler receipts, source/object fingerprints, actual imported object components and the Lean binary fingerprint are recorded. Imported third-party source text is not copied into the delivery.
