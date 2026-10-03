# Proposition 2.6: exact source audit and independent transfer frontier

Source: [arXiv:2211.02515v1](https://arxiv.org/abs/2211.02515v1) (2022-11-04), checked against both the [PDF](https://arxiv.org/pdf/2211.02515v1) and original TeX. PDF SHA-256: `4e38ecfe1a6d3a93494e2f5cc5a3336c33b9d0981e8d5ccfcd8d8dec3e5ab713`. TeX SHA-256: `5dc202bdc414fb743004ae32e8dec0dd284636f7197b1cab78a46336e0cde30b`. Full third-party source text is retained only for private research and is excluded from the publication candidate.

## Exact target and objects

Equation (2.20) is
Xi3* = sum_{psi in Psi1} sum_{rho in Z(psi)} C*(rho,psi) |J1(rho,psi) - Z(rho,chi psi) conjugate(J2(rho,psi))| |H2(rho,psi)| omega(rho).

The target is Xi3*=o(a*actual_prime_mass) under original (A), uniformly over real primitive chi of sufficiently large modulus. The shift c is fixed and compatible with the actual L2.3 gap/nonnegativity theorem. Actual square-root branches remain arbitrary; their existence is already proved. The zero set is the strict actual L(s,psi)-zero window (2.14), not all product zeros and not model zeros. The inherited and documented notation reading Z-tilde=Z is needed where Sections 8/11 use an undefined tilde.

H2 = conjugate(iota3) H13 + conjugate(iota4) H12, with iota3=-1.00635-0.22789i and iota4=-0.68738+1.60688i. H13 has strict n<P^0.498, frequency beta6=3i alpha/2; H12 has strict n<P^0.5 T^-10, frequency beta7=5i alpha/2. Both contain the actual chi psi coefficients, the logarithmic linear cutoff and the original complex power (Pj/n)^beta.

J1 and J2 use the actual tent on [0.5,0.504], peaking at 0.502 with slopes ±500. The J2 argument shifts by 0.004-log(D*t0)/log(P). The factor Z is for the product character chi psi of modulus Dp. It is not Z(psi). The a factor is (6/pi^2) L'(1,chi)^2 product_{q|D} q/(q+1), and the mass is the actual sum of the primes in the paper's strict short interval.

## Original cross-references

Section 11 invokes (8.25) and (8.26) twice, and Section 12 invokes them again. The supplied TeX defines neither label. The retained PDF corroborates this: printed p50 ends at (8.24), and printed p51 begins Section 9/(9.1). Full-PDF text search finds (8.25)/(8.26) only at the later references. This is recorded as missing original cross-references, not as proof that an intended weighted-norm inequality is false. The required norm inputs have to be reconstructed from source arithmetic.

Section 9 also writes an extra sum over r<D after replacing it by an integral and gives inconsistent cross denominators (0.504 instead of the P2 exponent near 0.5) in (9.5)/(9.6). None of those scalar formulas or numerical values are used in this deliverable. The bounded H2 energy required by Section 11 has not been inferred from them.

## Exact independent frontier

1. Positivity and critical-line location on the actual finite index sets are supplied by completed Proposition 2.2 and the compatible L2.3 constant. The complex product C* omega equals a real nonnegative weight. This is an exact object bridge, not a surrogate norm.
2. Weighted finite Cauchy gives the literal Xi3 square bounded by the actual J-defect energy times the actual H2 energy.
3. The completed original L11.2 plus weighted integral Cauchy gives the actual smoothed defect energy bounded by C L^-121 times the Gaussian integral of the actual shifted-short-polynomial energy. The sharp Gaussian mass is 2 sqrt(pi) L^15. Thus a uniform bound K for that polynomial energy would yield 4 pi L^-106 K for the E2 energy (times the absolute L11.2 constant squared for the smoothed defect). This is a proved analytic reduction; K is not introduced as a premise of a completion theorem.
4. Completed original L8.1 and P7.1 give a uniform actual polynomial energy bound
   actual_prime_mass * ((4/alpha+C L^2) sum_{j=1}^3 |S_j(a,conjugate(a))| + epsilon).
   C is fixed after the coefficient bound and before epsilon; D0 is uniform in chi, the bounded sequence and all genuine branches. Every actual d,r,m,n, mu(r), phi(r), lambda and xi factor stays inside the source S_j. No phi(D)/D or character weight has been discarded or absorbed without proof.

## Reconstructed coarse route and current verification status

The sharper Section 8/9 main-term calculation and its phi(D)/D asymptotic remain outside this reconstruction. A sufficient independent route is documented in `RECONSTRUCTED_NORM_ROUTE.md`: actual chi harmonic cancellation plus finite mu*xi arithmetic, a convergent sum of inverse totient squares, fixed normalized Gaussian error profiles, and exact H2 ramp identities. The source chi(dr) factors are retained through the exact inner-sum attachments, then bounded above by one explicitly in the coarse norm; no phi(D)/D main-term formula is assumed. All thirty-two candidate modules are now kernel checked, including the genuine finite Euler input, uniform BV norm, actual H2 and Gaussian energy transfers, and `proposition26_proved : Proposition26Target`. The last theorem has no norm premise; it also exports one common c with the proved BV norm and the actual J-defect energy bound. All fifteen expanded-source regressions passed. Complete actual ownership checks passed for all 422 declarations in the thirty-two production modules and all 15 declarations of the regression module, including any private/generated declarations without namespace filtering. Every checked declaration uses only propext, Classical.choice and Quot.sound. Source, object, component and log fingerprints accompany the private verification packet.

The existing crude L8.1 fourth moments have size P^2 L^36. Actual prime mass has size P^2 L^-77, so exchanging P^2 for the actual mass loses L^77. The existing L5.9 quotient bound adds L^9; the resulting simple coarse route has L^122 relative to mass. Sharp E2 saving L^-106 leaves L^16, not o(1). These bounds therefore cannot close the transfer as they stand. In particular, L5.2 is a gamma-ratio estimate; it does not imply C* <= alpha^2 |F|^2, and F controls the L(psi)L(chi psi) product, not L'(psi) separately.

No axiom, sorry, native_decide, contradiction from not-(A), asserted desired norm bound or asserted final estimate is used. Compilation/ownership evidence is recorded separately and only successful checks count as verification.
