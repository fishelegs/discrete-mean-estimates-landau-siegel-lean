# Verified arithmetic and local-residue components for Lemma15.1

The actual nu/Mobius convolution, coefficient-basis conversion on the original rough domain, and true zeta local residue have now been kernel checked. Full original Lemma15.1 remains unproved.

## Genuine results

- Exact rho-star = rho * (nu times n^beta), using the actual existing nu arithmetic function
- An explicit weighted finite replacement error preserving all original weights and rough cutoffs. Its right side is still an actual nu-convolution sum; no decay rate is claimed
- On the original rough set, n is coprime to D and b-psi(n1*n)chi(n)=chi(n1)b-chi-psi(n1*n)
- Exact punctured-limit residue of the genuine AppendixB zeta/Gaussian integrand: -A(0)omega1(-gamma)/(gamma*zeta(1-beta)). The true pole-removed-zeta and Gaussian correction factors are retained
- An explicit local error in those actual analytic deviations, with its closeness condition displayed
- The terminal integral, after justified variable change and integration by parts, equals -i*pi*j*b-star

## Source repair obligations

Official(15.1) writes the B expansion in the chi-psi basis, whereas the convolution before(15.5) uses the psi basis. Both natural coefficient conventions are separately defined; they cannot be silently interchanged. The conversion above explains the external chi cancellation on the rough domain. The natural convolution extension at chi(n)=0 is explicit, not asserted to follow from coefficient uniqueness there.

Official TeX5317 and renderedPDF108 both print P^12 in(B.3). That lies beyond the original kappa1 support. H14's actual strict n<P^(1/2) cutoff instead forces a complementary >=P^(1/2) tail; the endpoint still requires accounting. These source facts and the original alpha1 ambiguity are preserved, rather than hidden inside a renamed target. [Detailed source/derivation audit](CLOUD_LEMMA151_SOURCE_AND_ARITHMETIC_AUDIT.md).

## Validation and scope

Six production modules with62 declarations, plus7 named audit regressions: all69 axiom checks use only standard axioms.3859 dependency jobs and5221 whole-project jobs PASS;1348 Lean sources pass guards.967 SPEC/1232 full imports; strict audit remains392 candidates/nonzero exit, no new candidate. [Verification](cloud_lemma151_arithmetic_verification.json), [axioms](cloud_lemma151_arithmetic_axioms.log), [hashes](cloud_lemma151_arithmetic_source_hashes.json).

Reproduce `lake build ZhangLS.Spec.Lemma151Basis ZhangLS.Spec.Lemma151LocalResidue ZhangLS.Spec.Lemma151WeightedError ZhangLS.Spec.Lemma151TailIntegral`, `lake env lean audit/CloudLemma151ArithmeticRegression.lean`, `lake build`.

Coefficient-basis propagation through the full B expansion, rough-convolution collision control, a uniform one-kernel asymptotic, global contour error and the complete original target are still missing. No final numerical repair is proved. Numbered completion remains34 original +2 repaired=36/51.
