# Exact source B coefficient bridge

## Result and boundary

This package derives the exact B polynomial identity and the actual pre-(15.5)
L-function convolution. It also proves the uniform tau_5 coefficient majorant
needed to use Proposition 14.1 with Section 15's original input. It is not a
proof of Lemma 15.1, Proposition 14.1, a contour shift, or any arithmetic
asymptotic. It introduces no axioms or result-shaped analytic assumptions.

The original source B is defined as the product

    (H14(s,psi) + iota2 H12(s,psi)) H2(s,psi),
    H2 = conjugate(iota3) H13 + conjugate(iota4) H12.

H14, H12, H13 are independently defined as the actual finite character sums.
B is not defined as a sum with the desired final coefficient. Their exact
literal summands and strict endpoints are proved in BSourceRegressions.

## Source and coefficient conventions

Source: official arXiv:2211.02515v1 TeX and PDF.
TeX SHA256: 5dc202bdc414fb743004ae32e8dec0dd284636f7197b1cab78a46336e0cde30b.
PDF SHA256: 4e38ecfe1a6d3a93494e2f5cc5a3336c33b9d0981e8d5ccfcd8d8dec3e5ab713.
Relevant source displays are (2.21)-(2.27), (12.1)-(12.2), (15.1), and the
convolution immediately before (15.5). The source macros identify pc as chi psi.

Let U be the H14 coefficient plus iota2 times the H12 coefficient; let V be
conjugate(iota3) times the H13 coefficient plus conjugate(iota4) times H12.
Then the existing canonical convolution is

    b0(n) = sum_{ab=n} U(a)V(b) = lemma151BChiPsi D n,
    bpsi(n) = chi(n)b0(n) = lemma151BPsi chi n.

The package proves from the original finite sums, for every complex s,

    source B = LSeries(chi psi b0,s) = LSeries(psi bpsi,s).

Both equalities also target the existing
lemma23FiniteDirichletPolynomial API, with all finite-support obligations
proved for the actual kernels. Multiplicativity is applied directly at every
index, including ramified indices; no division by chi occurs.

At chi(n)=0 the chi psi display does not determine b(n). The choice b0 above
is the canonical convolution extension supplied by the original kernels.
b_ramified_display_invariance proves that arbitrary changes at such an index
are invisible in that displayed summand. b_psi_ramified_zero proves that the
canonical psi coefficient is zero there. No uniqueness claim is made for b0
from the character-weighted display alone.

## Source parameters and endpoints

All original values are retained exactly:

- P1 = P^0.504, P2 = P^0.5 T^(-10), P3 = P^0.498
- beta6 = 3 i alpha / 2; beta7 = 5 i alpha / 2
- iota2 = 0.94977 - 1.38995 i
- iota3 = -1.00635 - 0.22789 i
- iota4 = -0.68738 + 1.60688 i
- H14 uses n < P^(1/2), with the original P1 weight
- H12 and H13 use strict n < P2 and n < P3
- index zero is excluded by the actual kernel; its arithmetic coefficients vanish

No leading-order substitution P2=P^0.5 occurs. The generic product-support
theorem is discharged on U,V, and the exact support bound simplifies to

    bProductCutoff D = max(P^0.998, P T^(-10)).

Both b0 and bpsi vanish at and above this real bound. This is an exact upper
support bound, not an assertion that all lower coefficients are nonzero.
The bound and its simplification hold for every natural D, not just for a
large-D regime. The proof uses P>=1 and T>=1, established from their actual
logarithm/exponential definitions.

## Actual shifted L-function ratio

BRatioConvolution uses the already-existing lemma152Kappa, namely the actual
Mobius convolution of the beta1 and beta2 power coefficient functions.
It proves the character-twisted power shift and its absolute convergence,
then proves the quotient identity using the actual Dirichlet-character L-series
and Mobius inverse. On Re(s)>1, it transfers to actual LFunction values.

The public theorem b_source_ratio_convolution is quantified over every
D,p, real primitive chi modulo D, character psi modulo nonzero p, original
real c, and complex s with Re(s)>1. Its conclusion is

    L(s+beta1,psi)L(s+beta2,psi)/L(s,psi) * source B
      = LSeries(psi * (lemma152Kappa(actualBeta)*bPsiArithmetic chi),s).

The original c-dependent beta1 and beta2 are not replaced by their leading
values. Their real parts vanish by the existing exact definitions. No
summability assumption is left to the caller: it is proved from Re(s)>1 and
the finite support of the actual B coefficients.

## Uniform coefficient majorant for the Section 15 input to Proposition 14.1

For every real X and purely imaginary beta, the actual cutoff kernel has
norm at most 1. If its support is nonempty, n>=1 and n<X imply X>1, so the
logarithmic weight lies in [0,1]; the complex-power phase has norm 1.
This argument does not require an extra X>1 assumption.

Set

    C = (1+norm(iota2)) * (norm(iota3)+norm(iota4)).

The package proves C>0, then

    norm(b0(n)) <= C tau_2(n),
    norm(bpsi(n)) <= C tau_2(n),
    norm(lemma152Kappa(actualBeta)(n)) <= tau_3(n),
    norm((lemma152Kappa(actualBeta)*bPsiArithmetic chi)(n)) <= C tau_5(n).

The last theorem is b_actual_ratio_coefficient_tau_five. The same C is
independent of D,c,chi,n. This is the correct coefficient-side input to the
arbitrary-kappa-star Proposition 14.1 target. It does not assume or prove that
target. No pending Proposition71CoefficientEnergy or Proposition14 module is
imported. The elementary convolution majorant is proved locally.

The B*G*N*N product mentioned in the assignment belongs to Section 17,
whereas Proposition 14.1's short a-star is the separate g*(P4/n) polynomial.
No Section 17 product-support claim is needed or included here. In particular
this package does not substitute a B-support bound for P14's short-a-star bound.

## Does the basis repair change the finite-model coefficients?

It changes the arithmetic coefficient passed to the psi-basis convolution:
that input must be bpsi=chi b0. It also changes the b operand in the repaired
Lemma 15.1 rough-domain arithmetic sum. It does not change the original B,
its kernels, its cutoffs, or its four iota factors. This is certified by
b_four_source_coefficients_unchanged, whose coefficients are exactly

    conjugate(iota3), conjugate(iota4),
    iota2 conjugate(iota3), iota2 conjugate(iota4).

b_repaired_rough_sum invokes, rather than reproves, the existing
lemma151_psi_basis_rough_cancellation. It proves the exact full arithmetic-sum
identity with chi(n1) extracted and the original rho-star and beta_j retained.
Thus a finite model already computed from U*V is unchanged by this basis
repair alone. A formula that fed b0 into a psi-basis convolution is not
justified by the source product and must have its operand repaired.

This conclusion does not validate any separately contested tail phase,
Appendix B cutoff, limiting residue replacement, contour estimate, rough
collision estimate, or final leading asymptotic. The existing literal
Lemma151OriginalTarget is not silently relabeled or marked complete.

## Central validation

The six modules were installed with package-local import qualification only and freshly compiled sequentially. All 234 existing dependency sources and compiled inputs match the frozen package. All 87 public declarations, including named source-object regressions, have only the standard axioms. The whole-project 5337-job build passes. The strict audit remains 413 candidates, with no new candidate. The semantic review checked the literal H finite sums, exact beta and T-corrected support, actual LFunction-to-LSeries bridge, direct ramified-index identities and the uniform coefficient constant. No original numbered target is newly counted complete.
