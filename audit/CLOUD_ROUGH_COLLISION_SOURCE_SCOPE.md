# Lemma 15.1: genuine rough-collision bound and smooth/rough splitting

## Closed result

Write L=log D, P=exp(L^9), alpha=pi/L^9, and let C be the existing actual source constant

    C=(1+|iota2|)(|iota3|+|iota4|)=bCoefficientConstant.

For every positive D, positive integer X, actual beta_j=lemma83PaperBeta D c j,
and every pair of natural shifts l1,l2, the package proves

    | sum_{a,b in R(D,X)} U(l1 a)V(l2 b)rho_j(ab)/(ab)
      - (sum_{a in R(D,X)} U(l1 a)rho_j(a)/a)
        (sum_{b in R(D,X)} V(l2 b)rho_j(b)/b) |
      <= 16 C H_X^4 / D^4,

where R(D,X)={1<=n<=X : gcd(n,Q)=1}, Q=product of primes q<D^4,
H_X is the actual harmonic number, and U,V are the unchanged original
lemma151First and lemma151Second. This is a proved inequality between genuine
finite arithmetic sums, not an error hypothesis or a redefinition of the target.

If X<=P and L>=1, the same error is bounded by

    E(D)=256 C L^36 / D^4.

The package proves the fully explicit normalized bound

    E(D)/alpha <= (256 C 45!/pi)/D^3

and proves E=o(alpha) in Lean. No logarithmic factor, n1-dependent constant,
c-dependent constant, or unspecified asymptotic premise is absorbed here.
The coarse but explicit factorial constant comes directly from
L^45/45! <= exp(L)=D. It is independent of all source parameters.

## Arithmetic attachments now closed

1. The actual rho=(zeta)*(mu times n^beta) is multiplicative for coprime arguments.
2. Without coprimality its defect is bounded by 2 tau2(a)tau2(b), using the genuine
   divisor-function submultiplicativity, not a formal multiplicative substitute.
3. A common prime of a Q-rough a and b satisfies q>=D^4. The closed lower
   boundary is preserved because the original Q uses q<D^4 strictly.
4. The actual weighted multiples satisfy
   sum_{1<=a<=X,p|a} tau2(a)/a <= (2/p)H_X^2 for every prime p.
5. A finite common-prime cover and the elementary reciprocal-square tail give
   collision tau-mass <=8 H_X^4/D^4. No prime number theorem is needed.
6. If n1 is in the original N(Q) and n is Q-rough and nonzero, the actual B
   coefficient satisfies the exact divisor decomposition

       b0(n1 n)=sum_{d1 d2=n1} sum_{a b=n} U(d1 a)V(d2 b).

   This uses the existing proved gcd/divisor-pair bijection. It does not assume
   the two rough factors a,b are coprime.
7. Summing the genuine rectangle defects over d1 d2=n1 costs exactly
   tau2(n1). Multiplication by the corrected external chi(n1) costs no further
   factor, and includes ramified n1. Thus the closed finite divisor error is
   at most tau2(n1) E(D), uniformly even beyond the source's n1<T range.

## Literal source and preserved parameters

Official arXiv:2211.02515v1 local TeX and PDF hashes are recorded in the manifest.
Read source locations:

- (2.13): actual beta_j(c') from lemma83PaperBeta, without setting c'=0
- (2.21)-(2.27): P1=P^.504, P2=P^.5 T^-10, P3=P^.498; beta6 and beta7;
  all original iotas
- (12.1)-(12.2): H14 strict n<P^.5 and B=(H14+iota2 H12)H2
- (15.1), (15.5), (15.19)-(15.22): b coefficient basis and original rough sum
- Lemma 15.1, TeX lines 4273-4296: n1 in N(Q), n1<T, external chi(n)
- Appendix B, TeX lines 5245-5344: B.1/B.2 replacement, single kernels,
  literal B.3 and terminal residue

The coefficient basis issue is unchanged: b0 is the source chi-psi coefficient,
while the pre-(15.5) psi coefficient is bpsi=chi*b0. The published source bridge
and rough-domain character cancellation continue to apply. This package does
not reinterpret the literal original Lemma151OriginalTarget.

The source alpha1 remains undefined and no value is assigned. The new o(alpha)
certificate only compares the collision attachment with the separately defined,
actual alpha=pi/log(P); it does not claim alpha1=alpha.

Official TeX and PDF both print P^12 in B.3. The package's regression proves
that this literal region lies beyond kappa1 support. H14's actual strict cutoff
requires a complementary >=sqrt(P) tail, including equality. The endpoint
regression retains this fact. No corrected tail asymptotic is claimed here.
The printed tail phase and the terminal residue phase remain distinct; their
previous local-residue audit remains necessary.

## Exact remaining attachment

This is not a proof of full Lemma 15.1 or its one-kernel asymptotics.
To assemble the original argument one must still:

- Obtain a scalar, uniform rate for replacing rho-star by rho with the actual
  B weights and actual nu convolution. The existing weighted replacement
  theorem is exact but still has its nu-weighted majorant; this package does
  not make that majorant small
- Reindex the full source finite/infinite rough sum into the finite rectangles,
  proving the precise support/cutoff coverage in that reindexing. The pointwise
  smooth/rough B split is proved, but this final summation attachment is not
  asserted by the rectangle theorem
- Prove uniform one-kernel Mellin/contour asymptotics for the actual kernels,
  including c', l1|n1 with n1<T, the exact P2 factor, non-rough exclusion B.2,
  and the >=sqrt(P) boundary of the H14 complement
- Supply the global contour, reciprocal-zeta, Gaussian, and smoothing errors;
  local residues alone do not establish these arithmetic asymptotics
- Budget the external weighted sum over n1 in (15.19)-(15.22). The finite
  divisor count tau2(n1) and chi(n1) are included here, but no external n1
  weights are silently discarded
- Propagate the justified coefficient-basis and tail repairs downstream before
  identifying any repaired global numerical leading coefficient

## Central verification

All six production/regression modules were rebuilt sequentially after import-only relocation, followed by all40 direct public axiom checks. Twelve named source/endpoint regressions are included. The5459-job whole-project build and1619-source guards pass. All244 published project dependency sources and compiled inputs matched the frozen package. Source hashes were checked again after recovery of the interrupted session. The strict audit remains422 heuristic candidates with no new candidate; it is not presented as a clean historical semantic audit.
