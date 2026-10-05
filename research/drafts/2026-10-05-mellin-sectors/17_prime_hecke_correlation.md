# Exact finite prime-Hecke correlation for the periodic determinant weight

Draft research note dated 2026-10-05. Independently source-reviewed only as a finite correlation and constant-term lemma for Grimmelt–Merikoski's averaged determinant interface. Under the coprimality and strict large-level hypotheses below, the complete expression in their equation (10.2) is

    (2 phi(D)/P) sum_p (p-1)|gamma_p|^2.

Every corresponding linear constant-term orbit sum is zero. This supplies a finite correlation input, not an application of the averaged theorem to the actual arithmetic family. No near/middle arithmetic estimate, global balanced-energy saving, final strict gap or Lean certificate follows.

## 1. Hypotheses and exact primary normalization

Let chi be a nonprincipal real Dirichlet character modulo D. Let M,E be positive integers satisfying

    gcd(M,E)=1, gcd(ME,D)=1.

Put q1=ME, q2=D, q=DME and Gamma=Gamma_2(ME,D), where Gamma consists of the determinant-one integral matrices whose upper-right entry is divisible by ME and whose lower-left entry is divisible by D. On integral matrices set

    alpha((a,b;c,d))=1_(M divides a)1_(E divides b) chi(cd),
    T=Gamma\SL2(Z).                                            (1.1)

Let P>10 and let gamma_p be arbitrary complex weights supported on any set of positive primes in [P,2P] satisfying gcd(p,DME)=1. The support may be a strict subset of that interval. No prime-count estimate or nonempty-support assumption is used. For positive bottom-entry scales C0,F0 assume

    M,E > 20P max(C0/F0,F0/C0).                                (1.2)

Both inequalities are strict. They are stronger than the k=1 conditions in [note 14](14_periodic_determinant_mapping.md).

In Grimmelt–Merikoski, Definition 3 and Theorem 10.1, take both auxiliary automorphic characters to be principal: alpha belongs to A(ME,D,1,1). The original chi in (1.1) remains nonprincipal. To check this directly, let lambda=(u,v;w,z) be integral with ME|v, D|w and gcd(det lambda,q)=1. Modulo ME the determinant is uz, and modulo D it is also uz; hence u,z are units at the relevant moduli. Left multiplication preserves the top divisibility indicators and multiplies the bottom character product by chi(z)^2=1. Thus alpha(lambda g)=alpha(g). In particular alpha(-g)=alpha(g), for either parity of chi.

For a prime p, the primary column-primitive set is

    M_(2,1,p)(Z)={ (a,b;c,d) integral : ad-bc=p,
                   gcd(a,c,p)=gcd(b,d,p)=1 },
    T_(1,p)=SL2(Z)\M_(2,1,p)(Z).

For sigma_j in T_(1,p_j), use the primary correlation, including its conjugation,

    w(sigma,sigma1,sigma2)
      =sum_(tau in T) alpha(tau sigma sigma1)
                         conjugate(alpha(tau sigma2)).          (1.3)

Write g=(g11,g12;g21,g22) and

    N(g)=|g11|+|g12| C0/F0+|g21| F0/C0+|g22|.

With the theorem's K=P, its exact left-hand side in (10.2) is

    Q=(1/P) sum_(p1,p2) |gamma_p1 gamma_p2|
          sum_(det g=p1/p2, N(g)<=10)
            | sum_(sigma_j in T_(1,p_j),
                   sigma2 g sigma1^(-1)=sigma in SL2(Z))
                   w(sigma,sigma1,sigma2) |.                   (1.4)

The g sum contributes only when such an integral representative relation exists. In that case g is rational with entries in p2^(-1)Z, so no continuous summation is intended. The absolute value in (1.4) is outside the representative sum. It is not replaced by a sum of absolute values during the proof.

The primary reference is [Grimmelt–Merikoski, arXiv:2404.08502v2](https://arxiv.org/pdf/2404.08502v2), Definition 3 and Theorem 10.1 on PDF pages 45–46, and the projective-row description (10.4) on page 47. Its third scale is denoted D there; here that scale is F0, while D always denotes the character modulus.

## 2. The primitive-column representative set has p-1 elements

The integer gcd of a determinant-p matrix's first column divides p. Primitivity modulo p excludes gcd p, so that column has integer gcd one. A determinant-one integral row operation sends it to (1,0), yielding a matrix (1,b;0,p). Further row operations fixing the first column reduce b modulo p. The second-column condition excludes b=0 modulo p.

Conversely every (1,b;0,p) with 1<=b<=p-1 has determinant p and both columns primitive modulo p. Two such representatives are equivalent under determinant-one integral row operations only when their upper-right entries agree modulo p. Hence

    sigma_(p,b)=(1,b;0,p), 1<=b<=p-1                         (2.1)

is an exact representative set. The p+1 representatives of the unrestricted prime Hecke correspondence are not the set in (1.4).

## 3. Top-row support forces every contributing g to be diagonal

Suppose sigma2 g sigma1^(-1)=sigma is integral and unimodular. Then

    g=sigma2^(-1) sigma sigma1,
    g_ij in p2^(-1)Z, det g=p1/p2.                            (3.1)

If a summand in (1.3) is nonzero, put B=tau sigma2 and write its top row as (a,b). Its determinant is p2. The weight requires M|a and E|b. Since gcd(p2,ME)=1, the determinant identity makes b a unit modulo M and a a unit modulo E.

The first matrix in (1.3) is B g. Requiring the same top-row divisibilities there, and clearing the permitted denominator p2, gives

    M | p2 g21, E | p2 g12.                                  (3.2)

For example, modulo M the cleared first entry is a(p2 g11)+b(p2 g21), whose first term is zero and whose second coefficient b is a unit. Thus (3.2) is ordinary divisibility of integers; no divisibility assertion is made directly about an unspecified rational entry.

From N(g)<=10 and p2<=2P,

    |p2 g21|<=20P C0/F0,
    |p2 g12|<=20P F0/C0.

The strict inequalities (1.2) and (3.2) imply g21=g12=0. Therefore every off-diagonal g has each correlation in its representative sum equal to zero. This step requires no cancellation between representatives.

## 4. Diagonal classification and absence of off-prime terms

Write a remaining diagonal as

    g=diag(u/p2,v/p2), u,v integers, uv=p1 p2.                 (4.1)

Its determinant is positive, so u and v have the same sign. The extreme positive divisor pairs (1,p1p2) and (p1p2,1), with either common sign, have a diagonal entry of absolute size p1>10 and fail N(g)<=10.

If p1 and p2 are distinct, the only remaining possibilities are

    g=+/-diag(p1/p2,1), or g=+/-diag(1,p1/p2).

For the first type, sigma2 g sigma1^(-1) has nonintegral diagonal entries p1/p2 and p2/p1, up to the common sign. For the second type, it is, up to that sign,

    (1, b2/p2-b1/p1; 0,1).

Integrality forces b2/p2-b1/p1 to be an integer. Both fractions lie strictly between zero and one, so their difference must be zero. Then p2 b1=p1 b2; distinct primality forces p1|b1, contrary to 1<=b1<p1. Consequently no representative pair survives for p1!=p2.

If p1=p2=p, (4.1) leaves only g=I and g=-I. In either case integrality of sigma2 g sigma1^(-1) forces b1=b2, since the upper-right entry is, up to sign, (b2-b1)/p and |b2-b1|<p. For each sign there are exactly p-1 representative pairs, with sigma=+I or -I respectively. Both signs satisfy N(g)=2<=10. The original matrix sum counts I and -I separately.

## 5. Exact transformed projective orbit sums

Since gcd(ME,D)=1, the primary projective parametrization gives

    T <-> P1_(ME) x P1_D,

with the top row supplying the first coordinate and the bottom row the second. These projective coordinates are independent. In particular the top row is not also fixed modulo D.

Right multiplication by sigma_(p,b) is invertible modulo ME and D, because gcd(p,DME)=1. It therefore permutes each projective coordinate. The top support M|a and E|b selects exactly one direction in P1_(ME): [0:1] at prime powers dividing M and [1:0] at those dividing E. This uses gcd(M,E)=1.

The bottom character is nonzero exactly when both bottom coordinates c,d are units modulo D. Such directions are uniquely [r:1], with r in (Z/DZ)^*. Since chi is real, multiplication by the unit d changes chi(cd) by chi(d)^2=1. Consequently, for every representative sigma_(p,b),

    sum_(tau in T) alpha(tau sigma_(p,b))
       =sum_(r in (Z/DZ)^*) chi(r)=0,                         (5.1)
    sum_(tau in T) |alpha(tau sigma_(p,b))|^2=phi(D).          (5.2)

The zero in (5.1) uses nonprincipality of chi. This argument does not require D to be squarefree or odd, and retains zero values on nonunit bottom entries.

By alpha(-g)=alpha(g), each surviving correlation from Section 4 is

    w(+/-I,sigma_(p,b),sigma_(p,b))=phi(D).                  (5.3)

Thus the representative sum for each surviving g=+I or -I is the nonnegative number (p-1)phi(D). The outer absolute values in (1.4) do not change these sums.

## 6. Complete quadratic correlation and zero constant term

Substituting Sections 3–5 into the complete primary expression gives the exact identity

    Q=(2 phi(D)/P) sum_p (p-1)|gamma_p|^2
      <=4 phi(D) sum_p |gamma_p|^2.                           (6.1)

There are no off-prime terms and no omitted factor of two. This holds for arbitrary complex gamma_p on the stated support; it is not a prime-sign or random-correlation heuristic. For nonzero gamma the upper bound permits K_+=4phi(D)||gamma||_2^2 in the finite correlation hypothesis, with no need to invoke its optional Z^O(eta) loss. For zero gamma the expression is zero and any positive K_+ suffices.

The same representative decomposition gives, for each supported prime p,

    sum_(tau in Gamma\M_(2,1,p)(Z)) alpha(tau)
      =sum_(b=1)^(p-1) sum_(tau in T) alpha(tau sigma_(p,b))
      =0.                                                     (6.2)

This is the orbit factor in the theorem's linear constant term. It vanishes before summing over p or any determinant parameter h. It does not assert that a determinant count, its spectral error, or the actual family is zero.

## 7. Remaining averaged-application obligations

The finite calculation above does not apply Theorem 10.1 to the full actual near aggregate. Such an application still has to establish, at the actual weights and ranges:

- The determinant split Delta=p h, the support of beta_h and gamma_p, and gcd(h,pDME)=1, together with exact treatment of all excluded gcd sectors
- Both column-primitivity restrictions in M_(2,h,p)(Z), including every complementary sector; the k=1 argument does not establish them for k=p
- A common smooth function of the normalized matrix entries a/sqrt(|hp|), c/sqrt(|hp|), d/sqrt(|hp|), or a rigorously paid decomposition of the actual h,p-dependent weights
- All carrier, gamma-phase, Mellin-height, derivative and Z costs, the theorem's scale conditions and determinant-height condition, and the norms of the actual coefficient sequences
- Collective summation over the outer plain factors and all remaining labels, preserving both congruence signs, sharp-boundary remainders and the restricted even-principal subtraction

The strong level condition (1.2) is compatible with natural balanced scales M,E of order P t_c when C0/F0 stays bounded above and below and t_c grows. That scale observation neither proves that these cells carry mass nor justifies their attachment or summation.

The bounded-middle arithmetic upper bound in [notes 15–16](16_transformed_high_tail.md), the weighted cumulative remainder in [note 11](11_shifted_correlation_carrier_interface.md), the global balanced energy and final strict gap all remain unproved. Equation (6.1) is a finite interface lemma only; it does not imply a saving for any of those quantities.

## Sources and validation scope

The only external reference needed here is the versioned [Grimmelt–Merikoski primary paper](https://arxiv.org/pdf/2404.08502v2), with the locators stated in Section 1. [Note 14](14_periodic_determinant_mapping.md) provides the predecessor determinant mapping and k=1 comparison at its existing bounded scope. Exact candidate, independent source-review, acceptance and primary-file identities are recorded as hashes in [SOURCE_PINS.json](SOURCE_PINS.json). No external paper, full-text extraction or raw review is redistributed.

[Finite diagnostics](diagnostics/README.md) enumerate signed rational diagonal representative cases, transformed projective orbits at odd, even and nonsquarefree moduli, and the exact quadratic normalization. They support the written finite argument without certifying the external analytic theorem, an actual averaged application, an asymptotic saving or a Lean theorem.
