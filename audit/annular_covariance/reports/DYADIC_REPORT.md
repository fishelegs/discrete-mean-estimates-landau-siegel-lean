# Annular root-phase completion at the original parameter scales

2026-10-03. Source-level bounded repair research. No repository edits, Lean execution, or change of the exceptional-zero hypothesis or final exponents.

## Result and boundary

There is a completed good-family-to-full-family C1 interface for an honestly restricted class of bounded annular polynomials. Its normalized error is O(a^−1 L^−14), hence o(L^−8). The right contribution permits truncating κ at P^.999 and has error O(M L^−200). The left contribution does **not** permit that truncation: it needs P^1.003, a second moment of κ, and the actual small-shift Euler estimate. Its error is O(M L^−14).

The same method completes T1[A,J] against the original target J1, using cutoff P^1.005 on both sides and error O(a^−1 L^−14). The left T1 kernel contains three Gauss sums; it is retained explicitly below. All kernels retain the exact inherited gamma branch and finite source-window integrals. No gamma freezing, stationary-phase approximation, or assumption that roots and zeros are independent is used.

These are arithmetic representations, **not evaluated asymptotics or favorable-sign results**. The new right congruence, left Kloosterman, and target kernels still have to be evaluated, jointly with every Gram/target entry, before any gain can be claimed. Low-support portions of the original H1/H2 are outside this changed candidate class and have not been silently dropped from a statement about those original polynomials.

## 1. Quantifiers and admissible changed coefficient class

Use the exact source parameters

    L = log D, P = exp(L^9), alpha = pi/log P,
    T0 = 2 pi L^519, H = L^405, W = L^400,
    s0 = 1/2 + i T0,
    omega(s) = sqrt(pi)/W exp((s-s0)^2/(4W^2)),
    M = sum_{P<p<P(1+L^-68)} p asymp P^2 L^-77.

The letter M here is the family normalization, not a polynomial support parameter. Let U=P^.503 and V=P^.499. For any fixed coefficient bound C and fixed finite number of trial polynomials, choose sequences common to the whole p,psi family such that

    |a(m)| <= C, supp(a) subset [U,2U],
    |b(n)| <= C, supp(b) subset [V,2V].

They may depend on D, primitive real chi, and the prescribed source shifts, but not on p or psi. Endpoints mean the integers in those real intervals. Set

    A(s,psi)=sum a(m)psi(m)m^-s,
    B(s,psi)=sum b(n)psi(n)n^-s.

Finite fixed linear combinations of r_psi A + lambda Z(s,chi psi) conjugate(B) on the actual zeros, with fixed bounded lambda, are legal changed candidates. Since 2P^.503<P^.504<PT^-2 for sufficiently large D, all short polynomials remain in the original admissible coefficient/support range. Their cubes have lengths at most 8P^1.509 and 8P^1.497, both below P^2. The finite size and coefficient bound enter only the implied constants.

For the target interface, allow any |j(n)|<=C supported in [P^.5,P^.504], and put J(s,psi)=sum j(n)psi(n)n^-s. This includes the original J1 from (2.28)–(2.29), with j(n)=chi(n) times the triangular cutoff. Its cube has length P^1.512<P^2.

Assume the original (A), L(1,chi)<L^-2022, and the original definition of Psi1, zero region, and c*. All assertions hold uniformly for every primitive real chi of conductor D, both parities of chi and psi, and all sufficiently large D. There is no positive-discriminant or squarefree-conductor restriction. The sufficiently large threshold can depend on C, the finite trial count, and the source's fixed gap constant c', but not on chi or the coefficient values. The source lower bound a >> 1 is retained, as is the final requested exponent 2024.

Write mu for the source positive zero measure c*(rho,psi)omega(rho)/(aM). Define

    C1[A,B] = integral r_psi Z(rho,chi psi)^-1 A(rho,psi) B(rho,psi) dmu,
    T1[A,J] = integral r_psi A(rho,psi) conjugate(J(rho,psi)) dmu.

## 2. Exact branch and integrands

For primitive theta of conductor q and parity j define

    epsilon_theta = tau(theta)/(i^j sqrt(q)),
    h_j(s,q) = (q/pi)^(1/2-s) Gamma((1-s+j)/2)/Gamma((s+j)/2),
    Z(s,theta) = epsilon_theta h_j(s,q).

Let a0 be the parity of psi, c the parity of chi, b0=a0+c modulo 2, and

    r_psi = epsilon_psi epsilon_{chi psi},
    g_{a0}(s,p) = h_{a0}(s,p) h_{b0}(s,Dp).

The three original shifts beta_j are purely imaginary and satisfy exactly beta3=beta1+beta2. For all sufficiently large D, |beta_j|<=4pi/log P. Define the exact inherited branch

    B_beta(s,p) = product_{j=1}^3 Y(s+beta_j,psi)/Y(s,psi)^3.

This is independent of the sign choice of Y and of the root number; it depends on psi only through p and parity. With E_beta=product h_{a0}(s+beta_j,p)/h_{a0}(s,p), one has B_beta^2=E_beta^-1. The exact residue integrand is

    c_tilde(s,psi) = -i B_beta(s,p) Z(s,psi)^-1 K_psi(s),
    K_psi(s) = product L(s+beta_j,psi)/L(s,psi).

Its residue at each original simple zero is the original c*, exactly. B_beta is not assigned a principal square-root value. Its definition is valid throughout the high upper-half-plane rectangles used below, including their far real sides; all shifted gamma poles and zeros are off those rectangles. There is no full-vertical-line continuation in this report.

For C1 the exact right integrand, with omega suppressed, is

    -i B_beta g_{a0}^-1 K_psi A(s,psi) B(s,psi).                 (2.1)

The root numbers cancel, since r_psi/(epsilon_psi epsilon_{chi psi})=1. Define

    K_psi^-(1-s) = product L(1-s-beta_j,bar(psi))/L(1-s,bar(psi)).

The exact functional equation gives K_psi=Z(s,psi)^2 E_beta K_psi^-. Also

    Z(s,psi)/Z(s,chi psi)
      = tau(chi) chi(p) D^(s-1) bar(psi(D)) E_{chi,a0}(s),

where E_{chi,a0}=1 if c=0, E_{chi,0}=-i tan(pi s/2) if c=1,a0=0, and E_{chi,1}=i cot(pi s/2) if c=1,a0=1. Thus the exact left integrand is

    -i tau(chi) chi(p) D^(s-1) E_{chi,a0}(s) B_beta(s,p)^-1
       r_psi bar(psi(D)) K_psi^-(1-s) A(s,psi) B(s,psi).        (2.2)

No p or D factor is suppressed. In particular |tau(chi)|=sqrt(D), so |tau(chi)D^(s-1)|=1 on the critical line. There |E_{chi,a0}|=1 as well.

The absolutely convergent expansions are

    K_psi(s)=sum kappa(ell)psi(ell)ell^-s                 for Re(s)>1,
    K_psi^-(1-s)=sum bar(kappa(ell))bar(psi(ell))ell^(s-1) for Re(s)<0.

## 3. The actual small-shift Euler moments

This is the decisive improvement over a d4-only bound. For each prime q, put x=q^-beta1=e^(i theta1), y=q^-beta2=e^(i theta2). Then q^-beta3=xy and

    kappa(q)=x+y+xy-1,
    |kappa(q)|^2 = 4 + 4 sin(theta1) sin(theta2) <= 8.          (3.1)

The upper bound 8 is sharp among arbitrary unit x,y. More importantly, the actual prescribed shifts imply

    |kappa(q)|^2 <= 4 + C0 (log q/log P)^2.                   (3.2)

For prime powers, the generating function is

    sum_{k>=0} kappa(q^k) z^k
       = (1-z)/((1-xz)(1-yz)(1-xyz)),

so |kappa(q^k)|<=binom(k+2,2)+binom(k+1,2)=(k+1)^2 for k>=1. Consequently, uniformly over q>=2,

    sum_{k>=0}|kappa(q^k)|^2/q^k
       <= (1-1/q)^-4 exp(C0 (log q/log P)^2/q + C1/q^2).

All terms with k>=2 are O(q^-2), with an absolute constant: the bound follows by summing (k+1)^4 2^{-(k-2)}. For X<=P^K with fixed K, multiplicativity and positivity give the finite-prime majorant

    sum_{n<=X}|kappa(n)|^2/n
      <= product_{q<=X} sum_{k>=0}|kappa(q^k)|^2/q^k
      <<_K (log(2X))^4.                                     (3.3)

Here the additional exponential factor is bounded because

    sum_{q<=X}(log q)^2/q << (log(2X))^2.

This is a sum over **primes**, proved by partial summation from Chebyshev's theta(x)<<x. Replacing it by a sum over all integers would be insufficient. The remaining factor uses the standard Mertens upper bound product_{q<=X}(1-1/q)^-1 << log(2X). Thus (3.3) has a constant uniform in D and the actual perturbed shifts. No unjustified infinite Euler product at sigma=1 is used.

For a truncated kappa polynomial K_R, the coefficients of K_R^2 need not be bounded by |kappa*kappa|, because truncation can remove cancellation. Use instead the multiplicative positive majorant eta=|kappa|*|kappa|. At a prime eta(q)=2|kappa(q)|, so its local squared coefficient is

    eta(q)^2 = 4|kappa(q)|^2 <= 16+C2(log q/log P)^2.

The higher prime-power coefficients are bounded by d8(q^k). The same finite-prime argument proves

    sum_{n<=X} eta(n)^2/n <<_K (log(2X))^16.                  (3.4)

This correctly bounds the squared coefficients of every finite K_R^2 with R^2<=X. In source L powers, (3.3) costs L^36 and (3.4) costs L^144. For any bounded short sequence of length at most P^.504, the ordinary divisor bound gives the sixth-moment coefficient cost L^81.

## 4. Rigorous tail moves in the finite source window

Let J(sigma) be the upward segment from sigma+i(T0-H) to sigma+i(T0+H). Put S=L^9. Throughout |sigma-1/2|<=S and |t-T0|<=H+1, uniform complex Stirling gives, for j=0,1 and q=p or Dp,

    |h_j(s,q)| asymp (q t/(2pi))^(1/2-sigma),
    |B_beta(s,p)| + |B_beta(s,p)^-1| <= C,
    |E_{chi,a0}(s)| <= C.                                   (4.1)

The constants are absolute once D is sufficiently large. For example the log-modulus error in the first estimate is O((1+S)^2/t), which tends to zero. For B_beta, integrate the logarithmic derivative of h along each imaginary beta_j. The real main term -log(qt/(2pi)) contributes only an imaginary quantity; the remaining real part is O(|beta_j|(1+S)/t). This proves the bound for the inherited branch and its reciprocal without selecting a different square root. The tan/cot estimates are exponentially close to 1 throughout the high rectangle. On sigma=1/2 each h_j and E_{chi,a0} has modulus exactly one.

The normalized vertical Gaussian mass is bounded by a constant for these real shifts. On every horizontal side t=T0±H+O(alpha), its modulus is at most

    C W^-1 exp(-L^10/4+o(1)).                                (4.2)

### 4.1 C1 right tail

Set R=P^.999, and split off ell>=R only on J(3/2), where the series is absolutely convergent. For sigma>=3/2,

    sum_{ell>=R}|kappa(ell)|ell^-sigma << R^(1-sigma)(log R)^3,
    |A(s)B(s)| << C^2 (UV)^(1-sigma).

The second estimate uses the lower annular endpoints; this is where low supports cannot be silently included. Put Q(t)=Dp^2(t/(2pi))^2. By (4.1), the absolute tail integrand, excluding omega, is bounded by

    C^2 (log R)^3 Q(t)^(1/2) [Q(t)/(RUV)]^(sigma-1).          (4.3)

Since UV=P^1.002, uniformly in the original prime/height windows,

    Q(t)/(RUV) <= D L^1038 P^-.001 (1+o(1)) <= P^-.0005.    (4.4)

Move this tail contour right to J(1/2+S). The new vertical side contributes exp(-cL^18); the horizontal sides contribute exp(-cL^10), since (4.3) decreases with sigma and at its starting point is only exp(O(L^9)). This is a contour bound for the oscillatory Mellin integral itself; no localization heuristic or absolute bound at sigma=1/2 substitutes for it. It is uniform for each primitive character, so summing all characters still gives exp(-c'L^10).

### 4.2 C1 left tail

Set Rminus=P^1.003. Split ell>=Rminus on J(-1/2) in (2.2), where the dual expansion is absolutely convergent. For sigma<=-1/2,

    sum_{ell>=Rminus}|kappa(ell)|ell^(sigma-1)
       << Rminus^sigma(log Rminus)^3,
    |A(s)B(s)| << C^2 UV(4UV)^-sigma.

Using the exact |tau(chi)|D^(sigma-1)=D^(sigma-1/2), the tail integrand is bounded by

    C^2 UV D^-1/2 (log Rminus)^3 [D Rminus/(4UV)]^sigma.      (4.5)

The bracket is at least P^.0005 for all sufficiently large D. Move left to J(1/2-S). The vertical side is exp(-cL^18), and the horizontal sides are exp(-cL^10), exactly as above. Both parities are covered by the bounded exact E factor.

The cutoff P^.999 is not valid for this left tail. Its resonance scale is UV/D=P^1.002-o(1), and the bracket in (4.5) with P^.999 would be small, causing growth rather than decay on the left. The completed result uses distinct right and left truncations.

## 5. Exceptional-family completion

Write K_R for the finite right kappa polynomial and Kminus_Rminus for its finite dual counterpart. Shift only these finite expressions to J(1/2), after splitting the tails in their absolutely convergent half-planes. Their multipliers are analytic in the intervening high rectangles. The horizontal bounds are exp(O(L^9)) times (4.2). The reciprocal L-functions of bad characters are never shifted through their zeros.

On J(1/2), the right gamma multiplier has bounded modulus, and the exact large sieve (source Lemma 3.3), (3.4), and the short sixth moments give

    sum_Psi |K_R|^4 << P^2 L^144,       since R^2=P^1.998<P^2,
    sum_Psi |A|^6 << C^6 P^2 L^81,
    sum_Psi |B|^6 << C^6 P^2 L^81.

Holder with exponents 4,6,6,12/5 and |Psi2|<<M L^-739 therefore gives

    sum_Psi2 |K_R A B|
      << C^2 (P^2 L^144)^(1/4)(P^2 L^81)^(1/6)
                  (P^2 L^81)^(1/6)(M L^-739)^(5/12)
      << C^2 M L^-200,                                     (5.1)

because

    144/4 + 81/6 + 81/6 - 739*5/12 + 77*7/12 = -200.

For the left finite polynomial, its length P^1.003 is below P^2, so (3.3) gives the second moment P^2 L^36. The exact scalar/root/gamma multiplier on the critical line is bounded, with no D or p loss. Holder with 2,6,6,6 gives

    sum_Psi2 |Kminus_Rminus A B|
      << C^2 (P^2 L^36)^(1/2)(P^2 L^81)^(1/6)
                  (P^2 L^81)^(1/6)(M L^-739)^(1/6)
      << C^2 M L^-14,                                      (5.2)

because

    36/2 + 81/6 + 81/6 - 739/6 + 77*5/6 = -14.

Integrating against the bounded Gaussian mass preserves these bounds. Restore each tail on its original safe side. This establishes the right and left family-completion errors with the stated rates. Neither uses the unrelated H(GA,FB) L^-45 estimate.

## 6. Attaching the original zero mean and controlling crossed regions

Start with the source's good-character residue rectangle at sigma=1/2±alpha and endpoints T0±H+O(alpha), chosen a fixed multiple of alpha away from its zeros. The test factor r Z_chipsi^-1 AB is analytic there. The residues are exactly those defining C1, because c_tilde has the original c* residues. The original good-zero geometry permits moving the right side to sigma=3/2 and the left side to sigma=-1/2 in this finite window. No nontrivial denominator zeros occur in those crossed regions. Trivial zeros and gamma poles are on the real axis and lie outside the window. The transformed left denominator has the same reflected good-zero geometry.

For completeness, the necessary horizontal reciprocal-L bounds can be made much better than exp(O(L^18)). In a bounded sigma strip, the local logarithmic derivative expansion has O(log(pT0))=O(L^9) nearby zeros and an O(log(pT0)) regular part. Integrating each zero term from sigma=3/2 to a point at distance at least c alpha from the zero gives O(log(1/alpha)) in log-modulus. Thus

    |1/L(s,psi)| <= exp(O(L^9 log L))

on the needed good-character boundaries; numerator L-functions satisfy the usual exp(O(L^9)) convexity bound there. On the left one can use the functional equation and the same argument for the dual. The original near-central horizontal edges can also be bounded directly by source Lemma 5.9. These estimates, the finite polynomial bounds, and (4.2) make all good-character horizontal and short endpoint-adjustment contributions exp(-cL^10), even after summing the family. In particular an inadequately estimated exp(O(L^18)) reciprocal-L factor is not hidden under the Gaussian.

Both vertical segments are oriented upward, so the residue theorem is **right minus left**. The operations are now legal in this order:

1. Good-family residue rectangle and deformation to the two safe half-planes.
2. On each safe line, split the appropriate convergent kappa series at its own cutoff.
3. Move the tail outward and pay the uniform negligible tail/horizontal costs.
4. Move only the finite polynomial inward, pay (5.1) or (5.2) for Psi2, and return it.
5. Restore the convergent tail, expand the safe-line series, and perform finite primitive-character averaging.

This proves the attachment rather than merely asserting an identity for a formally completed family.

## 7. Explicit completed C1 arithmetic interface

Write e_p(x)=exp(2pi i x/p), and let all modular inverses below be taken only when their arguments are prime to p. Define finite exact kernels

    Vplus_{a0,p}(x) = (2pi i)^-1 integral_{J(3/2)}
         B_beta(s,p) g_{a0}(s,p)^-1 x^-s omega(s) ds,

    Vminus_{a0,p}(x) = (2pi i)^-1 integral_{J(-1/2)}
         E_{chi,a0}(s) B_beta(s,p)^-1 x^-s omega(s) ds.

For units v modulo p put

    O_{a0,p}(v) = (p-1)/2 [1_{v=1} + (-1)^a0 1_{v=-1}] - 1_{a0=0},
    c_{a0,p} = (-1)^(c*a0+a0) chi(p) epsilon_chi,
    Kl2(w;p) = p^-1/2 sum_{u mod p, u!=0} e_p(u+w/u),
    Rone_{a0,p}(v) = c_{a0,p}(p-1)/(2sqrt(p))
         [Kl2((Dv)^-1;p)+(-1)^a0 Kl2(-(Dv)^-1;p)]
         - 1_{a0=0} c_{a0,p}/p.

These are exact **unnormalized** fixed-parity primitive sums:

    O_{a0,p}(v)=sum_primitive,parity a0 psi(v),
    Rone_{a0,p}(v)=sum_primitive,parity a0 r_psi psi(v).

Set

    R_C(A,B) = -i sum_{p,a0} sum_{ell,m,n: p does not divide ell*m*n}
         kappa(ell) a(m)b(n) O_{a0,p}(ell*m*n)
         Vplus_{a0,p}(ell*m*n),

    L_C(A,B) = -i tau(chi) sum_{p,a0} chi(p)
         sum_{ell,m,n: p does not divide ell*m*n}
         bar(kappa(ell)) a(m)b(n)/(D*ell)
         Rone_{a0,p}(m*n/(D*ell)) Vminus_{a0,p}(m*n/(D*ell)).

The arguments of Vminus are positive real ratios, whereas the same notation inside Rone means the associated modular unit. All m,n sums are finite and the ell sums are absolutely convergent on their defining lines. The outside chi(p) and D factors remain explicit. In the left Kloosterman sum (Dv)^-1=ell/(mn), as required. One may cancel chi(p) against its occurrence in c_{a0,p} only after multiplication; it has not been discarded from either factor.

The completed theorem is

    C1[A,B] = (R_C(A,B)-L_C(A,B))/(aM) + O_C(a^-1 L^-14).     (7.1)

All errors are uniform across the fixed finite trial class. The separately stronger right completion error is O_C(a^-1 L^-200); all contour/tail errors are exponentially smaller than either rate.

## 8. Target T1: exact transforms, tails, completion, and root kernels

The analytic test for T1 is r A(s,psi) Jbar(1-s,bar(psi)), where Jbar has conjugated coefficients. On the right and left safe lines its exact integrands, before omega, respectively are

    -i B_beta epsilon_{chi psi} h_{a0}(s,p)^-1
          K_psi(s) A(s,psi) Jbar(1-s,bar(psi)),              (8.1)

    -i B_beta^-1 r_psi epsilon_psi h_{a0}(s,p)
          K_psi^-(1-s) A(s,psi) Jbar(1-s,bar(psi)).          (8.2)

The single-gamma conductor here is p; the D dependence stays in the unit root factors. On sigma=1/2 every gamma/root scalar in (8.1)–(8.2), other than the bounded B factor, has modulus one.

Take targetCutoff=P^1.005 on **both** sides. Put N0=P^.5, N1=P^.504 and q1(t)=pt/(2pi). On the right, for sigma>=3/2,

    tail << C^2 targetCutoff U q1(t)^-1/2 (log targetCutoff)^3
                    [q1(t)N1/(targetCutoff U)]^sigma.

The bracket is at most P^-.003 for large D: the unsimplified exponent gap is 1+.504-1.005-.503=-.004, with t0=P^o(1). On the left, for sigma<=-1/2, the bound

    sum_{n>=N0} n^(sigma-1) << N0^sigma

gives

    tail << C^2 U q1(t)^1/2 (log targetCutoff)^3
                    [targetCutoff N0/(2U q1(t))]^sigma.

This bracket is at least P^.001 for large D: the unsimplified exponent gap is 1.005+.5-.503-1=.002. The same outward contour moves pay exp(-cL^10) errors. The cutoff P^1.003 would not have sufficient slack for the dual-left pt0 factor; it is deliberately not used.

Both finite kappa polynomials have length below P^2 and use (3.3). A and J use sixth moments. The same 2,6,6,6 Holder calculation as (5.2) proves error O_C(M L^-14) on each side. The good-character residue/deformation proof of Section 6 applies to this analytic test as well. Thus this is an attached actual target mean, not only a support heuristic.

To specify every arithmetic factor, put d_{a0,p}=(-1)^(c*a0)chi(p)epsilon_chi and define

    G1_{a0,p}(v) = d_{a0,p} i^-a0/sqrt(p)
      { (p-1)/2 [e_p((Dv)^-1)+(-1)^a0 e_p(-(Dv)^-1)] + 1_{a0=0} },

    Kl3(w;p) = p^-1 sum_{x,y,z !=0, xyz=w} e_p(x+y+z),
    G3_{a0,p}(v) = c_{a0,p} i^-a0
      { (p-1)/(2sqrt(p)) [Kl3((Dv)^-1;p)+(-1)^a0 Kl3(-(Dv)^-1;p)]
                                      + 1_{a0=0}/p^(3/2) }.

Opening respectively one and three Gauss sums proves exactly

    G1_{a0,p}(v)=sum_primitive,parity a0 epsilon_{chi psi} psi(v),
    G3_{a0,p}(v)=sum_primitive,parity a0 r_psi epsilon_psi psi(v).

Both even-principal corrections are positive in these one/three-Gauss identities. No bound for Kl3 is needed for this interface.

Define

    Uplus_{a0,p}(x)=(2pi i)^-1 integral_{J(3/2)}
         B_beta(s,p) h_{a0}(s,p)^-1 x^-s omega(s) ds,
    Uminus_{a0,p}(x)=(2pi i)^-1 integral_{J(-1/2)}
         B_beta(s,p)^-1 h_{a0}(s,p) x^-s omega(s) ds.

Then, with all sums restricted by p not dividing ell*m*n,

    R_T(A,J)=-i sum_{p,a0,ell,m,n} kappa(ell)a(m)bar(j(n))/n
           G1_{a0,p}(ell*m/n) Uplus_{a0,p}(ell*m/n),
    L_T(A,J)=-i sum_{p,a0,ell,m,n} bar(kappa(ell))a(m)bar(j(n))/(ell*n)
           G3_{a0,p}(m/(ell*n)) Uminus_{a0,p}(m/(ell*n)),

and the completed target theorem is

    T1[A,J]=(R_T(A,J)-L_T(A,J))/(aM)+O_C(a^-1 L^-14).          (8.3)

The allowed J class also contains every A in the annular class for sufficiently large D. Therefore (8.3) covers T1[A,A] and T1[A_i,A_j], as well as the original target J1.

## 9. What this settles, and the stopping condition

For the ordered trial (r A, Z_chipsi conjugate(B)), the diagonal Gram entries are H(A,A), H(B,B), the upper cross entry is C1[A,B], and its target entries against J1 are T1[A,J1] and conjugate(C0[J1,B]). Thus (7.1) and (8.3) provide the two genuinely new attached interfaces. They do not evaluate their arithmetic sums. The old entries also need their actual joint precision; an unquantified printed o(1) does not automatically suffice.

One may also keep the unrooted A. For the ordered three-direction trial (A, Z_chipsi conjugate(B), r A), the diagonal is (H(A,A),H(B,B),H(A,A)), the upper triangular entries are

    C0[A,B], conjugate(T1[A,A]), conjugate(C1[A,B]),

and the target vector against J1 is

    H(A,J1), conjugate(C0[J1,B]), T1[A,J1].

This specifies the complete Gram/target algebra for that finite augmented class; it does not assign a sign or numerical asymptotic to any new entry.

For reference only, the same tail/moment framework can attach C0[J1,B] with second kappa moments and cutoff P^1.005 on both sides: its product support is between P^.999 and 2P^1.003. The root factors have unit modulus and do not change the completion estimate. This observation is not an evaluation of that old target entry.

The changed class excludes all lower blocks of the original broad H1/H2 supports. It is not a theorem that they may be removed without changing the variational problem. For this finite annular class the actual next task is to evaluate the complete Gram matrix and target vector, with the exact kernels or a separately quantified replacement, and show that any proposed residual normalization leaves every total error below the claimed signed margin. If a near-null residual is normalized, O(L^-14) may itself be insufficient. Stop before any favorable gain, contradiction, or final theorem claim unless that computation is completed.

## Sources and checks

Primary source: [the version-pinned external source input](../sources/CITATION.md), arXiv:2211.02515v1; the exact functional equations, (2.6)–(2.15), target (2.28)–(2.29), Proposition 2.1/2.2, Lemma 3.3, Lemma 5.9, and source residue deformation in Lemma 8.1. The source itself is not being treated as validation of its final contradiction.

Prior audited bridge: the [earlier bridge record](../PROVENANCE.md#prior-bridge), SHA256 `1ae639db7a00f45c59af8fa4d6521d7332c7eeff155b85e0c86eedac568b1ff4`, and its [independent review record](../PROVENANCE.md#prior-bridge). The new Euler bounds, annular tail moves, C1/T1 completion rates, and target three-Gauss kernel are proved in this report rather than imported from the H extension.

[the author check script](../scripts/check_annular.py) and [original results](../results/AUTHOR_ORIGINAL.txt) record finite algebraic/regression checks. They do not replace the uniform analytic proof or prove a signed main-term estimate.
