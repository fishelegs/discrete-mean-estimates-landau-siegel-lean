# A smaller arithmetic inverse tail, and the exact actual-energy obstruction

Draft research note dated 2026-10-05. Independently reviewed at source-proof level, with explicit attachment limits; not Lean-certified. This is an arithmetic improvement plus a quantified attachment limit, not a global replacement of the original finite inverse throughout its conductor-power core.

## 1. Results and what is NOT paid

Let chi be the actual primitive real nonprincipal character of conductor D, with either parity. Set

    L=log D, B=log P=L^9, X=D^4, nu=1*chi,
    lambda=L(1,chi), 0<lambda<L^-2022.

The original assumption exponent 2022 is unchanged. Put Q=2sqrt(D)(1+L). For sufficiently large D, every 1<=Y<=P^3 and every Z>=16(Q+1)^2 satisfy

    sum_(Z<n<=Y)nu(n)^2/n
      << L^2 lambda(1+log Y)+L^(5/2)(D/Z)^(1/4).       (1.1)

Empty sums are zero. Consequently, for EVERY FIXED delta>1,

    sum_(D^delta<n<=P^3)nu(n)^2/n <<_delta L^-2011.    (1.2)

On the smaller actual discarded inverse range, its top endpoint is only D^4, so

    sum_(D^delta<d<=D^4)nu(d)^2/d <<_delta L^-2019,
    1<delta<4.                                        (1.3)

Thus delta=3/2 is a concrete smaller arithmetic threshold. These are new source-level deductions from the elementary primitive character-sum bound and the existing nu-square convolution mechanism. They have not been newly Lean-compiled.

For the original finite-G/V4 core with 1<=M<=P^2D^5, let T_delta(M) be the LITERAL tuple part with D^delta<d<=D^4. Its actual positive family/Gaussian energy satisfies

    ||T_delta(M)||_H^2
      <<_delta (P^2+M/W)L^(-1427/2)(log L)^2,
    W=L^400.                                         (1.4)

The exact cross with the retained d<=D^delta part is bounded, without a new reciprocal lemma, by

    |<S_delta(M),T_delta(M)>|
      <<_delta (P^2+M/W)L^(-1323/4)(log L)^2.           (1.5)

Both parities, finite d<=D^4, original V4, prime window, input/output masks, p-unit deletion, principal projection, restricted Gaussian and actual diagonal are retained.

At the FULL retained core M=P^2D^5, (1.4) still contains

    P^2 D^5 L^(-2227/2)(log L)^2,                     (1.6)

and (1.5) still contains P^2D^5L^(-2923/4)(log L)^2. Neither is bounded by P^2 times any fixed logarithmic power. This is a precise obstruction to this ATTACHMENT METHOD, not a lower bound for the actual remainder. The original large-d part and its full-core cross therefore remain explicit; no global replacement of D^4 by D^delta is claimed.

There is a genuine narrower actual consequence: for M<=P^2L^730, the original and reduced-inverse squared core moments differ by o(P^2). For M<=P^2L^1113 their polynomials differ by o(P) in actual family L2, but that stronger range alone does not give an o(P^2) squared-moment identity. Neither statement proves the main moment in those ranges. The sharper cross uses the already-accepted full low-output L^52 bound; Section 7 also gives an independent, more conservative cross estimate from elementary coefficients.

Finally, Section 8 supplies an independent obstruction to a GENERIC weighted bilinear sieve, whenever the original prime window is nonempty. Arbitrary coefficients in a permitted balanced box can resonate with one actual nonprincipal character and have original-V4/Gaussian energy at least cP^2D^(1/4)/W while their two harmonic factor energies are O(1). Thus removing the remaining conductor powers needs an arithmetic property of the actual coefficients; it cannot follow from separability and lengths alone.

## 2. Exact public character-sum input, with its elementary proof

The public source

    ZhangLS/Spec/Lemma32PrimitivePolyaVinogradov.lean

has SHA256 43d2ed2abd9891463aae0a060731ef189c206b8a8771b6985ead58e0f0372d7b. Its theorem lemma32_actual_primitive_polya_vinogradov states, for every integer M and natural N,

    |sum_(M<=n<M+N)chi(n)|<=2sqrt(D)(1+log D)=Q.        (PV)

It is for the actual RealPrimitiveCharacter D, not an unproved Burgess estimate or a squarefree-only conductor. The immediately relevant finite Fourier, Gauss-norm, and kernel-summatory source files are identified by exact source hashes in SOURCE_PINS.json. No compilation or full transitive formal audit is claimed.

The analytic proof needed here is short. Primitive quadratic Fourier inversion gives

    D chi(x)=tau(chi) sum_(a mod D)chi(-a)e(ax/D),
    |tau(chi)|=sqrt(D).

The zero frequency vanishes because chi(0)=0 for D>1. For a!=0, a geometric progression over ANY integer interval has modulus at most 2/|1-e(a/D)|. With a represented by 1,...,D-1, the elementary sine/chord bound gives

    2/|1-e(a/D)|<=D/a+D/(D-a).

Summing these bounds is at most 2D(1+log D). Fourier inversion and |chi(a)|<=1 prove (PV). The primitive Gauss modulus follows from finite Fourier inversion twice (equivalently tau(chi)^2=D chi(-1)); hence both chi parities are covered. These are exactly the identities exposed by the pinned public source, including ramification.

We use the uniform INTERVAL version of (PV), not just initial partial sums. Its gain over the older trivial interval bound is the new arithmetic ingredient in the optimized hyperbola estimate below.

## 3. Optimize the nu summatory hyperbola with Q, not D

For an integer N>=1,

    A(N):=sum_(n<=N)nu(n)=sum_(b<=N)chi(b)floor(N/b).

Choose an integer 1<=U<=N. The short sum differs from N sum_(b<=U)chi(b)/b by at most U, because each floor error has modulus at most one. The long sum can be counted in the other order:

    sum_(U<b<=N)chi(b)floor(N/b)
       =sum_(a<=N/(U+1))sum_(U<b<=N/a)chi(b),

and so has modulus at most QN/U by (PV).

Also the convergent character harmonic tail satisfies

    |sum_(b>U)chi(b)/b|<=Q/U.                          (3.1)

To verify (3.1), let A_U(t)=sum_(U<b<=t)chi(b), which is bounded by Q for every t. Partial summation on (U,T], followed by T->infinity, gives the integral of A_U(t)/t^2, of modulus at most Q/U. No estimate at Re s<1 is needed.

Combining the three terms proves the optimized-input estimate

    |A(N)-lambda N|<=U+2QN/U.                         (3.2)

For N>=Q, take U=ceil(sqrt(QN)). It satisfies 1<=U<=N, U<=2sqrt(QN), and 2QN/U<=2sqrt(QN). Thus

    |A(N)-lambda N|<=4sqrt(QN).                       (3.3)

For real x>=Q+1, floor(x)>=Q and lambda>0. In particular (3.3) yields the upper bound

    A(x)<=lambda x+4sqrt(Q)sqrt(x).                    (3.4)

This is O(D^(1/4)L^(1/2)sqrt(x)) error. The existing Lemma31 hyperbola source instead inserted a multiple of D in (3.2), leading to sqrt(Dx); the finite algebra and positivity are unchanged here. We have rederived the replacement with the actual uniform interval bound, rather than merely changing a symbol in a source theorem.

For any real V>=Q+1 and Y>=V, Abel summation and A(V)>=0 give

    sum_(V<n<=Y)nu(n)/n
      =A(Y)/Y-A(V)/V+integral_V^Y A(t)/t^2 dt
      <=lambda(1+log Y)+12sqrt(Q)V^(-1/2).             (3.5)

The constants are explicit: 4sqrt(Q)/sqrt(Y) comes from the endpoint and at most 8sqrt(Q)/sqrt(V) from integrating t^-3/2. Floor and real endpoints cause no extra term in this exact Stieltjes/Abel identity.

## 4. Positivity, square convolution, and the new threshold

The real multiplicative function nu=1*chi is nonnegative, including at ramified primes. At a prime ell, with q=chi(ell):

- q=1 gives nu(ell^e)=e+1 and (nu*nu)(ell^e)=binomial(e+3,3)>= (e+1)^2
- q=-1 gives nu(ell^(2j))=1, nu(ell^(2j+1))=0; the convolution is j+1 at exponent 2j and zero at odd exponents
- q=0 gives nu(ell^e)=1 and (nu*nu)(ell^e)=e+1

Multiplicativity proves pointwise

    nu(n)^2<=(nu*nu)(n).                               (4.1)

For Y<=P^3 the total harmonic mass satisfies

    H_nu(Y):=sum_(n<=Y)nu(n)/n <<L^2.                 (4.2)

Indeed the part up to D^2 is at most (1+2L)^2 by nu<=tau_2. For the remaining part, (3.5) with V=D^2 costs lambda(1+3B)+12sqrt(Q)/D, which is O(1) under original A for sufficiently large D. If Y<D^2 only the first estimate is needed.

If ab>Z, then a>sqrt(Z) or b>sqrt(Z). Combining (4.1), nonnegativity, and (4.2) gives the EXACT positive convolution-tail comparison

    sum_(Z<n<=Y)nu(n)^2/n
      <=2 H_nu(Y) sum_(sqrt(Z)<a<=Y)nu(a)/a.           (4.3)

When Z>=16(Q+1)^2, the lower cutoff sqrt(Z) is certainly in the valid range of (3.5). Equations (3.5) and (4.3), with sqrt(Q)<<D^(1/4)L^(1/2), prove

    sum_(Z<n<=Y)nu(n)^2/n
      <<L^2[lambda(1+log Y)+D^(1/4)L^(1/2)Z^(-1/4)]. (4.4)

This proves (1.1). For fixed delta>1, Z=D^delta eventually exceeds 16(Q+1)^2. The second term is L^(5/2)D^(-(delta-1)/4), smaller than every fixed negative logarithmic power. For Y<=P^3, the first term is O(L^-2022 L^2 L^9)=O(L^-2011), proving (1.2). For Y=X=D^4 it is O(L^-2022 L^2 L)=O(L^-2019), proving (1.3).

Two explicit slowly moving thresholds also follow, without changing the original assumption:

    Z=D L^8054 gives the L^-2011 bound through P^3,
    Z=D L^8086 gives the L^-2019 bound through D^4.

The exponents solve 5/2-K/4=-2011 or -2019. These are arithmetic statements; none authorizes a new finite-inverse cutoff in an actual family norm.

## 5. Define the ORIGINAL discarded inverse sector exactly

Retain the literal original shifts beta_1,beta_2,beta_3,0, all imaginary, and

    a_beta=(n^-beta_1)*(n^-beta_2)*(n^-beta_3)*chi,
    upsilon=mu*(mu chi), |upsilon|<=nu.

Let Z=D^delta with fixed 1<delta<4. For original primes, nonprincipal psi of parity a, s=1/2+it, and 1<=M<=P^2D^5, define

    T_Z(M;p,psi,t)=sum_(dn<=M,Z<d<=X)
       upsilon(d)a_beta(n)psi(dn)(dn)^-s V4(n;s,p,a),
    S_Z(M;p,psi,t)=sum_(dn<=M,d<=Z)
       upsilon(d)a_beta(n)psi(dn)(dn)^-s V4(n;s,p,a).    (5.1)

The original core is S_X=S_Z+T_Z exactly. We do NOT redefine its original G or assert T_Z negligible on the whole core. The input n<=P^3 remains automatic here because n<=dn<=M<P^3 eventually. Outside this retained core it is not removed.

Put alpha=1/B, z=alpha+iv. The original Mellin identity gives

    T_Z=(1/(2pi))integral_R H4(z;s,p,a)
       sum_(k<=M)E_Z,z(k)psi(k)k^(-s-z)dv,
    E_Z,z(k)=sum_(d|k,Z<d<=X)upsilon(d)d^z a_beta(k/d). (5.2)

Every sum is finite, and H4 is the literal original four-gamma factor. The accepted positive-line envelope is

    |H4(alpha+iv;s,p,a)|
       <<exp(-v^2/2)/(alpha^2+v^2)^(1/2),
    integral_R sup_(original p,t,a)|H4|dv<<log B.       (5.3)

Both real-character parities and both psi parities are included in its exact gamma parameters. No reciprocal-product input is needed for the coefficient argument in this note.

## 6. Exact coefficient and hybrid-Gaussian attachment costs

Because d<=D^4, |d^z|=d^(1/B)<=2 eventually, uniformly for ALL v. Also |a_beta|<=tau_4, with all actual shifts retained. Thus

    |E_Z,z(k)|<=2[(nu 1_(Z<d<=X))*tau_4](k).           (6.1)

Divisor Cauchy and tau_2(dm)<=tau_2(d)tau_2(m) give

    sum_(k<=M)|E_Z,z(k)|^2/k
      <<[sum_(Z<d<=X)nu(d)^2tau_2(d)/d]
        [sum_(m<=M)tau_4(m)^2tau_2(m)/m].              (6.2)

Apply Cauchy once more to the first bracket. Its first square factor is the NEW finite-range tail (1.3). Its second square factor uses the literal finite top endpoint X=D^4:

    sum_(d<=D^4)nu(d)^2tau_2(d)^2/d
      <=sum_(d<=D^4)tau_16(d)/d <<L^16.

Consequently the first bracket in (6.2) is O_delta(L^(-2019/2+8))=O_delta(L^(-2003/2)). The remaining bracket is O(log(2M)^32), since tau_4^2tau_2<=tau_32. Since M<P^3, log(2M)<<B=L^9. Therefore

    sum_(k<=M)|E_Z,z(k)|^2/k
       <<_delta L^(-2019/2+8+288)=L^(-1427/2).         (6.3)

Using B^8 rather than L^8 for the first Cauchy factor would unnecessarily lose 64 logarithmic powers. The full finite range d<=D^4 is what justifies L^8 here. No finite/full restoration extends the d range to P^3 in (6.2).

The required accepted HYBRID interface, not merely ordinary LS, is

    sum_(original p, nonprincipal psi of fixed parity)
      integral |sum_(k<=M)c_k psi(k)k^-it|^2 dmu(t)
      <<(P^2+M/W)sum_(k<=M)|c_k|^2.                  (HLS)

This is the accepted hybrid-Gaussian large-sieve interface. Its derivation uses the continuous bound (Q^2 T+M), translation in t, and summable width-W Gaussian covering. The exact normalization 1/W supplies M/W, with no H/W or log M factor. The derivation from the interval primitive large sieve uses Conrey–Iwaniec–Soundararajan, [Asymptotic Large Sieve](https://aimath.org/~kaur/publications/u14.pdf), arXiv:1105.1176v1, equation (1.6). Exact mathematical source and acceptance identities are listed in SOURCE_PINS.json; this note does not claim a new proof or Lean audit of that accepted interface.

At each fixed v, the coefficients E_Z,z(k)k^(-1/2-z) in (5.2) are common across p,t, and their squared energy is at most (6.3), because alpha>0. Apply (HLS), extract the original H4 scalar envelope on the ORIGINAL height window, and use Minkowski with (5.3). Summing the two parity bounds proves

    ||T_Z(M)||_H^2
       <<_delta (P^2+M/W)L^(-1427/2)(log L)^2.         (6.4)

All Mellin heights are included with this v-uniform coefficient bound. No new cutoff or reciprocal-height tail is needed. This proves (1.4) for the actual original discarded sector, not an unweighted coefficient surrogate.

## 7. Cross term, actual diagonal, and the unpaid full-core gate

For the retained S_Z, a crude bound suffices to keep the cross explicit. On the same Mellin line, |upsilon(d)d^z|<=2tau_2(d) and |a_beta|<=tau_4, so its coefficients are bounded by 2tau_6. Since tau_6^2<=tau_36,

    ||S_Z(M)||_H^2
       <<(P^2+M/W)L^324(log L)^2.                    (7.1)

This is (HLS) and (5.3), without a new arithmetic hypothesis. Cauchy with (6.4) gives

    |<S_Z,T_Z>|
      <<_delta(P^2+M/W)L^((324-1427/2)/2)(log L)^2
       =(P^2+M/W)L^(-779/4)(log L)^2,                 (7.2)

This conservative bound is valid without importing a main energy estimate. The PINNED accepted full low-output theorem gives, for the same original S_X and every M<=P^3,

    ||S_X(M)||_H^2 <<(P^2+M/W)L^52(log L)^2.

This is the exact theorem accepted by the hybrid-sieve review, not an extension inferred from a paid logarithmic endpoint. Since S_Z=S_X-T_Z, (6.4) and Cauchy now improve (7.2) to

    |<S_Z,T_Z>|<=|<S_X,T_Z>|+||T_Z||^2
      <<_delta(P^2+M/W)L^((52-1427/2)/2)(log L)^2
       =(P^2+M/W)L^(-1323/4)(log L)^2.                (7.2a)

In particular

    ||S_X||^2-||S_Z||^2=||T_Z||^2+2Re<S_Z,T_Z>        (7.3)

is exact. At M<=P^2L^730, the last two terms are o(P^2), since the sharper cross exponent is 330-1323/4=-3/4. At M<=P^2L^1113, (6.4) gives ||T_Z||^2<<P^2L^-1/2(log L)^2=o(P^2), but even (7.2a) does not make its cross o(P^2) at that larger endpoint. The distinction between norm approximation and squared-moment approximation is essential.

At M=P^2D^5, the explicit upper bounds become

    ||T_Z||^2 << P^2[L^(-1427/2)+D^5 L^(-2227/2)](log L)^2,
    |<S_Z,T_Z>| << P^2[L^(-1323/4)+D^5 L^(-2923/4)](log L)^2.

Since D=exp(L), the D^5 terms cannot be absorbed into any fixed logarithmic target. The method therefore fails to pay the full-core discarded inverse sector or its cross, even though its harmonic coefficient tail is much smaller. These are unabsorbed UPPER BOUNDS, not a claim that the actual quantities are this large.

The actual parity covariance remains

    (p-1)/2[1_(k=l mod p)+(-1)^a1_(k=-l mod p)]-1_(a=0)

on p-unit k,l and zero otherwise. If A_Z(k),A_tail(k) are the literal gamma-dependent finite output coefficients in (5.1), the same-output contribution contains

    |A_Z(k)+A_tail(k)|^2
      =|A_Z(k)|^2+|A_tail(k)|^2+2Re(A_Z(k)conj(A_tail(k))).

The factor ((p-1)/2-1_(a=0))/k and the original Gaussian are unchanged. Thus (7.3) retains the actual diagonal as well as every off-diagonal and principal-projection cross. No coefficient restriction is assumed to decrease a sampled norm.

## 8. A generic original-weight bilinear bound cannot remove the conductor excess

This is a separate method obstruction, not an actual-coefficient lower bound. For any original parameter set whose strict prime window P<p<P(1+L^-68) is nonempty, choose an actual prime p_0 IN THAT WINDOW and any of its nonprincipal characters psi_0, of parity a. This obstruction is explicitly conditional on that nonempty-window property; it does not substitute an arbitrary nearby prime or invoke a new prime-distribution theorem. The chosen coefficients below are then fixed and common across the entire family. Let

    U=P D^(1/8), I=(U,2U],
    A(r)=conj(psi_0(r))r^(it_c)1_(r in I),
    B(n)=conj(psi_0(n))n^(it_c)1_(n in I).

Both harmonic factor energies are bounded:

    sum_r|A(r)|^2/r <=log 2+o(1),
    sum_n|B(n)|^2/n <=log 2+o(1).                     (8.1)

The box lies inside the remaining balanced ranges and rn<=4P^2D^(1/4)<P^2D^5. Consider the family operator

    F_(p,psi,t)=sum_(r,n)A(r)B(n)psi(rn)(rn)^(-1/2-it)
                                   V4(rn;1/2+it,p,psiParity),

with the SAME A,B at every family label and the ACTUAL original weight, corresponding to a d=1 weight input. The accepted exact negative-line formula proves

    V4(x;s,p,a)=1+O((x/C_min)^(1/4)),
    C_min>=cP^2sqrt(D)L^1038,

uniformly on the original height window and both parities. For x<=4P^2D^(1/4) this error is O(D^-1/16 L^-519/2)=o(1).

At psi=psi_0, the character phases of A and B cancel exactly on p_0-units. For |t-t_c|<=1/10, after removing a common unit scalar, the remaining phase of each term is confined to an arc of length at most (1/5)log 2. The total weighted sum therefore has modulus at least a fixed positive constant times

    [sum_(r in I,p_0 not dividing r)r^-1/2]^2 >>U.

The uniform o(1) error in V4 cannot remove this lower bound. The p-unit harmonic square-root sum is comparable to sqrt(U), since U/p_0 tends to infinity and the deleted fraction is O(1/p_0). The original restricted normalized Gaussian assigns mass >>1/W to |t-t_c|<=1/10. Keeping only this single nonprincipal character in the positive family yields

    ||weighted bilinear operator(A,B)||_H^2
       >>U^2/W=P^2D^(1/4)/W.                        (8.2)

Thus no estimate of the form P^2L^C times the product of (8.1), with ANY fixed C, can hold for arbitrary separable coefficients on the permitted balanced box, even with the original V4 and Gaussian left intact. The actual coefficients c_X,z and d23 are not these resonating coefficients. Equation (8.2) does not refute a theorem using their special arithmetic; it identifies exactly why a generic bilinear sieve or a lengths-only simultaneous duality argument cannot supply the missing D-power gain.

This obstruction is derived here from an explicit character resonance and the exact original V4 residue estimate. It uses no chi-completion, root-randomness or isometry saving.

## 9. Disposition and verification boundary

The new arithmetic tail (1.1)-(1.3) is proved, and the literal actual remainder/cross estimates (1.4)-(1.5) are proved. The original d>D^delta sector is genuinely negligible on the stated polylogarithmic output ranges. It is NOT yet paid on the full P^2D^5 core. The smaller arithmetic threshold by itself does not change the accepted finite inverse or close the balanced sector.

SOURCE_PINS.json identifies the exact public PV/Fourier and nu-square sources, the accepted hybrid-Gaussian interface and its acceptance identity, and the original H4/V4 envelope sources. These selected source bytes have been checked; no new Lean certificate or full recursive formal audit is claimed. Finite diagnostics support the hyperbola algebra, primitive Fourier bound, ramified square majorant, weighted tail inequalities, literal discarded/retained partition and rational budgets. They do not numerically instantiate the exceptional assumption or certify the asymptotic theorem.
