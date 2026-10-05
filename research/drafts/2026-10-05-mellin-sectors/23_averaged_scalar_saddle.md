# An averaged Gaussian saddle estimate and its precise downstream interfaces

Draft research note dated 2026-10-05. Independently source-reviewed jointly with the fixed-gap clarification in Section 5.1; not Lean-certified. Original assumption exponent 2022, time parameters t0=L^519 and W=L^400, and target exponent 2024 remain unchanged. Separate bounded alternative-route proof. We prove the proposed Fourier-L1 estimate for the exact scalar saddle kernel, including the endpoint v=-1. We also prove weighted/derivative versions, its near-one Mellin normalization, coarse exponential localization outside a comparable-height interval, and an explicit divisor-sampling bound. These supply several identifiable analytic interfaces used downstream in the original paper. They do not prove a new good-character family, exact phase-tilted mean formula, signed main term, whole middle-energy estimate or original strict gap.

The [time-parameter audit](20_time_parameter_audit.md) is unchanged. Here the height variable is denoted T=t0; it must not be confused with the paper's separate auxiliary scale mathcalT=exp(L^1.1).

## 1. Exact Fourier normalization and theorem

For W>=2 and T>=0 define

    Delta_(T,W)(x)=integral_R
       exp[(1/2+2pi i T)u-W^2u^2-2pi i x(exp(u)-1)]du,
    G_(T,W)(x)=sqrt(pi)/W * exp[-pi^2(x-T)^2/W^2]. (1.1)

The definition extends to every real x as an absolutely convergent integral. For x>0 it is exactly the scalar kernel used in the primary original construction. Set

    tau=T/W^2, epsilon=tau+1/W.

Assume 0<=tau<=1. For every pair of fixed nonnegative integers j,m, we prove

    integral_R (1+|(x-T)/W|)^m
       |d^j/dx^j [Delta_(T,W)(x)-G_(T,W)(x)]|dx
          <=C_(j,m) epsilon W^-j.               (1.2)

In particular,

    integral_R |Delta_(T,W)-G_(T,W)|dx
          <=C(T/W^2+1/W).                       (1.3)

We also prove, for every fixed j,N,

    |d^j/dx^j [Delta_(T,W)-G_(T,W)](x)|
       <=C_(j,N) epsilon W^(-j-1)
                           (1+|(x-T)/W|)^(-N). (1.4)

The constants depend only on the indicated fixed orders. No coefficient cancellation, arithmetic hypothesis or discarded inverse term enters these scalar bounds.

Use Fourier convention Fhat(x)=integral F(v)exp(-2pi i xv)dv. The EXACT substitution v=exp(u)-1 gives

    F(v)=1_(v>-1)(1+v)^(-1/2)
               exp[2pi i T log(1+v)-W^2 log^2(1+v)],
    F0(v)=exp[2pi i Tv-W^2v^2],
    Delta=Fhat, G=F0hat.                         (1.5)

There is no omitted Jacobian: exp(u/2)du=(1+v)^(-1/2)dv.

## 2. Uniform Sobolev control after removing the linear carrier

Put y=Wv and extend the following function by zero for y<=-W:

    A_W(y)=1_(y>-W)(1+y/W)^(-1/2)
                              exp[-W^2 log^2(1+y/W)],
    theta(y)=2pi T[log(1+y/W)-y/W],
    R(y)=A_W(y)exp(i theta(y))-exp(-y^2).         (2.1)

The first term in R has a smooth zero extension at y=-W. Indeed, with u=log(1+y/W), every fixed derivative is a finite sum of powers of W,T,u and exp(-u) times exp[-W^2u^2-u/2] and a unit phase. As u tends to minus infinity, the Gaussian in u dominates every such factor. Thus all derivatives tend to zero at the endpoint. Both terms are Schwartz functions at plus infinity as well.

We prove the stronger real-space bounds, for every fixed j,m,

    ||(1+|y|)^m R^(j)(y)||_1
       +||(1+|y|)^m R^(j)(y)||_2
          <=C_(j,m)(tau+1/W).                   (2.2)

### Central region

On |y|<=W/2, log(1+y/W) is comparable to y/W. Write E(y)=-log(1+y/W)/2-W^2log^2(1+y/W). Both E(y) and -y^2 are bounded above by a constant minus c y^2. Taylor's formula with bounded derivatives on [-1/2,1/2] gives

    |E(y)+y^2|<=C(|y|+|y|^3)/W.

For every fixed derivative order, the corresponding derivative difference is also at most W^-1 times a fixed polynomial in |y|. Applying the finite product/chain rule to exp(E), and using the bound by exp(-c y^2), yields

    |d^j/dy^j [A_W(y)-exp(-y^2)]|
       <=C_j W^-1 (1+|y|)^(C_j)exp(-c y^2).     (2.3)

This argument does not assume E+y^2 is uniformly small throughout the region; the inequality |exp(E)-exp(E0)|<=|E-E0|exp(max(E,E0)) handles that issue.

For the phase,

    |theta(y)|<=C tau y^2,
    theta'(y)=-2pi tau y/(1+y/W),
    |theta^(j)(y)|<=C_j tau, j>=2.              (2.4)

The last bound uses W>=2 and j fixed. Since tau<=1, every positive-order derivative of exp(i theta) contains at least one factor tau and is bounded by tau times a fixed polynomial in |y|. For order zero use |exp(i theta)-1|<=|theta|. Combining (2.3)-(2.4) proves (2.2) on the central region.

### Exterior and the endpoint

For y>-W change back to u=log(1+y/W), so dy=W exp(u)du. The square of the amplitude has the particularly simple measure

    |A_W(y)|^2dy = W exp(-2W^2u^2)du.           (2.5)

Every fixed y derivative and polynomial y weight contributes only a fixed polynomial in W,u,T/W and exponentials exp(C_jm |u|). Because T/W=tau W<=W, these factors are at most fixed powers of W times exp(C_jm|u|) and a fixed polynomial in u. On |y|>W/2 one has |u|>=c0>0 whenever y>-W. Completing the square in (2.5) therefore bounds these exterior L2 norms by a fixed power of W times exp(-cW^2). The L1 calculation is identical, with exponent -W^2u^2 plus a fixed linear term in u. The Gaussian reference term obeys the same exterior bound.

These exponentially small quantities are O_(j,m)(1/W), uniformly for W>=2. This proves (2.2) globally, including the entire v approaching -1 tail. No endpoint mass or boundary distribution is introduced by zero extension.

## 3. Fourier consequences

Equation (1.5) becomes

    Delta(x)-G(x)=W^-1 Rhat((x-T)/W).             (3.1)

Plancherel and Cauchy-Schwarz give, for example,

    ||Rhat||_1
       <=[integral_R(1+4pi^2xi^2)^(-1)dxi]^(1/2)
                      (||R||_2^2+||R'||_2^2)^(1/2)
       <=C epsilon.

This proves (1.3) with the exact W cancellation in the change of frequency variable. Applying the same argument to y^j R and enough derivatives gives every weighted L1 bound (1.2). Integration by parts in the Fourier integral, using (2.2) in L1, proves (1.4).

In particular

    ||Delta||_1<=1+C epsilon,
    ||Delta^(j)||_1<=C_j W^-j,
    |Delta^(j)(x)|<=C_(j,N)W^(-j-1)
                          (1+|(x-T)/W|)^(-N),  (3.2)

where epsilon<=3/2 has been absorbed. These are absolute bounds. They do NOT imply Delta(x)=G(x)(1+O(epsilon)) uniformly where G is extremely small, or positivity of the generally complex Delta.

## 4. Mellin normalization under weaker local constraints

Assume now T=L^a, W=L^b with fixed a>b>0. Let alpha_p=pi/L^9 and suppose

    b>=9, 2b-a>=9.                              (4.1)

Then epsilon=O(alpha_p). For |s-1|<=10alpha_p, we claim

    delta_(T,W)(s):=integral_0^infinity Delta(x)x^(s-1)dx
       =1+O(alpha_p log L).                     (4.2)

Let eta0=10alpha_p<1/4. On 0<x<1, (1.4) bounds |Delta-G| by C epsilon/W, so its weighted integral is O(epsilon/W). On x>=1,

    x^(Re s-1)<=1+x^eta0
       <=C(1+T+W)^eta0(1+|(x-T)/W|),

and (1.2) gives an O(epsilon) error, since (1+T+W)^eta0=O(1) for fixed a,b. Thus replacing Delta by G costs O(epsilon) in the Mellin integral, including the possible mild singularity at zero.

For the Gaussian, restrict first to T/2<x<3T/2. Its Mellin factor differs from T^(s-1) by O(alpha_p |x-T|/T); integrating gives O(alpha_p W/T). The complementary Gaussian tails are exponentially small in (T/W)^2, with their weighted integrals also controlled near zero. Since T/W=L^(a-b) tends to infinity and T^(s-1)=1+O(alpha_p log L), (4.2) follows.

Moreover, for 1/2<=Re s<=2, two integrations by parts and (1.2)-(1.4) give

    delta_(T,W)(s)<<L^C |s|^-2.                 (4.3)

Indeed integral |Delta''(x)|x^(Re s+1)dx is bounded by a fixed power of T+W+1, and the boundary terms vanish. These are the two Mellin-transform interfaces needed in the residue treatment of the UNTILTED scalar kernel. The earlier pointwise sufficient condition 4b>=3.06a+9 is not used.

## 5. Coarse exponential localization still available

Polynomial Fourier decay alone must not be used to pay an absolute P-power family cap at a merely polynomial-L distance. We therefore prove a separate exponential bound. Assume 2W<=T<=W^2 and put r=x/T.

For x>=2T, split the u integral at u0=-(1/2)log r. Its left real tail is bounded by exp[-cW^2log^2 r]. On the right piece shift to u-iy, where

    A=T(sqrt(r)-1), y=c0 min(A/W^2,1)

and c0 is a sufficiently small absolute constant. Along the shifted piece, x exp(u)>=sqrt(xT), and sin(y)/y is close enough to one that the phase contributes at most -c A y. The Gaussian's added W^2y^2 is absorbed by that negative term. The vertical connector at u0 has Gaussian size exp[-cW^2log^2 r]; its phase does not grow. Therefore

    |Delta(x)|<=C{exp[-cW^2log^2(x/T)]
           +exp[-c min(T^2(sqrt(x/T)-1)^2/W^2,
                                  T(sqrt(x/T)-1))]}.         (5.1)

For 0<x<=T/2, split at u0=(1/2)log(T/x), keep the right real tail and shift the left piece upward. The same calculation, now with A=T-sqrt(xT)>=cT, gives

    |Delta(x)|<=C{exp[-cW^2log^2(T/x)]
                                   +exp[-cT^2/W^2]}.        (5.2)

The shifts occur on one-sided half-lines where the exponential phase decays at the infinite endpoint. No upward shift through the growing positive-u tail is made. Fixed x derivatives insert (exp(u)-1)^j; the same bounds hold with constants depending on j, after harmless fixed polynomial factors are absorbed by the Gaussian.

Changing variables r=x/T and then sqrt(r)-1 on the high side shows that for every fixed v>-1 and fixed j,

    integral_(x outside [T/2,2T],x>0)
       |Delta^(j)(x)| x^v dx
       <=(1+T+W)^C exp[-c min(W^2,(T/W)^2)].     (5.3)

Consequently, when b>=5 and a-b>=5, these comparable-range tails are O(exp(-cL^10)), including every fixed polynomial moment. This is sufficient for the constant-factor localization used in the cited downstream arithmetic sums. It is a new direct contour estimate, not a consequence of (1.3) alone.

### 5.1. Mandatory fixed-gap localization and the literal primary interval

For every fixed eta0 in (0,1), the one-sided contour proof in Section 5 gives, for fixed j and v>-1,

    integral_(x>0, x outside [(1-eta0)T,(1+eta0)T])
      |Delta^(j)(x)| x^v dx
       <=C_(j,v,eta0)(1+T+W)^C
                    exp[-c_eta0 min(W^2,(T/W)^2)],

under the same assumptions 2W<=T<=W^2. The corresponding pointwise bounds in (5.1)-(5.2) hold throughout x/T>=1+eta0 and x/T<=1-eta0, with constants depending on this fixed gap.

Indeed in the upper case use r=x/T, u0=-(1/2)log r, A=T(sqrt(r)-1) and y=c_eta0 min(A/W^2,1). Choose c_eta0 smaller than a fixed multiple of both |log(1+eta0)| and sqrt((sqrt(1+eta0)-1)/sqrt(1+eta0)). Then the sine quotient leaves at least A/2 in the decaying phase, the Gaussian's W^2y^2 term is absorbed, and the vertical connector retains its Gaussian suppression. For the lower case take u0=(1/2)log(T/x), A=T-sqrt(xT), and decrease c_eta0 additionally using |log(1-eta0)|. Its sine quotient only strengthens decay. Since |u0| and A/T are bounded below by positive constants depending on eta0, the derivative and weighted-integral arguments are exactly the same. This proves the extension, rather than applying a bound outside its stated range.

For the literal primary interval on Zhang v1 page 38,

    I(Rh)=[(1/3)P T Rh,4P T Rh],
    P<p<P(1+L^-68), R<=r<2R,

the scalar argument is x=l/(p r h). Below I(Rh), x/T<1/3. Above it,

    x/T>2/(1+L^-68)>3/2

for sufficiently large L. Therefore the fixed-gap theorem with eta0=1/2 pays BOTH excluded edges of the original interval by exp(-cL^10) under the parameter conditions in Sections 4–5. The original statement outside [T/2,2T] alone would not cover the tiny upper sliver below 2T; this addendum supplies the required stronger statement explicitly.

No pointwise relative positivity or arbitrary coefficient-weighted consequence of continuous L1 is inferred. The separately proved divisor-sampling bounds in Section 6 and all unpaid global interfaces remain as stated.

## 6. A divisor-sampling interface for the actual arithmetic uses

For any fixed integer r>=2, the elementary largest-factor hyperbola argument gives

    sum_(n in an interval I subset [z,2z], length h)
       tau_r(n)<<_r h(log(2z))^(r-1)
                         +z^(1-1/r)(log(2z))^(r-2).         (6.1)

Choose a largest member of an ordered r-factorization; the product of the other r-1 members is <=(2z)^(1-1/r). Counting the last member by h/q+1 and summing tau_(r-1)(q) proves (6.1), with endpoints included.

Apply (6.1) to successive dyadic distance blocks about AT, using the absolute Schwartz envelope (3.2). For A>=1, T=L^a, W=L^b, T>=2W and 1<=A<=P^C0, this gives

    sum_(n>=1) tau_r(n)|Delta(n/A)|
       <<_r A(log(2AT))^(r-1)
          +A^(1-1/r)T^(1-1/r)W^-1(log(2AT))^(r-2)
       <<A L^C.                                (6.2)

The same conclusion holds for tau_r(dn), with an additional tau_r(d), by divisor submultiplicativity. All infinite distance blocks are summed with a fixed decay order larger than r+3; their factors (log(2AT)+j)^(r-1) are retained and geometrically summable. Small n near zero can be handled by a prefix interval; they do not require a false lower endpoint comparable to AT.

When A is exponential in L, the second term in (6.2) is smaller than the first for the fixed polynomial T,W. We have retained it because some actual p-unit-removal terms have A as small as one. Even there it costs only a fixed L power, not a P power.

As two concrete checks of downstream normalization:

- In the ordinary-prime principal correction, the prefactor 1/p combines with the inner scale A=pk and its outer 1/k. The support of the remaining short coefficient is <P mathcalT^-2. Formula (6.2) bounds that correction by P mathcalT^-2 L^C=O(P mathcalT^-c). For l divisible by p, substituting l=pv changes A to k and removes the prefactor 1/p; the same bound follows from the second, retained term in (6.2).
- In the principal-character contribution inside the primary quantity S(1,D;p) on page 78, the inner scale is A=Dpk and the denominator is phi(Dk)k. For coefficient majorant tau_5(dl), (6.2) gives a bound <<p L^C after the d,k sums. Explicitly phi(Dk)>=phi(D)phi(k), D/phi(D)<<L^2, sum_(d<P)tau_5(d)/d<<B^5 and sum_(k<P)1/phi(k)<<B^2; the remaining inner logarithm costs B^4. Thus p L^2 B^11 suffices. Here D/phi(D)=sum_(d|rad(D))1/phi(d)<=sum_(d<=D)tau_2(d)/d<<L^2, and 1/phi(k)<=tau_2(k)/k. The bound is for the displayed S(1,D;p) normalization; no omitted outer Gauss factor is declared paid. A sharper logarithmic exponent is not needed for this cited interface.

These are positive arithmetic majorants applied to the exact scalar kernel. They do not assign a sign to Delta or replace an arbitrary sampled norm by its average mass.

## 7. What the source consumers require

Primary inspected locations are [Zhang arXiv:2211.02515v1](https://arxiv.org/pdf/2211.02515v1), pages 27-28, 35-38 and 76-78. The normalized Mellin residue calculation uses the near-one Mellin value and fixed-strip decay, supplied by (4.2)-(4.3). The explicit constant-factor range localization uses tails away from height T, supplied by (5.1)-(5.3) together with the mandatory fixed-gap extension in Section 5.1. In particular the original I(Rh) upper edge is slightly below 2T and is paid using the fixed threshold 3T/2; the outside-[T/2,2T] statement alone is insufficient. The principal and p-unit corrections use absolute divisor-weighted sampling bounds, supplied by (6.2), not merely continuous L1 mass.

The exact positivity in the original argument concerns C*(rho,psi) and the positive time Gaussian. It does not follow from, or require us to declare, positivity of the complex Delta. We have NOT proved the original global pointwise relative statement Delta=G(1+O(alpha_p))+exponentially small error over its entire stated range. The interfaces above are independently proved alternatives for the listed consumers.

This is not a completed re-proof of every mean-value proposition or its numerical constants at altered parameters. In particular exact gamma phase tilts q_epsilon(s) from the [time-parameter audit](20_time_parameter_audit.md) introduce different kernels; (1.1) has no such tilt. The good-character and zero-gap chain, every changed discrete error budget, and the final signed main-term inequalities remain to be verified before any new original conclusion can be claimed.

## 8. Local parameter consequence and scope

For the untilted kernel alone, the sufficient averaged-normalization conditions are

    a>b, b>=9, 2b-a>=9,

with b>=5 and a-b>=5 additionally giving the exp(-cL^10) comparable-range tails. This is substantially weaker than the printed pointwise saddle condition 4b>=3.06a+9.

For illustration, combining these NEW KERNEL conditions with the unchanged hard-window phase-consumer requirement a-b>118 gives first integer pair (a,b)=(247,128). Under the separate Gaussian-refined phase-consumer premise a-b>113, the first integer pair is (237,123). They satisfy the conservative common-coefficient AFE range from the [time-parameter audit](20_time_parameter_audit.md). These are local interface ledgers only. Neither pair is asserted globally feasible, and no already accepted original-parameter result is relabeled as a theorem at those values.

All finite inverse terms, original parities, prime window, masks and actual signed cross structures are untouched by this scalar proof. The independent arithmetic middle problem remains open. All earlier results keep their stated scopes.

## 9. Sources, diagnostic limits and scope

The public primary is [Yitang Zhang, arXiv:2211.02515v1](https://arxiv.org/pdf/2211.02515v1), especially pages [27–28](https://arxiv.org/pdf/2211.02515v1#page=27), [35–38](https://arxiv.org/pdf/2211.02515v1#page=35), and [76–78](https://arxiv.org/pdf/2211.02515v1#page=76). The primary paper is linked, not redistributed. The interval-divisor argument is re-proved above; see also the earlier [mixed-boundary note](15_mixed_transformed_boundary.md). [SOURCE_PINS.json](SOURCE_PINS.json) gives hash-only identities of the exact joint source, mandatory clarification and one independent source review. Hash identity is not a proof certificate.

The [finite diagnostics](diagnostics/README.md) preserve the original author scripts and expected outputs, plus a portable extraction of the independent mathematical tests. Fourier grids check finite normalization and consistency only: they are not rigorous continuous-error or tail certificates. The endpoint, weighted derivative estimates, all infinite tails, Mellin weights, fixed-gap localization and divisor sampling are justified by the analytic arguments above.

Accepted scope is the untilted scalar Fourier–L1/Sobolev estimate and the named consumers at their displayed normalizations, jointly with Section 5.1. No arbitrary tilted-kernel theorem, global altered-parameter theorem, relative positivity, new good-character family, completed signed mean formula, actual middle-energy estimate, new Lean certificate or final strict gap is claimed. The original finite inverse, masks, parities, prime window and target are unchanged.
