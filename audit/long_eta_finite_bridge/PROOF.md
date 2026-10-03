# Long-eta sign research: an actual balanced-box reduction

2026-10-03. Public source-level mathematical proof with independent review. This is not a Lean certificate. Original `(A)` is `L(1,chi)<L^(-2022)`; the separate target scale is `L^(-2024)`. The actual good family, weight, branch, and first R5 profile are unchanged. This report does **not** establish Z2-min.

## Public-edition scope and conventions

The independent review's exact (T2)/(T3) hypotheses and Sections 3–5, particularly its complete high-frequency-tail proof, are authoritative. All finite polynomial lengths must be below `P^2` after the common truncations and tail inflations. With fixed support constant C and `F=P^(kappa/8)`, impose **both** inequalities in the chosen version:

    (T2) C N V <= P^(2-2 kappa),
         C U P^2 T_*^2/(R S) <= P^(2-2 kappa);
    (T3) C N <= P^(2-2 kappa),
         C U D P^3 T_*^3/(M R S) <= P^(2-2 kappa).

Their inflated maximum lengths are respectively bounded by `P^(2-7kappa/4)` and `P^(2-13kappa/8)` on the completed side, and `P^(2-2kappa)` on the other side. Both must satisfy the genuine finite second-sieve endpoint. The rough `RS` criterion does not discharge the other inequality. Its stated use also requires `C D^21 T_*^3 <= P^kappa` eventually.

The convention is `power_gamma(n)=n^(-gamma)`. The raw reflected completed coefficient is `c_inf=chi*power_(-beta3)`. In the ordinary `C_psi conjugate(D_psi)` pairing, `D_inf=conjugate(c_inf)=chi*power_(+beta3)`. These opposite shifts must not be interchanged. The actual `Psi1` whole quadratic form, with every phase and the genuine complement, remains the signed target. The comparison enlarges only nonnegative square sums in Cauchy; it neither deletes `Psi2` from a signed mean nor assumes conjugation closure.

### Global completion: precise limitation

The globally completed sampled residue observable is zero, whereas the original observable is `-m_H+o(1)`. This proves only that their **global difference** is not negligible. It does not identify the original long left complement alone with `m_H`. Comparing the decompositions must retain the globally completed right-contour contribution as well as both left contributions and the endpoint term. Holomorphy relates the two vertical integrals; it does not force either one to vanish. No stronger complement identification is claimed here.

## 1. Result and its exact scope

There is a useful additional arithmetic bridge for the actual remaining left contour. Its strongest form completes the actual shared chi profile as well as the two pure factors; Section 11 gives that improvement. It covers only the exact finite boxes satisfying **both** whole-polynomial maximum-length conditions (T3) below. The leading-scale descriptions `N<P^(2-epsilon)` and `RS>P^(1.0005+epsilon)` are illustrations, not replacement hypotheses. It has total sparse-replacement error `O(a^-1 L^(-623/4))`. All three root factors cancel exactly. The two-completion argument below is an intermediate theorem with a shorter proof and a separate explicit budget.

The intermediate bridge has two parts.

1. Completing the two pure factors **character by character**, and applying the existing second large sieve to two entire coefficient convolutions, removes the outer fixed power `P^.502` loss on a substantial balanced region. The bound has only explicit powers of `L=log D`. The good family is retained throughout; no unproved Psi2 deletion occurs.
2. On the same region, the genuine sparse-nu theorem under (A) permits replacing the finite convolution

       c_X = conjugate(eta_beta3) * nu_[1,X]

   by

       c_infinity = chi * power_(-beta3),       X=D^20.

   The normalized error, summed over all eligible smooth dyadic boxes, is

       O(a^-1 L^(-551/4)) + O(a^-1 P^-K)

   for any prescribed fixed K. Thus the balanced portion no longer contains a Mobius coefficient. Its remaining coefficients are the actual mixed divisor coefficients `chi*power`, with their signs and shifts. This is an arithmetic consequence of the original sparse structure, not an invocation of a non-exceptional Mobius theorem.

Here is the precise two-completion length version. Put `U=D^20 P^.5025`, `V=P^.5025`, and let `(N,R,S)` denote smooth dyadic lengths after combining the eta index with the S_X index. Fix `kappa>0` before D. This intermediate result applies to boxes with

       N V <= P^(2-2 kappa),
       U P^2 T_*^2/(R S) <= P^(2-2 kappa),                 (1.1)

where `T_*` is a fixed constant multiple of the largest actual height in the finite source window. Fixed dyadic support constants can be included in U,V,T_* without changing the statements. This includes `N,R,S=P^(1+o(1))`. On the resonance locus the first condition is essentially

       R S >= P^(1.5025+2 kappa+o(1)).                     (1.2)

The second is weaker there. Conditions (1.1), rather than their exponent shorthand, are the theorem's hypotheses.

No strict constant gain follows from this bridge. The new structured balanced main and every omitted/unbalanced box remain. In particular, this report does not replace S_X by a full continued L-product on the entire contour. That global replacement would annihilate the sampled-zero observable, and its difference is of main order under the accepted zero AFE. Section 9 makes this obstruction explicit.

## 2. Actual data and source inputs

Use exactly the data fixed in the accepted weighted-phase report and review:

* `L=log D`, `P=exp(L^9)`, `T0=2pi L^519`, half-window `L^405`, Gaussian width `L^400`.
* The real primitive chi of conductor D; actual primitive psi at the original primes p; both parities; actual Psi1 and actual c-star.
* The first R5 profile `h(m)=chi(m) f(log m/log P)`, supported in `[P^.502,P^.5025]`, with `|h|<=1` and common coefficients across p,psi.
* `M=sum_(d<=X,D not dividing d) upsilon(d) psi(d)d^-s`, `S_X=sum_(e<=X)nu(e)psi(e)e^-s`, `nu=1*chi`, `upsilon=mu*(mu chi)`.
* `A=M H`, with coefficients `Ahat(u)=sum_(dm=u,d<=X,D not dividing d)upsilon(d)h(m)`. The deletion remains on d. In particular `|Ahat|<=tau3` and its support ends at U.
* Actual prime mass `Mcal>=P^2/(4L^77)`, actual `a>1/2`, and actual `m_H=lambda+o(1)` with fixed lambda>0.

Two already-proved source inputs are essential here:

    sum_(D^4<e<=floor(P^2)) nu(e)^2/e <= 1260 L^-2011,     (2.1)

and, for arbitrary common complex coefficients supported at n<=floor(P^2),

    sum_(p,psi primitive) |sum b(n)psi(n)|^2
      <= (32+pi^2) P^2 sum |b(n)|^2.                     (2.2)

Their literal sources are `ZhangLS/Spec/Lemma31.lean`, theorem `lemma31_actual_square_paper_tail_le`, and `ZhangLS/Spec/Lemma33.lean`, theorem `lemma33_actual_second_mean_bound`. The endpoint P^2 in (2.1) is important: the source statement is not restricted to D^20. No new sparse-tail hypothesis is being added.

We also use elementary harmonic divisor bounds

    tau_j(n)tau_k(n)<=tau_(jk)(n),
    sum_(n<=Y) tau_j(n)/n <= (1+log Y)^j.                 (2.3)

All shifts beta_j are purely imaginary. Write `alpha_beta(n)=n^(-conjugate(beta))=n^beta` for the conjugated power in the left integrand. To avoid notation ambiguity below, `bar_eta` means the literal conjugate of eta_beta3, so `bar_eta=mu*alpha`, `alpha(n)=n^(-conjugate(beta3))`, and `|alpha(n)|=1`.

## 3. Safe-line regrouping before any central-line expansion

Start on Re(s)=-1/2, where the entire dual quotient series is absolutely convergent. Its coefficient factor is

    conjugate(kappa)=bar_eta * alpha1 * alpha2.

In `B^dagger=S_X^dagger H^dagger`, let e be the S_X index and m the H index. Their powers in the left integrand are

    q^(s-1) e^(s-1) m^(s-1) r^(s-1) s_index^(s-1).

The scalar gamma kernel and character likewise see q and e only through `n=q e`. Therefore combine them on this safe line:

    c_X(n)=sum_(q e=n,e<=X) bar_eta(q)nu(e).              (3.1)

This operation keeps the exact e cutoff and involves absolutely convergent sums. After the regrouping, the scalar kernel argument is

    x=n r s_index m/u.                                  (3.2)

Apply the accepted single-scalar tail procedure to this representation, not to an infinite series already placed on Re(s)=1/2. The coefficient envelope is still a fixed divisor function: `|c_X|<=tau4`. Thus the high tail at the original safe line is summable, outward scalar shifts have the same exponential gain, and the finite horizontal sums retain their paid Gaussian error. The true resonance is

    n r s_index m/u ~= D p^3(t/(2pi))^3.                 (3.3)

Only after these scalar tails are paid do we move the remaining finite terms to the central line. Partition n,r,s_index into a fixed smooth dyadic partition. Keep the shared h and Ahat as whole polynomials. Near boxes lie in a fixed P-power localization; distant boxes are paid by the same scalar estimates. There are `O((1+log P)^3)=O(L^27)` boxes. A hard artificial localization is identically one on every retained near box and is removed there, exactly as in the accepted review. No sharp product mask is sent through Poisson.

For fixed t a retained separated box has, apart from an exact modulus-one gamma/root/branch scalar, the sum

    sum_(psi in Psi1) A_psi(t) R_psi(t) S_psi(t)
                               conjugate(D_(c_X),psi(t)), (3.4)

where

    A_psi(t)=sum Ahat(u)psi(u)u^(-1/2-it),
    R_psi(t)=sum bar(psi)(r)r^(-1/2+it)alpha1(r)phi(r/R),
    S_psi(t)=sum bar(psi)(s)s^(-1/2+it)alpha2(s)phi(s/S),

and D is the ordinary psi polynomial obtained by conjugating

    sum_(n,m) c_X(n)h(m)bar(psi)(nm)(nm)^(-1/2+it)phi(n/N).

The conjugations in (3.4) are bookkeeping only; all energy bounds below are invariant under them. The literal signs and root factors remain in the scalar. None is replaced when later asking for a signed main term.

## 4. Exact completion and a uniform Fourier symbol

This section pays the p and t dependence instead of calling `T0=P^o(1)` harmless inside a logarithmic saving.

For a fixed smooth compact phi supported inside `(0,infinity)`, put

    w_(R,t)(x)=x^(-1/2+it)phi(x/R),
    hat(w)(xi)=integral_0^infinity w(x)exp(-2pi i x xi)dx.

The small imaginary beta shifts just replace t by `t_j=t+Im(beta_j)`. These are positive and comparable with T0. Primitive-character Poisson gives exactly

    sum_r bar(psi)(r)w(r)
      = tau(bar(psi))/p * sum_(h in Z) psi(h)hat(w)(h/p).

The h=0 term vanishes. Negative h are retained using `psi(-h)=psi(-1)psi(h)`. For h>0 there is the exact change-of-variable identity

    p^-1/2 hat(w)(h/p)
      = h^-1/2 exp(i t log(pt/(2pi e h)))
                         V_t(2pi h R/(pt)),               (4.1)

    V_t(y)=sqrt(t/(2pi)) integral_0^infinity
          z^-1/2 phi(z/y)exp(i t(log z-z+1))dz.            (4.2)

No asymptotic equality is used in (4.1). The analogous negative-frequency symbol has phase `log z+z+1` and a harmless scalar unit.

For any fixed j,A, the symbols have uniform logarithmic derivative bounds:

* on a fixed compact y interval containing the possible stationary point z=1, `(y d/dy)^j V_t(y)=O_j(1)`;
* for small y, the bound is `O_(j,A)(t^(1/2-A)y^(1/2))`;
* for large y, it is `O_(j,A)(t^(1/2-A)y^(1/2-A))`.

Proof: the first statement is one-dimensional stationary phase at the fixed nondegenerate critical point of `log z-z+1`, with parameter-dependent compact amplitudes. The amplitude after j logarithmic y derivatives is a fixed linear combination of derivatives of phi(z/y), whose support stays in a fixed compact interval in this region. The factor sqrt(t) cancels the stationary-phase t^-1/2. In the two outer regions the phase has no stationary point. Repeated integration by parts with `(it(1/z-1))^-1 d/dz` gives the stated estimates; the support z~y gives the y powers. Negative frequencies are nonstationary everywhere and obey the same bounds. These arguments apply for each fixed derivative order uniformly for every t>=1.

Consequently, if `v_t(x)=V_t(exp x)`, then

    ||v_t||_1+||v_t''||_1 <= C_phi,
    integral_R |Mellin(V_t)(xi)|d xi <= C'_phi.           (4.3)

The second claim follows by bounding the Fourier transform using the first norm at |xi|<=1 and the second norm times |xi|^-2 elsewhere. Thus Mellin inversion separates `(h/p)` with **uniform O(1) total variation**, not a factor T0^j. The h^-it, p^it and t-dependent phases in (4.1) are kept as exact unit twists. After Mellin inversion the h coefficients are common across every prime p; the remaining p factors have modulus one.

Truncate the dual index at the p-independent bound

    H_R=P^(kappa/8) * C P T_*/R,
    H_S=P^(kappa/8) * C P T_*/S.                         (4.4)

If either is below 1, the corresponding entire transform is a nonstationary tail and can be treated directly. Otherwise, rapid large-y decay bounds the discarded tails, even under the initial fixed P-power absolute cost, by `O(P^-K)` for any fixed K after choosing one fixed integration-by-parts order. No power of L is traded against a positive power of P. The kept coefficients, for every Mellin parameter, are bounded by a fixed constant times h^-1/2. All auxiliary signs/parities are finite choices.

This proves the exact form needed for (2.2): two short dual Dirichlet polynomials with common coefficients, integrated against Mellin measures of uniformly bounded total variation, and multiplied by arbitrary modulus-one family scalars.

### 4A. Complete high-frequency-tail payment from the independent review


Uniform Mellin total variation alone would not authorize a sieve on an infinite central-line polynomial. That is not the justification used here. The positive exponent margin in (T2)/(T3) permits a direct absolute high-frequency tail estimate, which I detail to remove this potential gap.

Let `q<=Qmax`, `1<=tau<=T_*`, and set

    Bmax=C Qmax T_*/R,  F=P^(kappa/8),  H=F Bmax.

Choose the fixed C so `h>H` is in the large-y region uniformly for actual q,tau. For H>=1, the large-y estimate in Section 3 and `sum_(h>H)h^-A <<_A H^(1-A)` give

    sum_(h>H) h^-1/2 |V_tau^sigma(2pi hR/(q tau))|
      <= C_A (q/R)^(A-1/2) H^(1-A)
      <= C_A T_*^(1/2-A) Bmax^1/2 F^(1-A).              (Tail)

The tau dependence cancels in the first inequality. If H<1, every nonzero integer frequency is in the large-y region and

    sum_(h>=1) h^-1/2 |V_tau^sigma(2pi hR/(q tau))|
      <= C_A (q/R)^(A-1/2)
      <= C_A F^(-A+1/2).

Both formulas hold for both signs and for q=Dp as well as p. For the full, untruncated transform, splitting h below, near and above `q tau/R` also gives

    sum_(h>=1) h^-1/2 |V_tau^sigma(2pi hR/(q tau))|
      <= C(1+Bmax^1/2).

Here is an intentionally coarse total budget. All original finite near-box lengths and every Bmax are <=P^4 eventually; for Bmax use R>=a fixed positive constant, Qmax<=2DP and T_* comparable with L^519. The absolute L1 sum of each of A, the c box, and each original or full transformed pure/profile factor is at most P^3 eventually. For A and c this follows from the harmonic divisor bounds and length<=P^4; for transforms use the last display. In a telescoping replacement of up to three factors, one tail thus costs at most `C_A P^14 F^(1-A)` before the box count. O(L^36) boxes are eventually <=P, and a fixed extra P absorbs fixed constants. The family count divided by Mcal is <=1 and the normalized Gaussian integral is bounded. Hence the entire discarded dual tail is at most

    C_A a_norm^-1 P^16 F^(1-A).

Choosing one fixed integer `A>1+8(K+16)/kappa` makes this O(a_norm^-1 P^-K). The H<1 case is at least as good after increasing A if needed. This uses a positive P margin, not the false absorption of a fixed positive P power by L^-J. There is no need here to apply a length-(P^2+N) large sieve to discarded high-frequency dyadic shells.

The precise order is: use the exact per-character Poisson identity; pay the infinite Fourier tails by (Tail); retain all low frequencies and both signs below common H; only then use (M) and the finite length-P^2 second sieve. Every remaining polynomial is genuinely finite. No stationary-phase remainder is separately discarded.

## 5. Entire-polynomial Cauchy removes the outer half-power

After the two completions, group the psi polynomials as

    C_psi = A_psi * dualR_psi * dualS_psi,
    D_psi = H_psi * c-box_psi.                           (5.1)

The common-coefficient lengths are at most `U H_R H_S` and `N V`. By (1.1) and (4.4), both are below P^2, with a fixed margin, eventually. Write the weighted coefficient energy as

    E(b)=sum |b(n)|^2/n,

where all unit n^(it) and Mellin twists are included in b if desired.

For every exact modulus-one multiplier lambda_psi, Cauchy and the existing second sieve give

    |sum_(Psi1) lambda_psi C_psi conjugate(D_psi)|
       <= (sum_(Psi1)|C_psi|^2)^(1/2)
          (sum_(Psi1)|D_psi|^2)^(1/2)
       <= C P^2 sqrt(E(C)E(D)).                         (5.2)

Both square sums can be enlarged to the full primitive family. This is legal for an arbitrary good subset; no statement about signed cancellation over Psi2 has been made. Bounded-total-variation Mellin integration preserves (5.2).

The coefficient of C is bounded by tau5: tau3 for actual Ahat, and one for each pure dual coefficient. Thus

    E(C)<=C(1+log P)^25=O(L^225).                        (5.3)

For original c_X, the D coefficient is also bounded by tau5, giving a per-box bound `O(a^-1 L^302)` after division by `a Mcal`:

    302=77+(225+225)/2.

For the simpler c_infinity in Section 6, the D coefficient is bounded by tau3. Its energy is O(L^81), so the corresponding bound is

    O(a^-1 L^230),       230=77+(225+81)/2.              (5.4)

The Gaussian has bounded L1 mass and introduces no T0 or window-length factor. Summing all eligible boxes adds at most L^27, giving `O(a^-1 L^257)` for the simpler balanced main. This is only an upper bound on the absolute value, far too large for a constant-gap result. Its useful content is the complete removal of the fixed P-power normalization obstruction in this region.

## 6. Exact sparse convolution replacement

As Dirichlet convolutions on positive integers,

    bar_eta*nu = (mu*alpha)*(1*chi) = alpha*chi.          (6.1)

This identity includes ramified integers. No D-unit restriction is inserted. It is compatible with the actual M deletion, which is untouched in Ahat.

Let

    f_tail(e)=nu(e)1_(e>X),
    E_X(n)=c_X(n)-c_infinity(n)
          =-(bar_eta*f_tail)(n).                       (6.2)

On a box n~N, every tail index satisfies e<=C N<P^2 by (1.1). The source sparse bound (2.1) therefore applies to every term of this finite error.

After multiplication by H, the error coefficient is pointwise bounded by the threefold convolution

    |bar_eta| * f_tail * |h|,

with the actual compact n-box mask retained; dropping its bounded absolute value is allowed solely for an energy bound. Apply coefficient Cauchy with the number of ordered triples dividing an integer, then use submultiplicativity of tau3. This gives

    E(error*H)
      <= C [sum |eta(q)|^2 tau3(q)/q]
           [sum_(X<e<=P^2)nu(e)^2 tau3(e)/e]
           [sum |h(m)|^2 tau3(m)/m].                    (6.3)

All summation endpoints here can be enlarged to P^2. Since `|eta|<=tau2` and `|h|<=1`, the first and third factors are at most

    O(L^108),    O(L^27),

using `tau2^2 tau3<=tau12`. For the middle factor, ordinary Cauchy, the **actual** sparse tail, and `nu<=tau2` give

    sum nu(e)^2 tau3(e)/e
      <= [sum nu(e)^2/e]^(1/2)
         [sum nu(e)^2 tau3(e)^2/e]^(1/2)
      <= C L^(-2011/2) L^162 = C L^(-1687/2),            (6.4)

because `nu^2 tau3^2<=tau4 tau9<=tau36`. Consequently

    E(error*H)<=C L^(-1417/2).                          (6.5)

Apply (5.2) to this error and the unchanged C side. After normalization the per-box error is

    O(a^-1 L^[77+225/2-1417/4])
      =O(a^-1 L^(-659/4)).                             (6.6)

The O(L^27) box sum gives the stated

    O(a^-1 L^(-551/4)).                                (6.7)

All constants depend only on the fixed profile, partition, kappa, and fixed desired power-tail order. There is no uncanceled D^C or T0^C in this logarithmic saving. Conditions (1.1) were used before applying the P^2 sieve. The bound is uniform on the finite height window. It retains actual Psi1 and the exact branch/root multiplier.

## 7. What has and has not happened to Psi2

The comparison (6.7) holds directly on the good family. It does not require completion to a full character family and subtraction of Bad. This avoids, rather than guesses, the missing P^3 bad-family estimate.

However, to evaluate the new signed main using character orthogonality, a **new** Psi2 estimate would again be needed unless the evaluation works directly on Psi1. The small comparison error does not supply that estimate for the main. A raw fourth moment of the long D side is generally illegal: at N~P and V~P^.5025, its square has length P^3.005, above the P^2 sieve. Thus (5.2) cannot simply be upgraded to a vanishing bad-family contribution by quoting the old short-polynomial proof.

There is a useful exact further structure, but it is not completed here: write `c_infinity(n)=sum_(zw=n)chi(z)alpha(w)`. After completing r,s, the remaining root factor is epsilon_(chi psi), including the exact CRT factors. Completing the chi(z)bar(psi)(z) sum at conductor Dp can cancel that last root and produces an ordinary two-polynomial character pairing. If both resulting polynomials are shorter than p, full-family orthogonality reduces it to the exact equality of their product indices. The inherited z*w box mask, all gamma phases, and the Psi2 term still have to be paid. This observation does not evaluate that diagonal, assign it a sign, or prove that it is less than m_H.

## 8. The remaining independent proposition

Fix a kappa as above and the inherited smooth partition. Let

* `J_bal^div` be the actual good-family left mean on the eligible boxes (1.1), with c_X replaced by `chi*alpha` and with every multiplier/weight unchanged;
* `J_rest` be the actual original left mean on the entire complementary set of finite boxes, after the already-accepted long-pure negligible region and scalar tails are removed.

Then the proved reduction is

    I_left = J_bal^div + J_rest + o(1).                 (8.1)

The o(1) here consists of the accepted right/endpoint/tail payments as appropriate, the accepted long-pure contribution, and (6.7); no part of J_rest is discarded. More precisely, endpoint/right terms belong to the final Z_H relation, while (8.1) itself needs only the left scalar/long-pure tails and (6.7).

A sufficient **independent** arithmetic statement is now

    Re(J_bal^div+J_rest) <= (1-epsilon)m_H+o(1),
                       epsilon>0 fixed.                (8.2)

This is a smaller structural target than applying a generic Mobius trace estimate to all of (8.3) in the preceding report: the core balanced region has divisor coefficients and no fixed P^.502 budget. It is still a genuine signed theorem, not established here.

For example, independent constants b,c with `b+c<1` and proofs

    Re J_bal^div <= b m_H+o(1),
    Re J_rest <= c m_H+o(1)

would suffice. A whole-quadratic-form estimate at constant precision could suffice without separate b,c. Ordinary large-sieve upper bounds, sparse tail bounds, or unweighted coefficient energies do not supply these constants. No upper/lower bound needed in (8.1) has been assumed beyond the displayed genuine source inputs. The additional bounds just described are explicitly missing.

## 9. Why a global cancellation or a diagonal label gives no gain

If S_X^dagger is replaced on the whole contour by the continued complete product

    L(1-s,bar(psi)) L(1-s,chi bar(psi)),

the two functional equations imply that multiplying it by Phi gives the actual product `L(s,psi)L(s,chi psi)`. The Ctilde denominator then cancels. The resulting full numerator is holomorphic at every sampled L(s,psi) zero and has zero residue there. Its sampled-zero observable is exactly zero.

The original observable is `-m_H+o(1)` under the accepted source AFE. Their difference is therefore of constant scale. This is why a global declaration that the nu tail is o(1) would be false **as an inference from the available estimates**. It is not what (6.7) says: the second-sieve length conditions fail on other boxes, and the full completion changes all those parts as well. The complete comparison must retain the excluded left terms and the globally completed right contribution; this argument does not identify the original left complement alone with the compensation.

On the left, the globally completed numerator can also be written exactly as

    -i B_beta Z_psi^-1 M L(s,chi psi)
                      product_j L(s+beta_j,psi) H H^dagger.

Holomorphy gives equality of its two vertical contours plus endpoints; it does not say that either one-sided integral vanishes. A term called a diagonal after subsequent transforms cannot be dropped on that ground. Nor does evaluating the original full left side as `m_H+o(1)` using the same zero AFE yield the favorable gap in (8.2).

Thus this report proves an actual new reduction and a paid error, but does not claim the main theorem false, a global impossibility, a favorable diagonal constant, or a new strict-gain theorem.

## 10. Checks and trust boundary

`checks/check_author.py` checks the finite convolution identities, the truncated-tail identity, divisor-factor bounds, exact rational exponent arithmetic, admissible length examples, and the Fourier change-of-variable normalization. These checks are regression evidence for algebra and accounting. They do not certify the stationary-phase proof, a large-D threshold, an L-function zero configuration, or (8.2).

No new external literature result is used. The analytic Fourier-symbol lemma is derived in Section 4; the large-sieve and sparse inputs are the actual source theorems identified in Section 2. The inherited contour/tail and long-pure facts remain within the scope of the independent review, with the safe regrouping order explicitly preserved in Section 3.

## 11. Stronger bridge using the actual shared chi profile

This section improves the useful region substantially. It uses the literal `h(m)=chi(m)f(log m/B)`, not just bounded common coefficients.

Add a smooth dyadic partition of the H^dagger index m, with length M. Its smooth coefficient is

    phi_M(x/M)=f(log x/B)phi(x/M).

Every fixed scale-invariant derivative of phi_M is uniformly bounded independently of D,M: derivatives of f contribute inverse powers of B and f itself was fixed before D. There are O(log P)=O(L^9) such M boxes. The complete near-box count is now O(L^36).

The character in this factor is `chi*bar(psi)`, primitive at its **actual conductor Dp**. Apply exactly the Fourier argument of Section 4 with p replaced by Dp. Its dual polynomial has coefficients

    chi(j)psi(j)j^(-1/2-it)

times a common Mellin weight of uniformly bounded total variation, an exact common unit phase, and the normalized Gauss factor `tau(chi bar(psi))/sqrt(Dp)`. The p dependence still separates through unit Mellin twists. The D dependence is known and common to the entire family. The allowed dual length is

    H_M = C P^(kappa/8) D P T_*/M.                      (11.1)

All the Fourier symbol and tail arguments remain uniform. This is why one cannot make the same deduction for profiles whose coefficients are separately selected for psi.

### Exact root cancellation

Let a be the parity of psi and b the parity of chi psi. For any primitive character theta of parity j and conductor q,

    tau(bar(theta))/sqrt(q)=i^j epsilon_theta^-1.

Since chi is real, the three Poisson Gauss factors multiply the original root factor as follows:

    epsilon_psi^2 epsilon_(chi psi)
     * [tau(bar(psi))/sqrt(p)]^2
     * [tau(chi bar(psi))/sqrt(Dp)]
       = i^(2a+b).                                     (11.2)

Negative dual indices contribute their exact parity factors. Thus no hyper-Kloosterman or additive trace remains after all three completions. The gamma/branch multiplier and scalar phases remain, depend on p,t and parity, and have modulus one. They are never replaced by their absolute value when defining the signed main.

### The enlarged legal length region

Group the remaining ordinary character polynomials as

    C3_psi = (M H)_psi * dualH_psi * dualR_psi * dualS_psi,
    D3_psi = c-box_psi.                                 (11.3)

The corresponding uninflated lengths are

    C3_length <= C U D P^3 T_*^3/(M R S),
    D3_length <= C N.

Thus, for a fixed kappa>0, it is enough that

    C N <= P^(2-2 kappa),
    C U D P^3 T_*^3/(M R S) <= P^(2-2 kappa).            (11.4)

The three P^(kappa/8) tail inflations leave both final lengths below P^2. Dyadic constants are absorbed in the fixed C. On resonance, the two sides have approximately equal lengths: the relation `N R S M/u ~= Dp^3(t/(2pi))^3` identifies both with N, up to the actual u support and the stated fixed margins.

Uniformly over the entire first profile and A support, `U/M<=D^20 P^.0005`. Consequently the explicit sufficient exponent region is

    R S >= P^(1.0005+3 kappa),                          (11.5)

eventually, for near boxes satisfying the first condition of (11.4). The real conditions are (11.4); (11.5) is only a convenient sufficient description. At `R=S=P^.6`, the leading scale is `N=P^1.8`, but the actual resonance and whole-polynomial maxima retain the fixed profile-width factor `P^.0005` and the displayed D, T_*, and M factors. Thus `P^1.8` is only a leading-scale illustration: the exponent can be `1.8005+o(1)`, before the fixed tail inflation, and both exact inequalities (11.4) must still be checked. The earlier D polynomial has leading length `P^2.3025`, above the second-sieve endpoint.

As before, apply Cauchy directly on Psi1 and enlarge only the two nonnegative square sums. No bad-family estimate is required for this comparison. Root cancellation does not authorize replacing Psi1 by the full family in a signed evaluation.

### Improved sparse error budget

The coefficient of C3 has envelope tau6, hence

    E(C3)<=C(1+log P)^36=O(L^324).

Now the error on the D3 side is just `bar_eta*nu_tail`, without the extra H convolution. The two-factor coefficient Cauchy inequality gives

    E(E_X)<=C [sum |eta(q)|^2 tau2(q)/q]
                [sum_(e>X)nu(e)^2 tau2(e)/e].            (11.6)

The first factor is O(L^72), since `tau2^3<=tau8`. For the second,

    sum nu(e)^2 tau2(e)/e
      <= [sum nu(e)^2/e]^(1/2)
         [sum nu(e)^2 tau2(e)^2/e]^(1/2)
      <= C L^(-2011/2) L^72 = C L^(-1867/2),

using `nu^2 tau2^2<=tau16`. All e are below P^2 by (11.4), so the literal source sparse theorem applies. Therefore

    E(E_X)<=C L^(-1723/2).

The normalized per-box comparison error is

    O(a^-1 L^[77+324/2-1723/4])
      =O(a^-1 L^(-767/4)).                             (11.7)

Summing the O(L^36) boxes gives

    J_eligible[c_X]-J_eligible[chi*alpha]
       =O(a^-1 L^(-623/4))+O(a^-1 P^-K).                (11.8)

The exact signed form and all source normalizations are retained. The right inequality (11.8) is an absolute error estimate; it supplies no sign for either main.

For reference, the mixed divisor main has D3 coefficient envelope tau2 and energy O(L^36), so its available absolute bound is `O(a^-1 L^257)` per box and `O(a^-1 L^293)` over the region. These powers are deliberately explicit. They are not a constant-scale sign estimate.

### Exact remaining question after the strongest reduction

One may replace the eligible set in Section 8 by the larger set (11.4), define its complementary J_rest accordingly, and use error (11.8). The missing proposition is still the one-sided bound (8.2), now for an ordinary, parity-weighted, good-family Dirichlet-polynomial pairing with coefficients `chi*alpha`, plus the original longer complement.

Even after (11.2), full-family orthogonality would involve congruences between potentially P^2-long products, both parity cases, and a genuine Psi2 correction. It is not merely the equality diagonal. Ordinary second-sieve control is only an L-polynomial upper bound. The original inverse convolution `upsilon*1*chi=delta_1` is also exact, but its two smooth/profile masks and the fixed d cutoff prevent replacing C3 by a delta coefficient. A proof of the resulting signed main and complementary contribution at actual m_H precision is the next independent arithmetic requirement. No constant gain is claimed here.
