# A half-norm main term for the actual completed right mean

2026-10-03. Source-level mathematical proof, independently accepted at the scope stated in [the review](INDEPENDENT_REVIEW.md). This is not a Lean certification. The original assumption `(A): L(1,chi)<L^-2022`, final exponent-2024 target, real primitive conductor-D character, actual families, compatible shifts, branch, prime window, first R5 profile, both profile masks, finite mollifier cutoff and D-deletion are unchanged.

## 1. Result

The principal Ramanujan row captures **one half** of the actual squared norm. It neither cancels nor captures the whole norm. More strongly, the whole completed right mean has the same half-norm real part:

    Re J_right^infinity = Im R_D = (1/2)m_H + o(1),
    Im R_pr = (1/2)m_H + o(1),
    R_np = o(1).                                             (1.1)

The equality signs in the first line mean equality up to the displayed o(1). The last assertion is complex, not inferred from equality of real or imaginary parts: Section 7 gives its separate complex source chain.

For the exact fixed profile in the [public interface](../signed_phase_refinements/INTERFACE.json), this evaluates the signed constant as

    lambda/2 = (8000/pi) integral_0^1 |F0'(u)|^2 du
                      +(11 pi/500) integral_0^1 |F0(u)|^2 du > 0. (1.2)

Here `m_H=lambda+o(1)` is the existing actual norm result. Neither the original AFE nor a hypothetical principal character is used to assign (1.1).

The main new arithmetic input is a paid replacement of the **actual finite** mollifier convolution by the original P7 coefficient, first at the level of finite integer coefficients and then in two legitimate means. The replacement is not an unqualified identity `M L Lchi=1`. Its cutoff defect has support above D^20 and the available weighted sparse saving; its D-deletion has an exact D-supported formula and a separate D-power bound.

This does not prove a strict gain. With the independently accepted sparse-long reduction, the remaining signed target becomes precisely

    Re Delta_rho,high <= (1/2-epsilon)m_H + o(1),              (1.3)

for fixed epsilon>0. The exact high-rho term and its original label condition `2K>P^.99` remain present. No favorable bound for it is proved here. In particular, the half in (1.1) is not itself the final saving.

## 2. Original objects and the finite coefficient defect

Use

    L=log D, B=log P=L^9, W=L^400, t0=L^519, T0=2pi t0,
    X=D^20, V=P^(201/400), Y=floor(P^(151/100)),
    h(n)=chi(n) f(log(n)/B), w_p=(p t0)^beta3.

The actual real f is supported on `[251/500,201/400]`, is bounded by one, and is the fixed first bump. The weight w_p has modulus one and has the **positive** beta3 exponent. The normalizer is the actual `a Mcal`, with `a>1/2` and `Mcal=sum_actual_primes p>=P^2/(4L^77)`.

Let convolution always mean finite Dirichlet convolution on positive integers. Set

    nu=1*chi, upsilon=mu*(mu chi),
    kappa=mu*power_beta1*power_beta2*power_beta3,
    g=kappa*h,
    U_X(d)=upsilon(d) 1_(d<=X,D does not divide d),
    q_tail=(upsilon 1_(d>X,D does not divide d))*nu,
    q_D=(upsilon 1_(D divides d))*nu.                         (2.1)

The original completed coefficient is

    b=U_X*h*(chi*power_beta1*power_beta2*power_beta3).

Since `nu*kappa=chi*power_beta1*power_beta2*power_beta3` and `upsilon*nu=delta_1`, associativity on each finite divisor set gives exactly

    U_X*nu=delta_1-q_tail-q_D,
    b=g-e_tail-e_D,
    e_tail=q_tail*g, e_D=q_D*g.                              (2.2)

The partition of the upsilon index in (2.2) is disjoint: it consists of `d<=X,D∤d`, `d>X,D∤d`, and **all** `D|d`. This is why q_D uses the full deleted sequence while q_tail still excludes D-multiples. No original mask is silently changed. In particular h stays inside g and the opposite h(m) stays in every mean below. The total cutoff k<=Y is applied only after these exact coefficients are formed.

The source prime-power values are

    upsilon(p)=-(1+chi(p)), upsilon(p^2)=chi(p),
    upsilon(p^j)=0 for j>=3.

The source `lemma36_absolute_convolution_le` therefore gives

    q_tail(n)=0 for n<=X,
    |q_tail(n)| <= nu(n) tau2(n).                            (2.3)

It is unnecessary for q_tail to equal the earlier rho_X coefficient. It need not: its cutoff is on the upsilon index. The accepted sparse energy proof is universal for any sequence satisfying (2.3), as is explicit in Section 3 of the sparse-long independent review.

### Exact D-deletion

The following formula holds for every positive n and actual D>=2:

    if D is not squarefree: q_D(n)=0;
    if D is squarefree:     q_D(n)=mu(D) 1_(rad(n)=D).       (2.4)

At any p|D, chi(p)=0, so upsilon has local polynomial `1-z` and nu has local series `(1-z)^-1`. If p^2|D, every deleted upsilon coefficient is zero, proving the first case. If D is squarefree, forcing every p|D into the upsilon divisor contributes `-z/(1-z)` at each such prime. At every p∤D the unrestricted upsilon and nu factors cancel exactly. Thus all primes of n must be in D, every p|D must occur at least once, and the coefficient is mu(D). This proves (2.4) without assuming that the nonprincipal exceptional chi has conductor one. With rad(1)=1, (2.4) also says q_D(1)=0 because D>=2. Index zero is excluded throughout.

For j=2,3, the geometric Euler sums and `tau_j(Du)<=tau_j(D)tau_j(u)` yield

    sum_n |q_D(n)| tau_j(n)/n
      <= tau_j(D)/D * product_(p|D)(1-1/p)^(-j)
      <<_j D^(-1/2).                                      (2.5)

For example, in the squarefree case the numerator is at most `(j 2^j)^omega(D)`, which is `O_j(D^1/2)` by separating finitely many small primes. The same estimate holds with `|q_D|^2`, since its values have modulus zero or one. Thus the deletion is paid independently; it is not subsumed into a sparse bound whose starting endpoint is D^2.

## 3. The weighted sparse estimate applies literally

The accepted sparse-long review proves, from the original arbitrary-endpoint L3.1 bounds, that for every Y<=P^4

    sum_(D^2<n<=Y) nu(n)/n << L^-2013,
    sum_(n<=Y) nu(n)/n << L^2.

For any sequence q supported above X and bounded by `nu tau2`, its proof gives

    sum_(n<=Y) |q(n)|^2/n << L^-1997,
    sum_(n<=Y) |q(n)|^2 tau3(n)/n << L^(-1853/2).          (3.1)

For clarity, the second assertion is not transferred on the basis of notation. The proof uses only those two support/majorant facts: `nu^2 tau2^2<=nu^{*9}` pays the unweighted tail because X>D^18. Above D^108, `nu^2 tau2^2 tau3<=nu^{*54}` and the positive convolution union bound give L^-1907. Between X and D^108, Cauchy between the unweighted estimate and `nu^2 tau2^2 tau3^2<=tau144` gives `L^(-1997/2)L^72=L^(-1853/2)`. The latter bound dominates the high part. All these are valid also for q_tail in (2.1).

The shifts are purely imaginary. Consequently `|kappa|<=tau4` and `|g|<=tau5`. For arbitrary q and g, divisor Cauchy and submultiplicativity of tau2 give the finite energy inequality

    sum_(k<=Y) |(q*g)(k)|^2/k
      <= [sum_(r<=Y)|q(r)|^2 tau2(r)/r]
         [sum_(v<=Y)|g(v)|^2 tau2(v)/v].                  (3.2)

No infinite polynomial appears in (3.2). Since `tau5^2 tau2<=tau50` and `sum_(n<=Y)tau50(n)/n<<(log Y)^50<<L^450`, (2.5), (3.1), and tau2<=tau3 yield

    E_tail := sum_(k<=Y)|e_tail(k)|^2/k << L^(-953/2),
    E_D    := sum_(k<=Y)|e_D(k)|^2/k << D^(-1/2)L^450.     (3.3)

The first exponent is `450-1853/2=-953/2`. It is small enough after the actual P^2/Mcal normalization, not just in an abstract coefficient norm.

## 4. Whole completed-right comparison, with no crossing of quotient poles

Define Theta_H to be **the original** P7 `Theta_1(h,h)` on its original upward safe-right segment Re(s)=3/2. Its scalar is exactly

    -i (p t0)^beta3 Z_psi(s)^(-1)
       product_j L(s+beta_j,psi)/L(s,psi).

The h sequence is admissible with coefficient bound one: it is zero for n>=P^.5025, and `P^.5025<P T^-2` eventually for the paper's `T=exp(L^1.1)`. Its reality includes chi's zero values.

Here is the legal order of the comparison.

1. For J_right^infinity use the already accepted total-index truncation k<=Y and branch freezing from the completed-right report. The branch-free finite scalar is `-i w_p Z_psi(s)^-1`; the total branch error is `O(a^-1 L^-11/2)`. The original coefficient b and both h masks are retained.
2. On the safe line Re(s)=3/2, expand Theta_H into its absolutely convergent g coefficient series and truncate its **total** index at the same Y. For omitted k and actual m, `k/m>P^1.0075`, whereas `pt/(2pi)=P^(1+o(1))`. On a fixed right line Re(s)=R, the absolute tail is bounded by `P^(1.01-.0075R)L^(C_R)`. Choosing R=2000 gives a power saving stronger than P^-10 eventually. The horizontal edges are fixed P powers times `exp(-cL^10)`. All full g series used here have Re(s)>1.
3. Subtract the two finite retained polynomials using (2.2), then move **only this finite coefficient difference** to Re(s)=1/2. The reciprocal Z factor is analytic on this positive-height rectangle and has modulus one on the center line. No full kappa quotient is moved through the zeros of L(s,psi). In particular no principal-value or hidden residue assertion is being made on Re(s)=1/2.
4. Apply the actual P^2 second sieve to the finite defect polynomial and the opposite H polynomial separately. Their lengths are Y<P^2 and V<P. The coefficients are shared across primes; t supplies only unit twists. The actual good subset can be bounded by the whole primitive family.

The normalized absolute finite defect is at most

    C a^-1 (P^2/Mcal) sqrt[(E_tail+E_D) L^9]
      << a^-1 L^(-627/4) + a^-1 D^(-1/4)L^307.           (4.1)

The source Gaussian on the critical line is positive and has mass at most one over the original height segment. Thus (4.1) also pays its integral. The arithmetic for the first exponent is `77+9/2-953/4=-627/4`; the deletion exponent before harmless rounding is `77+9/2+225=613/2`.

We have proved the **complex** comparison

    J_right^infinity = Theta_H/(a Mcal)
       + O(a^-1 L^-11/2) + O(a^-1 L^(-627/4))
       + O(a^-1 D^(-1/4)L^307) + O(a^-1 P^-10)
       + O(exp(-cL^10)).                                 (4.2)

All constants and the fixed R are chosen before D and the actual character. The existing b-energy argument is used only at its accepted branch-freezing scope. The new coefficient replacement has its own explicit sparse and deletion payments.

## 5. A direct bound for the principal projection

The principal comparison can also be proved without a new nonprincipal estimate for arbitrary b. For any finite q define

    R_pr(q*g;Y) = (a Mcal)^-1 sum_p w_p sum_m h(m)/(m phi(m))
                      sum_(k<=Y)(q*g)(k)c_m(k)Delta(k/(pm)).

Take `sigma=1+1/B`. The exact source Mellin kernel has the uniform elementary bound

    |Delta(x)| <= C L^260 x^(-sigma), x>0.                (5.1)

Indeed shift its Mellin integral from 3/2 to sigma within the fixed positive strip. No gamma pole is crossed. Uniform Stirling bounds give `|Theta*(sigma+it)|<< (1+|t|)^(sigma-1/2)` for positive t, with extra exponential decay for negative t. Multiplying by the actual `W^-1 exp(-((t-T0)/(2W))^2)` Gaussian and integrating gives `O(T0^(sigma-1/2)+W^(sigma-1/2)+1)=O(L^260)`. The small real-line Gaussian multiplier is uniformly bounded. This proof is from the exact kernel and makes no stationary-phase sign assumption.

The elementary Ramanujan and totient identities give

    |c_m(k)| <= sum_(d|(m,k)) d,
    phi(du)>=phi(d)phi(u),
    sum_(u<=z) 1/phi(u) << 1+log z.

For the last inequality use `u/phi(u)=sum_(r|u)mu(r)^2/phi(r)` and the convergent product `sum_r mu(r)^2/(r phi(r))<infinity`. Since `m^(sigma-1)<=V^(1/B)<2`, it follows that

    sum_(m<=V) m^(sigma-1)|c_m(k)|/phi(m)
       << B sum_(d|k)d/phi(d) <= B tau3(k).              (5.2)

The last inequality uses `d/phi(d)<=tau2(d)` and `1*tau2=tau3`. It loses only powers of L, including on the rows with nonunit k or large gcd. There is no hidden power of V or P in this principal-projection bound.

Insert (5.1)-(5.2), then expand k=r v ell in q*kappa*h. Submultiplicativity of tau3, `|h|<=1`, and `|kappa|tau3<=tau4 tau3<=tau12` give

    |R_pr(q*g;Y)|
      << a^-1 L^(260+9+27+108)
                    sum_(r<=Y)|q(r)|tau3(r)/r
       = a^-1 L^404 sum_(r<=Y)|q(r)|tau3(r)/r.            (5.3)

The two Dirichlet-series factors are at most `zeta(sigma)^3<<L^27` and `zeta(sigma)^12<<L^108`. The prime factor is bounded because

    Mcal^-1 sum_p p^sigma <= max_p p^(1/B)=O(1).

This preserves the actual prime normalization. Dropping masks here occurs only in nonnegative upper bounds after the exact masked coefficient identity.

For q_tail, Cauchy and (3.1) give

    sum_(r<=Y)|q_tail(r)|tau3(r)/r
      <= [sum|q_tail|^2 tau3/r]^1/2 [sum tau3/r]^1/2
      << L^(-1853/4+27/2)=L^(-1799/4).

For q_D, use (2.5). Hence

    R_pr(b;Y)-R_pr(g;Y)
       = O(a^-1 L^(-183/4)) + O(a^-1 D^(-1/2)L^404).     (5.4)

This is a bound on the actual complex principal difference. No positivity of b or c_m(k) has been assumed.

## 6. Literal P7 attachment and the half-norm normalization

Remove the artificial total cutoff in the baseline R_pr(g;Y). The bound `|c_m(k)|<=phi(m)` and the same fixed safe Mellin line Re(s)=R give

    |R_pr(g;infinity)-R_pr(g;Y)|
       << a^-1 P^(.51-.0075R)L^(C_R),                   (6.1)

using `#primes/Mcal<=1/P`. Again R=2000 pays O(a^-1 P^-10).

For every m,k>0, set d=gcd(m,k), m=dq, k=dell. The exact identity

    c_m(k)/phi(m)=mu(q)/phi(q), (q,ell)=1,

rewrites the untruncated baseline as

    R_pr(g;infinity)=(a Mcal)^-1 sum_p w_p
       sum_d 1/d sum_q h(dq)mu(q)/(q phi(q))
                          sum_((ell,q)=1) g(dell)Delta(ell/(pq)).

The inner expression is **exactly** `proposition71PrimePrincipalMean D p c h h`, or source (7.16), with its original kappa and admissible h,h. Absolute convergence follows on a positive safe Mellin line; the short indices are finite. Therefore

    -i R_pr = PrincipalMean_P7(h,h)/(a Mcal) + o(1).       (6.2)

The source `proposition71_original_principal_reduction` proves the complex comparison

    Theta_H = PrincipalMean_P7(h,h) + o(Mcal)             (6.3)

under the original (A), with every bounded-sequence and support hypothesis now literally satisfied. This applies P7 only after (5.4), not to the tau7 original b. No P14 conductor substitution or Lemma15.1 specialization is used. The repaired Lemma15.1 concerns a different coefficient and is unnecessary here.

The original Lemma8.1, applied to the real h,h and the same actual branches, gives

    sum_(Psi1,rho) C_rho |H_psi(rho)|^2 omega(rho)
       = Theta_H + conjugate(Theta_H) + o(Mcal).

The left side divided by a Mcal is the original m_H. Thus, using a>1/2,

    Re(Theta_H/(a Mcal))=(1/2)m_H+o(1).                  (6.4)

Equations (4.2), (6.2)-(6.4) prove the two half-norm statements. The `-i` sign and the positive prime weight are both retained: `Re(-i z)=Im z`. This is the source of the imaginary-part evaluation, not a Ramanujan positivity claim. If desired the complex leading functional can be retained as the actual P7 residue arithmetic mean: the proved `proposition71_principal_residue_little_o` identifies PrincipalMean with its three source residues, with the same prime phase and S_j(h,h). No printed approximate residue constant is needed to obtain the half-norm result.

## 7. Why the nonprincipal remainder is genuinely paid here

The accepted completed-right report supplies the complex identity

    J_right^infinity=-i R_D+o(1), R_D=R_pr+R_np.

Combine it with the complex (4.2), (6.2), and (6.3):

    -i R_np
       = J_right^infinity-(-i R_pr)+o(1)
       = [Theta_H-PrincipalMean_P7(h,h)]/(a Mcal)+o(1)
       = o(1).

This proves complex R_np=o(1). Equality of the two signed halves alone would prove only Im R_np=o(1); that weaker inference is not used. Nor is a general tau7 version of P7 or P14 assumed. The original b is compared in both means to the genuinely admissible old row by explicit quantitative defect bounds.

The remaining whole signed expression is consequently

    Im R_D + Re Delta_rho,high
       = (1/2)m_H + Re Delta_rho,high + o(1).

There is still no independent arithmetic proof of (1.3). The old AFE diagnostic, if combined afterward with these results, would require the high-rho real part to supply the other half under (A). That observation is diagnostic only and is not used in the proof above or as evidence for a strict inequality.

## 8. Source ledger and verification boundary

Principal accepted inputs:

* [Completed-right proof](../completed_right_mean/PROOF.md) and [independent review](../completed_right_mean/INDEPENDENT_REVIEW.md): original SHA256 respectively `46a3697d7dce3228f84817dafefbc8d9fc34e19b1e0e63323853d2df3d735670` and `f2ec027691f680cd5f2c6de3ff1993fd0cdad2edf691069ac3a2a5137b42ecaf`.
* [Sparse-long independent review](../sparse_long_reduction/INDEPENDENT_REVIEW.md), Section 3: the weighted sparse proof at the universal support/majorant scope described above.
* Unchanged [public interface](../signed_phase_refinements/INTERFACE.json): exact first bump, lambda, a, and actual m_H normalization. Its actual-Gram input is given in the [Gram derivation](../actual_gram_bridge/DERIVATION.md) and [independent review](../actual_gram_bridge/INDEPENDENT_REVIEW.md).
* `Lemma36CoefficientMajorant.lean`: local upsilon values and absolute convolution majorant.
* `Lemma83Definitions.lean`: original kappa as mu convolved with the three shifts.
* `Lemma53Kernels.lean`: exact Delta, Theta*, and normalized Gaussian.
* `Lemma33.lean:72`: actual P^2 second mean.
* `Proposition71PrincipalSplitAttachment.lean`, `Proposition71OriginalSevenEleven.lean`: exact principal row, full prime phase, actual nonprincipal estimate and complex Theta-to-principal reduction.
* `Lemma81.lean`, `Lemma81Objects.lean`, `Lemma81KernelReplacement.lean`: actual discrete norm, conjugate-and-swap formula, safe-right Theta and its scalar.

The public primary source is [Zhang, arXiv:2211.02515v1](https://arxiv.org/html/2211.02515v1), especially Sections 3, 7 and 8. The report derives new estimates from the actual checked repository inputs; it does not treat the paper's claimed final contradiction as an input. The current repaired 15.1 has been inspected solely to verify that no transfer from its different coefficient is needed.

`check_author.py` uses only the Python standard library. It checks the exact coefficient partition, convolution identities and D-deletion formula for genuine quadratic characters in small conductors, Ramanujan gcd normalization, elementary divisor envelopes, and the rational exponent budgets. `verify_bundle.py --repo PATH` separately checks the pinned repository sources and public dependencies. The small characters are used only for universally valid finite algebra and are **not** claimed to satisfy (A). There are no numerical experiments with a purported exceptional character, no parameter fitting, and no compiler verification. The analytic conclusions in Sections 3-7 are covered by the [independent source review](INDEPENDENT_REVIEW.md); finite checks alone do not certify them. Original and public artifact hashes are distinguished in `PROVENANCE.json` and `SOURCE_HASHES.json`.
