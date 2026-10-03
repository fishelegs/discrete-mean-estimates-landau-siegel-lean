# Independent review: split-prime kernels and complete normalization

2026-10-03. **ACCEPT at source level for the exact reductions, legal masks, cited pointwise bounds, and conditional full-budget comparisons. No signed half-norm estimate is proved.**

Reviewed historical author report SHA256 `3cf78b90d64bece449a21465eb46123c983791b46d43aab01c78ff59f85d24f5`, together with its literature file, checker and manifest. All twelve historical author-manifest entries matched at curation; their identifiers and hashes are retained in [AUTHOR_SOURCE_MANIFEST.json](AUTHOR_SOURCE_MANIFEST.json). The squarefree-core appendix was already independently accepted and is outside this review; it has not been re-proved here.

The main normalizations are correct. For a once-occurring selected prime, two completions cost `G_2(Y/P)` times the relative prime saving; four completions cost `G_4 Y` times that saving. Here `G_2=P^(9/40000+o(1))` and `G_4=P^(9/20000+o(1))` for the stated finite cutoffs. The candidate's common `P^.001` allowance safely covers these factors and the named fixed-conductor costs. The exact principal rows have an extra `P^-1` relative to the oscillatory prefactors. The literal actual-family subtraction remains unestimated.

The potentially dangerous Fourier-mask step is valid in this version: its Fourier twists enter a **bilinear theorem with arbitrary separate coefficients**. The pointwise prime branch instead uses literal intervals and partial summation. It must not be rewritten as an application of the same prime theorem at unrestricted Fourier-modulated frequencies.

Acceptance is relative to the previously accepted localization, exact completion-symbol and tail inputs. This is not a transitive formal-verification certificate or an exceptional-character example. The independent mathematical checks are separate from the author implementation.

## 1. Exact arithmetic partition

At each integer, finite convolution gives `nu*upsilon=delta_1`. Thus `c_X+rho_X=delta_1`. For a split prime `ell>X` and `(ell,w)=1`, every divisor `e<=X` of `ell^j w` divides `w`. Multiplicativity therefore gives

    rho_X(ell^j w)=-upsilon(ell^j)c_X(w)
                   =2c_X(w), -c_X(w), 0

for `j=1,2,>=3` respectively. This is exact, including the sign at a square. The majorant `|c_X(w)|<=nu(w)tau_2(w)<=tau_4(w)` follows by the same unrestricted nonnegative convolution bound used for rho; restricting the divisor sum only decreases its absolute majorant.

Selecting the largest split prime is unique, with its valuation retained. Alternatively, in the residual squarefree-kernel region select the largest split prime of odd valuation above X. A nonzero rho coefficient forces that prime's valuation to be exactly one. Its remaining odd-part condition is `ell*s(w)>P^.15`, because `(ell,w)=1`. The prime-order condition, new selector, dyadic support and `ell>X` are intersections of intervals for fixed remaining indices. Excluding the finitely many prime divisors of w changes a prime sum by at most `omega(w)=O(log P)`.

If no odd split prime exceeds X, use the short-cutoff expansion, without deleting `e<=X`:

    rho_X(v)=-sum_(ef=v,e<=X)nu(e)upsilon(f),  v>1.

For each nonzero term, the factorization `f=r t^2 b` in the candidate is unique. Local upsilon factors are `1-z`, `1-z^2`, and `(1-z)^2` at ramified, inert, and split primes, respectively. Hence

    upsilon(f)=mu(r)chi(t)(-2)^omega(b),

with all the stated squarefreeness and coprimality restrictions. There is no condition `(e,f)=1`. The implication `s(v)<=s(e)r b<=D^21 b` is valid termwise. Thus the new selector forces `b>P^.15/D^21`; in the no-large-odd-prime branch all primes of b are at most X, and therefore at most any fixed `P^sigma` eventually. This validates the advertised smooth-prime case without assuming that a large product contains a large individual prime.

## 2. Gauss kernels, roots and corrections

For `p` odd and `p∤cn`, expand the Gauss sum and use parity orthogonality on **all** characters. The two residue constraints are `xc/n=+1` or `-1` for `tau(psi)`, and `c/(xn)=+1` or `-1` for `tau(bar psi)`. Removing the principal character, whose Gauss sum is `-1`, gives exactly

    sum_(primitive, parity a) tau(psi)psi(c)bar psi(n)
       =(p-1)/2 [e_p(n/c)+(-1)^a e_p(-n/c)]+1_(a=0),

    sum_(primitive, parity a) tau(bar psi)psi(c)bar psi(n)
       =(p-1)/2 [e_p(c/n)+(-1)^a e_p(-c/n)]+1_(a=0).

When `p|cn`, both left sides are zero. The entire kernel must be set to zero, including its principal correction, before evaluating an inverse. The candidate uses this convention correctly.

Let `a` be psi's parity and `b` the parity of `chi psi`. Put `g=tau(bar psi)/sqrt(p)` and `h=tau(chi bar psi)/sqrt(Dp)`. Since `epsilon_psi*g=i^a` and `epsilon_(chi psi)*h=i^b`, the original root product yields

    two completions (one pure, one chi): i^(a+b) epsilon_psi;
    three completions (two pure, one chi): i^(2a+b);
    four completions (three pure, one chi): i^(2a+b) g.

Consequently the first and third rows give the additive and reciprocal kernels, with exactly their `1/sqrt(p)` normalization; the middle row is a congruence kernel. Substituting `n=ell*w*survivors` produces a linear or reciprocal first power of ell. Two pure completions instead leave `epsilon_(chi psi)`; CRT introduces `psi(D)`, so the additive argument becomes `n/(Dc)`. Completing two pure and two chi factors introduces `bar psi(D)` in the remaining conjugate mixed Gauss sum, giving reciprocal argument `c/(Dn)`, up to the retained unit scalar. Their different conductor costs belong in `G_r`.

The quadratic character modulo p is one of the original nonprincipal characters and remains in these identities. There is no squaring-map loss. Every character actually transformed by Poisson is primitive and nonprincipal at conductor p or Dp, so its zero Fourier term vanishes. The artificial principal character used in orthogonality is only an algebraic correction.

The actual good family is handled by the finite identity `Psi1=all primitive-Psi2`, at the level of the complete weighted expression. Reopening [Proposition71OriginalFamilyExtension.lean](../../ZhangLS/Spec/Proposition71OriginalFamilyExtension.lean) confirms that its analytic family-extension theorem concerns the original admissible Theta/C integrand; it does not provide a bound for an arbitrary high-rho selector. Retaining `T_bad` is essential. No closure of Psi1 under conjugation or inversion has been assumed.

## 3. The frequency and changing-coefficient issue

The once-occurring prime branch can be estimated without finite Fourier expansion of its prime-order mask. At fixed remaining indices, its sharp selectors give an interval inside `(Q,2Q]`. Vaughan's additive theorem is uniform in a prefix endpoint. Baker's proof explicitly treats `(x,x']`, `x'<=2x`, uniformly. Fouvry–Shparlinski explicitly states that prefix sums have the same bounds; alternatively its proof works with the corresponding prefix von Mangoldt sum. Differences give arbitrary endpoints inside the dyadic box. Fixed-power margins at the stated range boundaries absorb fixed support factors and the replacement p by Dp.

The smooth weights and `ell^(it+i xi)` have total variation `O(1+|t|+|xi|)` after the common `Q^-1/2` factor is taken out. Integrating against the original Schwartz Mellin measure pays its first absolute moment. The selected completion symbols do not introduce a new ell-dependent Mellin frequency: they depend on their own dual indices. Thus this step costs only a fixed power of L. The omitted primes cost `O(log P)` and are included in B.

The balanced product branch is different. Order the distinct primes of b increasingly, and let a be the shortest initial product reaching Z. Then

    Z<=a<ZH,  S/(2ZH)<d<2S/Z,
    a/Pplus(a)<Z,  Pplus(a)<Pminus(d).

The condition `ZH<S/2` ensures `d>1`. Conversely these conditions pick that unique initial product. The order implies `(a,d)=1`; the restrictions `(t,a)=(t,d)=1` are separate. All coefficients in a and d factor exactly.

For `J=ceil H+1`, `m=2J+1`, expand the cyclic indicator of residues `1,...,J`. Its Fourier coefficients satisfy

    |gamma_h| <= min(J/m, 1/(m|sin(pi*h/m)|)),
    sum_h |gamma_h|=O(log m).

Since `Pminus(d)-Pplus(a)` lies between `-(J-1)` and `J-1`, the expansion represents the strict order with no wraparound error. Each summand multiplies the a coefficient by `e_m(-h Pplus(a))` and the d coefficient by `e_m(h Pminus(d))`. Bourgain–Garaev's bilinear theorem permits these arbitrary separate unit twists uniformly. Coefficients may also change with p, c, e, r, t, x and every frozen spectral parameter: the theorem is applied separately at each fixed choice, before absolute summation. No common-coefficient large sieve is invoked here.

This justification would fail for a pointwise prime theorem that allows only `e_p(A ell)` or `e_p(A/ell)`. A Fourier order twist can produce additive frequency `A/p-h/m` (possibly of conductor pm), or the mixed phase `e_p(A/ell)e_m(-h ell)`. Uniformity in the old numerator A does not cover those frequencies. Likewise the sharp product cutoff's logarithmic Fourier representation has bounded L1 norm, but cannot be charged only that norm when a prime estimate requires an extra first moment in its Mellin frequency. The candidate does not make either transfer. Future arguments must retain direct interval/partial-summation control, or prove a theorem for the actual modulated phase.

The squarefree selector also separates legally. For fixed `g=s(er)`, let `g_a=(g,a)`, `g_d=(g,d)`. Their disjoint divisor choices cost at most `tau_3(er)=D^o(1)`. The remaining condition is exactly

    ad>P^.15*g_a^2*g_d^2/g.

For integer `n=ad` in the finite support, interpolate the step between the two adjacent logarithmic integer arguments. The transition width is at least a constant times `1/M`, with `M` a common fixed-constant enlargement of the actual maximum integer support. A smooth compactly supported interpolant has `||H||_1=O(log M)`, `||H'||_1=O(1)`, `||H''||_1=O(M)`. Integrating the bounds `min(log M,|xi|^-1,M|xi|^-2)` gives `||Hhat||_1=O(log M)`. Its exact Mellin representation supplies separate factors `a^(i xi)d^(i xi)` with no truncation. These enter arbitrary bilinear coefficients after completion, so no new Poisson-height cutoff is needed. A fixed enlargement of M, if a dyadic support crosses P^4, changes none of these estimates.

## 4. Full normalization and exact required savings

Use the normalizer `a_0>1/2` in this section to avoid confusing it with a bilinear index. Write

    C_r <= constant * E_r P^(r-3)Y,
    E_r=D^(j-1)F^r T_eff^r/T0^3,
    G_r=sqrt(E_r),  Y=KU.

The fixed localization constants can be left explicit. For r=2,4 use the root choices above. The Gauss oscillatory kernel is `O(sqrt P)`, and the exact prime-mass ratio is `#actual primes/Mcal<=P^-1`. The c sum costs `sqrt(C_r)` times a log power. For a once-occurring selected prime, the other uncompleted variables cost `sqrt(Y/Q)`, and the weighted prime sum costs `B(Q)/sqrt Q`. Thus

    |oscillatory row| << a_0^-1 L^C sqrt(C_r Y/P)*B(Q)/Q
                       << a_0^-1 L^C G_r Y P^((r-4)/2)*B(Q)/Q.

The principal row has kernel `1/sqrt p`, so its budget is

    |principal row| << a_0^-1 L^C P^-3/2 sqrt(C_rY)
                     << a_0^-1 L^C G_r Y P^((r-6)/2).

These recover the candidate's `(Y/P)B/Q`, `Y B/Q`, `Y/P^2` and `Y/P` factors, with the whole completed-polynomial length present. Counting parities, signs, original refined boxes, new dyadic subdivisions and bounded Mellin measures adds log powers or fixed constants only.

For exact exponent accounting set `y=log_P Y`, `g_r=log_P G_r`, and let `ell_r` be any **additional** positive-power loss outside G and the actual relative saving. For a target `O(P^-zeta)`, a fixed positive margin is needed in the following comparisons:

| Branch | Required relative saving exponent |
|---|---|
| Two completions, selected prime to exponent one | `s > y-1+g_2+ell_2+zeta` |
| Four completions, selected prime to exponent one | `s > y+g_4+ell_4+zeta` |
| Two completions, bilinear additive product | `s_AB > y-1+g_2+ell_2+zeta` |
| Four completions, bilinear reciprocal product | `delta > y+g_4+ell_4+zeta` |
| Two-completion principal row, with a hypothetical further gain h | `h > y-2+g_2+ell_2+zeta` |
| Four-completion principal row, with a hypothetical further gain h | `h > y-1+g_4+ell_4+zeta` |

For sup-norm versions of the bilinear theorem, dividing each divisor-bounded coefficient by `P^eta` adds `2eta` to `ell_r`. Mask log norms do not add a fixed power. The gcd partition and conductor costs are explicitly `P^o(1)` and must consume a reserved positive margin. For a split-prime bound derived from a pure-phase theorem, its `sqrt D` loss belongs either in the actual B or in `ell_r`, never both.

The finite-cutoff contributions are more precise than the candidate's convenient .001:

    g_2=9/40000+o(1)=.000225+o(1),
    g_4=9/20000+o(1)=.000450+o(1).

This follows from `F=P^(1/8000)` and `T_eff=P^(1/10000+o(1))`. Thus `g_2+ell_2<=.001` and `g_4+ell_4<=.001` eventually for the named subpower costs, before the separately displayed `2eta`. The unused allowances are .000775 and .000550. No second .001 should be added for the same completions. Equivalently, retain E_r exactly throughout.

For example, the long reciprocal saving at `theta=3.01` is `.352`. At `y=3.01`, the additional gain needed by this method is greater than `2.658450+o(1)` powers of P, or `2.659` under the candidate's coarse allowance, before a requested target exponent. At `theta=y=.99`, the intermediate saving is `.061875`, leaving `.928575+o(1)` (coarsely `.929125`). At `alpha=beta=.075`, BG gives `1/1960`; its required further gain is `y+.000450-1/1960+2eta+o(1)`, or the candidate's conservative `y+.001-1/1960+2eta`.

These are thresholds for making the displayed **absolute upper-bound method** small. They are not necessary lower bounds on the actual sum and do not preclude a joint signed argument.

### Repeated-prime and congruence branches

If a selected prime occurs to exponent two, its weight is `ell^-1`, and the other variables have length `Y/Q^2`. With a valid exact-phase bound `B_2(Q)=Q P^-s_2`, the oscillatory budget is

    a_0^-1 L^C G_r Y P^((r-4)/2) P^(-theta-s_2).

Hence the required `s_2` is `y-1-theta+g_2+ell_2+zeta` additively, or `y-theta+g_4+ell_4+zeta` reciprocally. The corresponding principal budgets also gain `P^-theta`. A first-power theorem cannot supply B_2. The cited prime-field inverse-power result alone does not cover the split-prime indicator modulo D; in particular the quadratic identity `chi(n)=chi(n^-1)` does **not** extend to `chi(n)=chi(n^-2)`. No such extension is used by the candidate. Selecting an odd large prime or taking the smooth-prime branch avoids needing this unsupported estimate in the residual partition.

For three completions the exact primitive parity kernel is

    (p-1)/2 [1_(n=c)+(-1)^a 1_(n=-c)]-1_(a=0).

If a congruence row supplies relative density/cancellation `P^-s_cong` against its unrestricted weighted sum, its main budget is `G_3 Y P^-s_cong`, with `g_3=27/80000+o(1)`. Its principal budget is `G_3Y/P`. A signed congruence estimate must therefore beat `y+g_3` in this normalization, or exploit further outer cancellation; it is not a prime exponential-sum estimate merely because it came from three completions.

## 5. Applicability and stopping regions of the literature

[SOURCES.md](SOURCES.md) records the actual primary-source statements and endpoint checks. All estimates named in the candidate were reopened. Their stated power exponents and primary hypotheses agree with the candidate.

Vaughan supplies `s_add=min(1/2,theta/5,(theta-1)/2)` for theta>1. Its split-prime reduction has the displayed `sqrt D` conductor-expansion cost. Below or at theta=1 it gives no uniform power saving. FKM explicitly excludes a pure linear additive phase; its prime-field reciprocal/mixed-phase result cannot simply be substituted at modulus Dp.

Baker covers the short reciprocal range with the precise squarefull-part restriction and a possibly tiny positive saving. Fouvry–Shparlinski supplies `s_mid=min(theta/16,theta/3-1/4)` and `s_long=min(1/2,theta/5-1/4)` in their respective ranges. Together, with fixed margins and the exact split-conductor reduction, these give some saving for every fixed theta>1/2. They do not give a saving as large as y in the high-K range.

The BG bilinear formula is valid for arbitrary separate bounded coefficients. Its factor `AB` is essential. Its exponent in the candidate is correct, including `delta_BG=1/1960` at the stated example and the fixed-parameter requirement on k1,k2. A sufficient open range for each factor is exactly the displayed range; endpoints are not automatically saving. The candidate's ceiling `delta_BG<=1/2` follows from each maximum being at least `-1/2`.

For the additive bilinear estimate, fold each coefficient modulo p, apply Fourier Parseval, and use

    ||alpha_fold||_2 <= (1+A/p)^(1/2)||alpha||_2,
    ||beta_fold||_2  <= (1+B/p)^(1/2)||beta||_2.

Together with the divisor L2 bounds this proves the candidate's exponent `s_AB`, with no arbitrary-joint-mask assumption. It is at most 1/2. Neither displayed bilinear application pays a new high-length region under absolute summation of all other variables.

In fact, for a once-occurring prime `theta<=y+o(1)`. When theta>1, Vaughan's `s_add<theta-1<=y-1`, so that scalar prime application alone cannot make any such box small. When theta<=1 it has no positive saving, and its possible absolute-size region lies below y=1, already inside the eligible whole-polynomial length range. This is a statement about this particular proof method, not impossibility of additive cancellation after joint averaging.

## 6. Signed target and verdict boundaries

The remaining sufficient signed assertion is still

    Re(T_rec+T_pr-T_bad)<=(1/2-epsilon)m_H+o(1)

after all residual boxes, with the exact original coefficients, masks, gamma/branch phases and actual families. A separate absolute o(1) estimate would be stronger and sufficient. Estimates of the reciprocal phase alone do not establish either assertion. Principal and bad-family terms may instead be controlled jointly with the phase row; demanding that each be small separately is not necessary for a signed proof.

The candidate expressly leaves this theorem open, and correctly avoids treating an AFE, a zero identity, or the accepted right-half-norm identity as a new gain. Thus the source-level reduction and budget assessment are accepted. **A claim that this package completes the remaining signed half-norm bound or exponent-2024 theorem would be NEEDS_FIX/UNPROVED.**

## 7. Reproduction

Run `python3 audit/prime_pairing_budget/verify_bundle.py --repo .` from the repository root. The verifier checks the portable bundle and exact public dependency pins. The independent mathematical checker retains 13,336 arithmetic cases, 196,440 balanced-factorization/selector cases, 2,046 parity Gauss cases, 300 completion-root/CRT cases, 2,688 conductor-reduction cases, 1,360 finite Fourier mask cases, and exact rational exponent identities. It does not import or execute either candidate checker. [INDEPENDENT_ORIGINAL.json](INDEPENDENT_ORIGINAL.json) preserves the historical receipt and [INDEPENDENT_RERUN.json](INDEPENDENT_RERUN.json) records the portable run. [REPRODUCE.md](REPRODUCE.md) specifies the exact comparison rules.

The universal arguments are given above. The finite numerical Gauss checks are diagnostics, not substitutes for orthogonality or analytic proof. The primary-source endpoint assertions were checked directly in the cited PDFs. The source-only scope is unchanged.
