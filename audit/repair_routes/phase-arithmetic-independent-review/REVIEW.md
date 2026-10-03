# Independent arithmetic review of the bounded phase-repair branch

Public audit edition. Mathematical content is retained from the reviewed report; portable paths, immutable citations, and explicitly labeled clarification notes are documented in [PACKAGING.md](../PACKAGING.md). Read [CORRECTIONS.md](../CORRECTIONS.md) with this report.

Date: 2026-10-03. Scope: mathematical audit only. No Lean execution, repository edits, new axioms, or claim to prove the missing weighted-zero mean.

## Verdict

The frozen CRT/parity calculation, its essential prime-dependent factor χ(p), the central-value ramified-deletion estimate, and the prime-modulus specialization of MQW Theorem 2.2 all survive independent checking. The bare-pair exponent is exactly −3/200, not merely a heuristic. None of these statements evaluates the proposed new trial's complete Gram/target ratio.

Three clarifications should accompany the frozen reports:

1. The displayed trilinear Kl₂ kernel evaluates the full-parity **C₀ right-contour term**. The candidate with one additional rψ has cross term C₁, whose root numbers cancel and whose character average is a **congruence kernel**. Their analytic difficulties are related, but they are different sums.
2. The deletion result is stronger than the squarefree wording suggests. Its d₈(D)/D form is valid for every positive integer D in the specified diagonal. The √D simplification holds for every actual real primitive conductor. For even real primitive conductors, the deleted terms are identically zero for this particular ρ.
3. Any appeal to the full-parity character kernel still needs a separately paid replacement of Ψ₁ by the full family, plus contour and residue-conversion errors. An exact finite character identity does not settle those costs.

The companion `ERRATA.md` gives narrowly scoped wording changes. `exact_checks.py` and `exact-checks.json` record exact arithmetic and cyclotomic finite checks. The proofs below, rather than those finite checks, establish the universal elementary identities.

## 1. Definitions and exact conductor-phase calculation

Let χ be a nonprincipal real primitive character of conductor D, p an odd prime not dividing D, and ψ a primitive character modulo p. Let c,a,b ∈ {0,1} be the parities of χ, ψ, χψ, so b is a+c modulo 2. Every character modulo p other than the principal character is primitive. All statements involving normalized even-family averages assume p≥5.

Use the positive-exponential Gauss sum τ(θ)=Σ θ(u) exp(2πiu/q), and

    ε(θ) = τ(θ)/(i^parity(θ) √q),
    R_a(s) = Γ((1−s+a)/2)/Γ((s+a)/2),
    Z(s,θ) = ε(θ)(q/π)^(1/2−s) R_parity(θ)(s).

This agrees with Zhang's exact (2.2), before any high-height approximation. CRT, by writing a residue as up+vD, gives

    τ(χψ) = χ(p) ψ(D) τ(χ) τ(ψ).

Consequently

    ε(χψ) = (−1)^(ca) χ(p) ψ(D) ε(χ) ε(ψ).

Indeed a+c−b is 2ac, which accounts for the sign. Neither CRT nor this sign calculation assumes D squarefree. For real primitive χ, τ(χ)^2=(−1)^cD and |τ(χ)|=√D.

Direct substitution gives

    Z(s,ψ)/Z(s,χψ)
      = i^(b−a) D^s R_a(s)/[χ(p)ψ(D)τ(χ)R_b(s)]
      = τ(χ)χ(p)conj(ψ(D)) D^(s−1) E_(c,a)(s),

where

    E_(0,a)(s)=1,
    E_(1,0)(s)=−i tan(πs/2),
    E_(1,1)(s)= i cot(πs/2).

For c=1, the gamma reflection identity gives R₀/R₁=tan(πs/2) and R₁/R₀=cot(πs/2). The extra factor (−1)^c from 1/τ(χ) supplies the signs above. See the [gamma reflection formula](https://dlmf.nist.gov/5.5#E3).

For H(s,ψ)=Σ a(n)ψ(n)n^(−s), actual index dilation is

    T_D H = Σ a(n)ψ(Dn)(Dn)^(−s) = D^(−s)ψ(D)H.

Thus, exactly,

    [Z(s,ψ)/Z(s,χψ)] T_DH = τ(χ)χ(p)D^(−1)E_(c,a)(s)H.

On the critical line and in any positive measure, ||T_DH||²=D^(−1)||H||². Its support grows from N to DN without increasing the unnormalized coefficient bound; multiplying it by √D to obtain a unit-size direction increases that bound by √D. If H uses coefficients χ(n)f(n), the new coefficient at Dn is χ(n)f(n), not χ(Dn)f(n)=0. It is not an instance of the same smooth χ-profile family.

At P=exp((log D)^9), dilation adds precisely (log D)/(log P)=(log D)^(−8) to the logarithmic support exponent. Fixed endpoint exponents .499 or .503, after this addition, eventually satisfy the broad source cutoff N<PT^(−2), T=exp((log D)^1.1). This only checks the support hypothesis, not coefficient normalization or applicability of specialized mean formulas.

After multiplication by D/τ(χ), the phase-paired direction is χ(p)E H. Since χ(p) is not constant over the prime family, it is not a single scalar multiple of H. An explicitly χ(p)-compensated construction is E H. For even χ this equals H exactly. Without compensation, multiplication by χ(p) is an isometry and splits the span into the χ(p)=±1 prime subfamilies; its covariance with other vectors is a weighted prime-sign question.

For odd χ and s=1/2+it, set y=exp(−πt). Then

    E_(1,0)=(1−iy)/(1+iy),   E_(1,1)=(1+iy)/(1−iy),
    |E|=1,   |E−1|²=4y²/(1+y²).

Hence ||(E−1)H||≤2exp(−πt_min)||H|| on a positive-height window with t≥t_min. In Zhang's window t_min=2π(log D)^519−(log D)^405. This establishes exponential closeness of the compensated trial to H, but does not prove optimality against arbitrarily magnified residuals. That would need means accurate at the residual scale.

## 2. The root factor and the distinct cross kernels

Define

    rψ = ε(ψ)ε(χψ),
    d_a = (−1)^(ca)χ(p)ε(χ),
    c_a = (−1)^a d_a,
    N_a = (p−1)/2 − 1_(a=0),
    Q_p = p√D/π,
    g_(a,c)(s,p) = Q_p^(1−2s) R_a(s)R_b(s).

Then

    Z(s,ψ)Z(s,χψ)=rψ g_(a,c)(s,p),
    rψ=c_a ψ(D)τ(ψ)^2/p.

Here Q_p is the same conductor scale as BPZ's central-value Q when their prime q is p; it is not Zhang's P or his height t₀.

Let dμ be Zhang's actual positive c*ω zero measure divided by its chosen normalizing constant, and define

    C_k[A,B] = ∫ rψ^k Z(ρ,χψ)^(−1) A(ρ,ψ)B(ρ,ψ) dμ.

The trial rψA+Z(ρ,χψ)conj(B) has cross term C₁. The original trial A+Zconj(B) has cross term C₀.

On Re(s)>1, since Zhang's β_j are purely imaginary,

    Kψ(s)=Π_(j=1)^3 L(s+β_j,ψ)/L(s,ψ)
          =Σ κβ(ℓ)ψ(ℓ)ℓ^(−s),
    κβ=(n↦n^(−β₁))*(n↦n^(−β₂))*(n↦n^(−β₃))*μ,
    |κβ(ℓ)|≤d₄(ℓ).

The source contour proxy for c* is c(s,ψ)=−i(pt₀)^β₃Z(s,ψ)^(−1)Kψ(s). Its residues differ from c* by the gamma-shift multiplier controlled in Zhang Lemma 5.2. An exact residue treatment retains that multiplier; treating it as 1 requires an error estimate after integration. After making that justified replacement, the C_k right-edge integrand has the root factor

    −i(pt₀)^β₃ rψ^(k−1) g_(a,c)(s,p)^(−1) Kψ(s) A(s,ψ) B(s,ψ) ω(s).

This is only one contour contribution, not an already established formula for the entire zero mean. In the following kernels the ψ-sum is the full primitive parity family; passing from Ψ₁ needs its own estimate. Put v=ℓmn and omit terms with p|v, since ψ(v)=0 there.

### C₀: inverse root, hence a Kl₂ kernel

With Kl₂(u;p)=p^(−1/2)Σ_(x≠0)exp(2πi(x+u/x)/p), the exact average is

    (1/N_a)Σψ rψ^(−1)ψ(v)
      = conj(c_a)(p−1)/(2N_a√p)
          [Kl₂(v/D;p)+(−1)^aKl₂(−v/D;p)]
        − 1_(a=0)conj(c_a)/(pN_a).

All divisions in kernel arguments are modulo p. To prove it, expand conj(τ(ψ))² and use

    Σ_(ψ primitive, parity a) ψ(w)
      = (p−1)/2 [1_(w=1)+(−1)^a1_(w=−1)]−1_(a=0)

for units w. The constrained products are xy=±v/D. Negating both variables removes the minus signs in their additive phases without changing xy. The principal correction equals minus 1 before division by pN_a. This proves both the argument and its sign; finite Gauss checks are unnecessary for the proof.

### C₁: root cancellation, hence a congruence kernel

The exact average is instead

    (1/N_a)Σψ ψ(v)
      = (p−1)/(2N_a)[1_(v≡1 mod p)+(−1)^a1_(v≡−1 mod p)]
        − 1_(a=0)/N_a.

Therefore the structured sum needed for C₁ is a κβ(ℓ)a(m)b(n)-weighted congruence sum in ℓmn, with the same gamma Mellin kernel. It is not the addendum's Kl₂ sum. Multiplying the original A by χ(p) merely multiplies its C₀ kernel by χ(p); multiplying by χ(p)E(s) also retains E(s) inside the Mellin integral. Explicit compensation removes χ(p).

For general k, one gets an even-dimensional hyper-Kloosterman kernel when k≠1: dimension 2|k−1|, argument vD^(−(1−k)) when k≤0, and (D^(k−1)v)^(−1) when k≥2, together with the parity companion and principal subtraction. This observation does not supply the required coefficient estimates.

### Target pairings are another family of kernels

For T_k[A,J]=∫rψ^k A conj(J)dμ, use J*(1−s,barψ)=Σconj(j(n))barψ(n)n^(−(1−s)). Its contour root factor is rψ^k ε(ψ)^(−1), rather than rψ^(k−1). In particular T₁ has the root factor ε(χψ)=d_aψ(D)ε(ψ). For v=ℓm/n a unit, its exact average is

    (1/N_a)Σψ ε(χψ)ψ(v)
      = d_a i^(−a)/(N_a√p)
          {(p−1)/2 [e_p((Dv)^(−1))+(−1)^a e_p(−(Dv)^(−1))]
            +1_(a=0)}.

The inverse gamma factor here is the single G_a(s,p)^(−1), where G_a=(p/π)^(1/2−s)R_a, and the product weights include n^(−(1−s)). This follows by one Gauss expansion; the principal correction is positive because Σ_(x≠0)e_p(x)=−1. Thus evaluating C₁ alone would still not evaluate the true target pairing or the complete trial ratio.

## 3. Ramified deletion: an independent bound without Proposition 4.1

The published diagonal removes D|a or D|b and records an error Oε(q^(1+ε)/D); the paper's main proposition assumes D^300≤q≤D^C with C fixed. Its printed conductor setup is positive squarefree D and even exceptional character. These are separate facts from the following direct estimate. See [BPZ §§3, 4, 6.1](https://arxiv.org/html/2012.04392v2#S6.SS1).

For the central-value weight,

    V(x)=(1/(2πi))∫ Γ(1/4+s/2)^2/[Γ(1/4)^2s] x^(−s) ds,

there is an absolute constant C_V with |V(x)|≤C_V(1+x)^(−2). For x≥1 move the line to Re(s)=2; for 0<x≤1 move it to −1/4, crossing only the residue 1. Gamma decay makes both remaining integrals absolutely bounded. This proof does not mention q≤D^C, Proposition 4.1, or any exceptional-zero estimate.

Set ν=1*χ and ρ=μ*(μχ). At every integer, |ρ|≤τ and 0≤ν≤τ. Parametrize a₀m=b₀n by

    a₀=ha, b₀=hb, m=br, n=ar, (a,b)=1.

The denominator √(a₀b₀mn) is habr. The union of the removed portions is bounded by the sum of D|ha and D|hb. By symmetry it suffices to bound the first, and submultiplicativity of τ gives

    E_del ≪ q Σ_(ha≤X,hb≤X,D|ha) τ(h)^2τ(a)^2τ(b)^2/(hab)
                    ×Σ_(r≥1) τ(r)^2/r (1+r/Q)^(−4).

Here Q=q√D/π≥1. We used a,b≥1 to replace the two decay weights by (1+r/Q)^(−4). Discard (a,b)=1 and replace hb≤X by b≤X.

The prime-power identity

    binom(j+3,3)−(j+1)^2=j(j−1)(j+1)/6≥0

proves τ(n)^2≤d₄(n) for every n. Also d₄*d₄=d₈, and d₈(uv)≤d₈(u)d₈(v). For completeness, the latter counts ordered eight-part prime-exponent compositions: split a composition of A+B canonically into one of A and one of B, giving an injection into the product set. It is valid without coprimality.

For any fixed k and Y≥1,

    Σ_(n≤Y) d_k(n)/n ≤ (Σ_(m≤Y)1/m)^k ≤(1+log Y)^k.

Consequently

    Σ_(b≤X) τ(b)^2/b ≤ (1+log X)^4,
    Σ_(ha≤X,D|ha) τ(h)^2τ(a)^2/(ha)
      ≤ Σ_(j≤X,D|j)d₈(j)/j
      ≤ d₈(D)/D ·(1+log X)^8.

Finally, split the r-sum at Q and into intervals (2^jQ,2^(j+1)Q]. Its tail is at most a fixed constant times

    Σ_(j≥0)2^(−4j)[1+log(2^(j+1)Q)]^4 ≪ (1+log(2Q))^4.

Combining these independent inequalities proves

    E_del ≪ q D^(−1)d₈(D)(1+log X)^12(1+log(2Q))^4.

No constant depends on a q-versus-D power-range parameter. This proves precisely the central-weight deletion step. It does not prove the other diagonal terms, off-diagonal terms, derivative-weight estimates, or the full range extension.

### Actual conductor scope, including the prime 2

A real primitive character has conductor |δ| for a fundamental discriminant δ. Its odd part is squarefree and v₂(D) is 0, 2, or 3. This also follows from the elementary local classification: at odd primes a quadratic character factors modulo p, while every odd unit congruent to 1 modulo 8 is a square, so a primitive quadratic 2-part has modulus at most 8. The signed discriminant determines χ's parity; it cannot be replaced by positive squarefree D without losing cases. See the [classification in the analytic-number-theory notes, §2](https://w3.impa.br/~goncalves/NotesDavenport.pdf).

Writing D=2^v d with d odd squarefree gives

    d₈(D)/√D = [binom(v+7,7)/2^(v/2)] Π_(p|d)8/√p
      ≤ 30√2 · Π_(odd primes p<64)max(1,8/√p).

The displayed constant is absolute. For v=0,2,3 the 2-part factors are respectively 1, 18, 30√2. Thus E_del/q≪D^(−1/2)(log D)^48 at X=D^20 and q=exp((log D)^9), uniformly over the actual conductor range. This is smaller than every fixed negative power of log D.

There is a stronger elementary observation for even conductors. At any ramified prime p|D, χ(p)=0, hence

    ρ(p)=−1,  ρ(p²)=0,  ρ(p^j)=0 for j≥2.

When 4|D, D|a implies 4|a, so ρ(a)=0. Removing D∤a and D∤b therefore changes this diagonal by exactly zero. This statement concerns the existing D-divisibility deletion; it does not generalize every other use of squarefreeness in BPZ.

For an odd exceptional character or another parity of the variable character, the natural central kernel replaces Γ(1/4+s/2)^2 by the product with parities a,b. The same contour proof works for the four possible pairs (a,b), with a common absolute constant. This is an independently justified local weight extension, not a claim that BPZ printed or proved its whole proposition in these cases.

## 4. MQW: the bare-pair power saving is valid

For q=p prime, MQW Theorem 2.2 has ρ=1 and p_min=p. It bounds a bilinear normalized Kl₂ sum by

    ≪ε p^ε ||α||₂||β||₂√(MN)
       [M^(−1/2)+p^(−1/2)+(MN)^(−3/16)p^(11/64)]

when 1≤M≤Np^(1/4) and MN≤p^(5/4), with α supported on [M,2M], β on an interval of length floor(N), and any unit multiplier in Kl₂. No smoothness or continuous-height average is assumed. See [MQW Theorem 2.2](https://arxiv.org/html/2511.07550v1#S2.SS1).

Take M=p^(499/1000), N=p^(503/1000). Both conditions hold. On dyadic blocks the coefficients α_m=a(m)m^(−1/2−it), β_n=b(n)n^(−1/2−it) have bounded L² norms if a,b are bounded; arbitrary t and any fixed-character factors do not change this fact.

After the p^(−1/2) from the exact root-average kernel, the three exponents are

    −1/2+N_exponent/2 = −497/2000,
    −1+(M_exponent+N_exponent)/2 = −499/1000,
    −1/2+(M_exponent+N_exponent)/2
       −3(M_exponent+N_exponent)/16+11/64 = −3/200.

The third bracket exponent alone is −2/125. Thus the leading bound is Oε(p^(−3/200+ε)). The parity companion has the same bound. The principal-character term is smaller: for bounded coefficients its normalized contribution is O(p^(−2)√(MN)).

The full-cutoff assertion also survives. Partition both cutoffs dyadically and orient each block with the smaller length as M. The first exponent is bounded using the maximal longer length; the third contribution is p^(−21/64)(MN)^(5/16), increasing with MN. Thus every smaller block is no worse than the top bound, and the partition costs only logarithms. Constant-factor endpoints can be padded or partitioned with zeros. The same −3/200 applies to exponents .498 and .504 because their sum is again 1.002.

This is a valid power saving for a full-parity root-weighted **bare two-polynomial** average. It invalidates an impossibility inference based only on the elementary p^.001 certificate. It is not yet an estimate for C₀, C₁, T₁, the selected Ψ₁ family, or the weighted zeros.

## 5. Why κβ and the gamma integral cannot be discarded

For C₀, after the justified full-family passage, the Kl₂ part has the form

    p^(−1/2) Σ_(ℓ,m,n) κβ(ℓ)a(m)b(n) Kl₂(±ℓmn/D;p) W_p(ℓmn),

where W_p is the Mellin integral of (pt₀)^β₃g_(a,c)^(−1)ω, with any retained residue multiplier. It couples all three variables. Replacing it by arbitrary independent coefficients loses information rather than proving it harmless. Expanding κβ gives four convolution variables in addition to m,n, hence six variables.

On Re(s)=σ>1, one may fix a unit ℓ and apply MQW to m,n, uniformly in the multiplier ±ℓ/D. For ℓ on a dyadic block of length R, absolute summation of κβ costs

    Σ_(ℓ~R)|κβ(ℓ)|ℓ^(−σ) ≪ R^(1−σ)(1+log R)^3.

The coefficient L² norms cost M^(1/2−σ), N^(1/2−σ). Stirling gives

    |g_(a,c)(σ+it,p)^(−1)| ≍ [Dp²(t/(2π))²]^(σ−1/2).

The Gaussian ω is normalized to have O(1) vertical L¹ mass for bounded σ. Thus, with N₀=Dp²t₀² and at the proposed polynomial lengths, this particular absolute-value method yields, apart from logarithms and p^ε,

    p^(−1/2−.016) (RMN)^(1−σ) N₀^(σ−1/2).

At RMN≈N₀ its bound is p^.484√D t₀. This is an unusable upper certificate, **not** a lower bound or proof of lack of cancellation. The gamma phase's stationary condition is log(ℓmn)≈log(Dp²(t/(2π))²), so dismissing those blocks requires a real kernel/tail argument. For MN=p^1.002 their indicated R is D t₀²p^.998.

Merging ℓ with the longer polynomial gives length D t₀²p^1.501 paired with p^.499; their product is N₀, exceeding the theorem's p^1.25 admissible product. Merging the shorter polynomial changes the individual powers but not this forbidden product. Residue-class subdivision or convolution structure may help, but needs its own accounting and cannot be absorbed into an unspecified L² coefficient at no cost.

For C₁ the kernel is instead the congruence indicator from §2. κβ and W_p are still present, and potential resonant main terms need evaluation. A successful Kl₂ calculation for C₀ is therefore not automatically either an upper bound or a main-term formula for C₁. The target T₁ has a further single-Gauss kernel and also needs its own analysis.

## 6. Prime-sign rarity and the stopping boundary

Conditionally on Zhang's stated Lemma 3.1 and prime-family mass asymptotic, the positive-sign prime mass bound in the addendum is algebraically correct: ν(p)^2=4 for χ(p)=1, so Σ_(p~P,χ(p)=1)p≪P²(log D)^(−2011), and division by M≈P²(log D)^(−77) yields (log D)^(−1934).

For any H, ||χ(p)H+H||²=4E_+(H) is exact. A uniform per-prime weighted square bound C·a_norm·p·(log D)^K gives E_+(H)≪(log D)^(K−1934); K<1918 is sufficient for E_+=o((log D)^(−16)). Prime counting alone gives no such weighted-energy estimate. A bound without a_norm requires an independently justified lower bound for a_norm.

The stopping statement is appropriately limited: these local results establish no favorable signed residual or complete ratio at the (log D)^(−8) scale. They neither prove global impossibility nor certify a repair. A continuation must fix its candidate, use that candidate's actual C_k and T_k kernels, retain the zero weights and transfer term, and prove joint errors small enough for the intended margin under the original hypothesis L(1,χ)<(log D)^(−2022).

## 7. Reproducibility and source scope

- Packaged inputs: [the derivation](../phase-mechanism-repair/DERIVATION.md), [the addendum](../phase-mechanism-repair/PRIME_SIGN_AND_BILINEAR.md), and their scripts and regenerated JSON outputs. Their package-relative SHA-256 hashes are in `exact-checks.json`; pre-packaging input hashes are recorded separately in `../ORIGINAL_INPUT_SHA256.json`.
- Zhang: the hash-identified arXiv v1 TeX source listed in [SOURCES.md](../SOURCES.md), particularly (2.2), (2.6)–(2.15), Lemma 3.1, Lemma 5.2, (7.1)–(7.2), and §§13–14. [Public source record](https://arxiv.org/abs/2211.02515v1). Used for definitions and claimed reductions, not endorsement of its final theorem.
- BPZ: [version 2, §§3, 4, 6.1](https://arxiv.org/html/2012.04392v2#S6.SS1). The new deletion proof is given independently above and does not invoke Proposition 4.1.
- MQW: [version 1, Theorem 2.2](https://arxiv.org/html/2511.07550v1#S2.SS1). Its exact prime specialization is the sole nontrivial bilinear estimate used here.
- Čech–Matomäki: [version 2, Lemma 4 and proof](https://arxiv.org/html/2303.05277v2#S4). The elementary parity/CRT proof above explains why the unweighted root-moment method does not require the central-value q≤D^C range. This does not remove range or conductor assumptions from their other results.

The exact cyclotomic checks test both parities, signed discriminants, ramification at 2, the principal subtraction in C₀, and the principal addition in T₁. All are finite regression tests. They are neither universal proofs nor analytic mean estimates, and they do not validate Zhang's argument.
