# Exceptional reciprocal-product lemma under original A

Draft research note dated 2026-10-05. Independently reviewed at source-proof level; not Lean-certified. Original assumption exponent 2022 and original target exponent 2024 are unchanged.

## Result

Let χ be a primitive real nonprincipal character modulo D. Write

    L = log D,   B = L^9,

and assume only original A:

    0 < L(1,χ) < L^(-2022).

For every fixed c>0, uniformly for

    s = 1 + c/B + iv,   |v| ≤ L^5,

one has, for sufficiently large D,

    |1 / (ζ(s)L(s,χ))| ≪ L log L.                         (RESULT)

The implicit constant is absolute once D is sufficiently large depending on c. In particular this is O_c(L^(5/4)), so it also meets the requested L^(3/2−ε) alternative with ε=1/4. The estimate is a reciprocal lemma only. It does not establish or attach the original finite-G gamma estimate, a middle-contour estimate, a quadratic-form approximation, or a Landau–Siegel contradiction.

The decisive ingredient beyond the previously accepted local input is a precisely stated public quantitative Deuring–Heilbronn theorem. It includes the other zeros of the exceptional character itself. The proof below then uses elementary periodic partial summation and a normalized analytic logarithm on discs of radius (log L)/L.

## 1. Accepted local input and exact source checks

The accepted local derivative profile proves directly from original A that a_D=L′(1,χ)≥1/2 eventually, with elementary local derivative bounds. This is sufficient to derive a real zero at distance O(L^(-2022)). The exact public source files below are pinned to repository commit 1b1bdae9503bf45acc091381e5574b86930f55ae in SOURCE_PINS.json:

- `Lemma55SimpleRealZero.lean`, lines 100–106, supplies an actual simple real zero β with

      0 < δ := 1−β ≤ 64 L^(-2022).                        (ZERO)

- `Lemma55LocalDerivatives.lean`, lines 19–24 and 68–73, supplies the stated actual local second-derivative bound and first-derivative variation.

The simple-zero source explicitly leaves a larger-height zero exclusion as a separate obligation. No such exclusion is imported from that file: the needed exclusion below comes from the public theorem in §2. All statements here are asymptotic in D; the existing explicit source threshold can be included in the eventual lower threshold.

## 2. Public quantitative repulsion, including the same character

Source: Kübra Benli, Shivani Goel, Henry Twiss, Asif Zaman, *Explicit Deuring–Heilbronn phenomenon for Dirichlet L-functions*, arXiv:2410.06082v3, 8 January 2026, [Corollary 1.1](https://arxiv.org/html/2410.06082v3#S1).

Its applicable statement is: for q>400000 and T≥4, if the product of all Dirichlet L-functions modulo q has a real zero β₁>1−1/(10 log q), every other zero ρ with Re ρ>1/2 and |Im ρ|≤T obeys

    Re ρ < 1 − log(1/[16(1−β₁)K])/K,
    K = 10 log q + log T + 107.                           (DH)

This is a theorem about other zeros of the full product, not merely characters different from the exceptional character. Thus it covers every zero of L(s,χ) other than β. The proof also explicitly treats the exceptional-character case in Proposition 5.1. Simplicity at the removed zero is provided by (ZERO).

Apply (DH) with q=D, β₁=β, and T=L^5+2. The exceptional-zero hypothesis follows from 64L^(-2022)<1/(10L). Eventually K≤11L, and

    log(1/[16δK]) ≥ 2021 log L − log 11264
                 ≥ 2000 log L.

Consequently every relevant other zero satisfies

    Re ρ < 1 − 100 (log L)/L.                            (REPULSION)

The deliberately weakened constant 100 follows from 2000/11>100. No ineffective Siegel lower bound is used: this is the explicit Corollary 1.1, not the paper's ineffective Corollary 1.2.

Put R=(log L)/L and

    z_v = 1 + 1/L + iv,
    F(w) = L(w,χ)/(w−β),

with the removable value F(β)=L′(β,χ)≠0. This F is entire. For |v|≤L^5, the closed disc |w−z_v|≤R is contained, with ample horizontal and vertical margin, in a zero-free region for F. Indeed its real part is greater than 1−R>1/2 and its imaginary part has absolute value below L^5+1<T. The zero β has been removed, and (REPULSION) excludes every other zero. This establishes analyticity and nonvanishing on an open neighborhood of the closed disc, as required below.

## 3. A polynomial upper bound for the divided function

For completeness, the larger-disc growth estimate is proved here rather than extrapolated from a radius-O(1/B) Taylor estimate.

Let Aχ(x)=Σ_(n≤x)χ(n). Nonprincipality and periodicity give Aχ(D)=0 and |Aχ(x)|≤D. For Re w>0, continuation by partial summation gives

    L(w,χ) = Σ_(n≤D) χ(n)n^(−w)
             + w ∫_D^∞ Aχ(x)x^(−w−1) dx.

Differentiating under this absolutely locally uniformly convergent integral is valid. On the rectangle

    1−2R ≤ Re w ≤ 2,   |Im w|≤L^5+1,

eventually Re w≥1/2, |w|≤2L^5, and D^(1−Re w)≤L². The finite part of the derivative is at most

    L² Σ_(n≤D) (log n)/n ≤ 2L^4.

The derivative of the integral part is bounded by

    D^(1−σ) [1/σ + |w|(L/σ + 1/σ²)] ≪ L^8,
    σ = Re w.

For example, 20L^8 bounds the full derivative for all sufficiently large L. Therefore, using the actual zero rather than dividing an upper bound by a possibly tiny denominator,

    F(w) = ∫_0^1 L′(β+u(w−β),χ) du

shows

    |F(w)| ≤ 20L^8                                      (UPPER)

on all the discs in §2. The full straight segment used in this identity lies in the displayed rectangle. In particular the estimate remains valid through w=β; there is no unaccounted pole or small-denominator loss.

## 4. Euler anchor and normalized analytic logarithm

The absolutely convergent reciprocal Euler product at z_v gives

    |1/L(z_v,χ)| ≤ Σ_(n≥1)|μ(n)χ(n)|n^(−1−1/L)
                 ≤ ζ(1+1/L) ≤ 1+L.

Since |z_v−β|≤L^5+2/L≤2L^5 eventually, this implies

    |F(z_v)| ≥ 1/(4L^6).                                (ANCHOR)

Together, (UPPER) and (ANCHOR) yield

    |F(w)/F(z_v)| ≤ 80L^14

throughout the radius-R disc. Because the disc is simply connected and F is nonzero on a neighborhood of its closure, it has an analytic logarithm g_v normalized by

    exp(g_v(w))=F(w)/F(z_v),   g_v(z_v)=0.

No principal-branch assumption or unproved bound on the argument of F is being made. The real part satisfies

    Re g_v(w) ≤ log(80L^14) ≤ 15 log L

eventually. The elementary Borel–Carathéodory inequality gives, for |w−z_v|≤r<R,

    |g_v(w)| ≤ [2r/(R−r)] · 15 log L.                   (BC)

One direct proof is to apply Schwarz's lemma to g_v/(2M−g_v), where M is any positive upper bound for Re g_v, and then rearrange; the normalized value at the center is zero.

For s=1+c/L^9+iv and fixed c>0, eventually 0<c/L^9≤1/L, so |s−z_v|≤1/L. Choose r=1/L in (BC). It follows that

    |g_v(s)| ≤ 30 log L/(log L−1) ≤ 60,
    |F(s)| ≥ e^(−60)|F(z_v)|.

In particular,

    |1/L(s,χ)| ≤ e^60 (1+L) |z_v−β|/|s−β|.             (TRANSFER)

All constants are independent of v and D. The only use of fixed c is to put s within distance 1/L of its Euler anchor; c affects the eventual threshold, not the displayed comparison constant.

## 5. The zeta pole pays for the exceptional-zero denominator

Write ε=c/L^9, so s−1=ε+iv and s−β=ε+δ+iv, with ε,δ>0. Hence

    |s−1|/|s−β| ≤ 1.                                   (CANCELLATION)

### Small heights

There is an absolute neighborhood of 1 where

    |1/ζ(s)| ≤ 2|s−1|.

An explicit elementary check suffices: for Re s>0,

    ζ(s)=s/(s−1)−s∫_1^∞ {x}x^(−s−1)dx.

For |s−1|≤1/8 this gives

    |(s−1)ζ(s)−1| ≤ (1/8)(1+9/7)=2/7,

so the claimed bound follows. If |v|≤1/16 and ε≤1/16, the point is in this neighborhood. Combining (TRANSFER) and (CANCELLATION),

    |1/(ζ(s)L(s,χ))| ≤ 2e^60(1+L)|z_v−β|
                      ≪ 1+L|v| ≪ L.                   (SMALL)

In particular there is no blowup as v tends to zero, including v=0. Treating 1/(s−β) alone would miss this cancellation.

### Heights away from zero

For |v|≥1/16, the geometric ratio obeys

    |z_v−β|/|s−β| ≤ 1+|z_v−s|/|s−β|
                  ≤ 1+16/L ≤ 2.

For |v|≥13, use Nicol Leong, *Explicit estimates for the logarithmic derivative and the reciprocal of the Riemann zeta function*, arXiv:2405.04869v4, 27 August 2025, [Corollary 4](https://arxiv.org/html/2405.04869v4#S2.SS3):

    |1/ζ(σ+it)| ≤ 30.812 log t    (σ≥1, t≥13).

Complex conjugation gives the negative-height version. This source corrects an error affecting some older explicit reciprocal-zeta constants, which are not used here.

On the fixed compact region 1≤σ≤2 and 1/16≤|t|≤13, the reciprocal is bounded by an absolute constant. To recall why the boundary line causes no gap: Euler products exclude zeros for σ>1, while 3+4cos θ+cos 2θ≥0 gives

    |ζ(σ)|³ |ζ(σ+it)|⁴ |ζ(σ+2it)| ≥ 1    (σ>1).

A zero at 1+it with t≠0 would make the left side tend to zero as σ decreases to 1, contradicting this inequality. Thus compactness legitimately applies, without any assumption about unproved zeros near that compact set.

Together these facts give

    |1/ζ(s)| ≪ log(|v|+3) ≪ log L,

uniformly for 1/16≤|v|≤L^5. Inserting this and the bounded geometric ratio in (TRANSFER) proves (RESULT).

## 6. Completed-factor audit: nothing has been discarded

The proof never uses the functional equation or assigns a value to a completed-factor logarithmic derivative. It bounds the entire divided function F through its actual values and zero-free region.

To make this explicit, let a∈{0,1} be the character parity, define

    Aχ(w)=(D/π)^((w+a)/2) Γ((w+a)/2),
    Gχ(w)=Aχ(w)L(w,χ)/[(w−β)(w−(1−β))].

Near β, elementary logarithmic differentiation gives the exact identity

    F′(w)/F(w)
      = 1/[w−(1−β)] + Gχ′(w)/Gχ(w)
        − (1/2)log(D/π) − (1/2)ψ((w+a)/2).

The analytic-log argument controls this whole expression. It does not set Gχ′/Gχ to zero or claim it is o(L). In fact (BC) on radius 3/L about 1+1/L gives g₀=O(1); Cauchy's estimate on a radius-1/L circle then gives F′(w)/F(w)=O(L) for |w−(1+1/L)|≤2/L. This includes β, because |β−(1+1/L)|=δ+1/L≤2/L eventually. At w=β the identity is consistent with Gχ′(β)/Gχ(β)=O(L), which can still contribute at the conductor boundary-layer scale. No first-order phase cancellation needed for a separate gamma or near-critical argument has been established here.

## 7. Scope and limitations

- This is a rigorous analytic implication of original A, the accepted actual near-one simple-zero input, and the identified public quantitative repulsion theorem
- The same-character issue, the full height |v|≤L^5, removable division at β, analytic-log branch, all conductor-dependent losses, and the zeta-pole cancellation are paid explicitly
- The result has not been formally compiled or connected to a finite-G expression
- No previous failed gamma/middle proof is repaired merely by this reciprocal estimate; its remaining transfers, weights, endpoints, and error budgets require separate verification

Exact source identities and public references are recorded in SOURCE_PINS.json. This note proves the reciprocal input only; its applications to two actual finite-V4 sectors are developed in 02_short_sector.md and 03_small_product_sector.md.
