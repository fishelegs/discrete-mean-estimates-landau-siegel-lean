# Two bounded structured-phase tests at Zhang's original scales

2026-10-03. Read-only research; no repository changes, Lean execution, strengthened exceptional-zero hypothesis, or claim of a completed repair. The fixed source is [Zhang, arXiv:2211.02515v1](https://arxiv.org/abs/2211.02515v1); see [version and source anchors](SOURCES.md). Assumption (A) remains L(1,χ)<L^−2022, and the corresponding zero-free-region exponent 2024 is unchanged.

## Findings first

1. The full product functional-equation phase Q=(Zψ Zχψ)^−1 has a genuine, bounded short-polynomial covariance formula on the actual weighted zeros:

   ⟨QA,B⟩μ = −⟨GA,FB⟩μ + O(L^−100 ‖A‖μ ‖B‖μ).

   This is a new analytic interface, not independence of root numbers and zeros. It retains the short-factor resonances. F and G have length D^4. Their product is 1+O(L^−227) on the good family; replacing them by their separate pointwise upper bounds would unnecessarily lose L^158.

2. The good-family-to-full-family extension for these new analytic–analytic entries can be paid at O(M L^−45), by keeping the short divisor structure and using a sixth moment. The printed bounded-coefficient Proposition 7.1 does not itself cover the new coefficients. The proof below is an explicit additional extension argument. To preserve an L^−8 margin, keep the exact gamma multiplier in the arithmetic kernel; Zhang's displayed proof of Lemma 8.1 only gives O(M L^−1) after freezing it.

3. The complete Q-augmented Gram matrix still contains one signed mixed entry, ∫Zχψ^−1 GAB conjugate(F)dμ, which is not an analytic–analytic entry. Thus the short-polynomial identity alone does not provide a gain. A particularly natural compensated construction, Q F H+conjugate(F)H, is O(L^−179)H pointwise and gives only an unresolved tiny residual after normalization.

4. An exact functional-equation transform of all four factors in κ identifies conditional arithmetic kernels for C₁: completing its right contour to all primitive characters would give a congruence kernel, while doing so on the left would give Kl₂(±ℓ/(mn);p), with formal resonance near mn=Dℓ. The C₁ family-completion, truncation, and contour-shift errors have not been paid. The H extension in item 2 does not cover them. The existing Kl₂(±ℓmn/D;p) expression is C₀'s right-contour kernel, not C₁'s.

Neither finite test establishes a surviving signed L^−8 improvement. The stopping condition is an explicit asymptotic for the remaining joint entries, including these resonances, with a joint normalized remainder o(L^−8).

## 1. Notation and precise separation of the phases

Let L=log D, P=exp(L^9), p∈(P,P(1+L^−68)), t₀=L^519, M=Σp. Let μ be the positive measure c*(ρ,ψ)ω(ρ)/(aM) on ψ∈Ψ₁ and the source's zeros ρ of L(s,ψ). Here a is (2.31), a≫1 by Lemma 5.7, and ρ lies on Re ρ=1/2. Write ⟨X,Y⟩μ=∫X conjugate(Y)dμ, linear in the first entry.

Let aψ∈{0,1} be the parity of ψ, c∈{0,1} that of χ, and b=aψ+c mod 2. For a primitive θ of conductor q and parity j, write

   εθ=τ(θ)/(i^j√q),
   h_j(s,q)=(q/π)^(1/2−s) Γ((1−s+j)/2)/Γ((s+j)/2),
   Z(s,θ)=εθ h_j(s,q).

Define

   rψ=εψ εχψ,
   g_a(s,p)=h_a(s,p)h_b(s,Dp),
   Q(s,ψ)=(Z(s,ψ)Z(s,χψ))^−1=rψ^−1 g_a(s,p)^−1.

Thus Q is a height-dependent full functional-equation phase. It is not rψ, rψ^−1 alone, or the single factor Zχψ^−1.

The source's original signed cross term is

   C₀[A,B]=∫Zχψ^−1 AB dμ.

A root-twisted replacement rψA+Zχψ conjugate(B) instead has cross term

   C₁[A,B]=∫rψ Zχψ^−1 AB dμ.

More generally C_k has rψ^k. On the right residue contour it has root power rψ^(k−1), not rψ^k. This indexing fixes the distinction between the two tests below.

All identities are for every real primitive χ and both ψ parities. No squarefreeness or positive-discriminant restriction is added. For sufficiently large D the primes in the source interval are odd and coprime to D.

## 2. Candidate one: the full product phase Q

The source defines (Section 3)

   F(s,ψ)=Σ_{d≤D^4} ν(d)ψ(d)d^−s,   ν=1*χ,
   G(s,ψ)=Σ_{d≤D^4} υ(d)ψ(d)d^−s,   υ=μ*(μχ),
   |υ(d)|≤ν(d)≤d₂(d).

Lemmas 4.1 and 4.2 give |F|+|G|≪L^79 and FG=1+O(L^−227) in the stated good-character region. Lemma 4.8 gives, at every product zero in Ω,

   Q(ρ,ψ)=−G(ρ,ψ)F(1−ρ,conjugate ψ)+e(ρ,ψ),
   |e|≪L^−100.

On the critical line F(1−ρ,conjugate ψ)=conjugate(F(ρ,ψ)). Multiplication by A conjugate(B) and Cauchy–Schwarz prove

   ⟨QA,B⟩μ=−H(GA,FB)+E_AB,
   H(X,Y):=⟨X,Y⟩μ,
   |E_AB|≪L^−100√(H(A,A)H(B,B)).                  (2.1)

The same identity with B=W remains valid for any square-integrable W; no independence of W and ψ is used. Since |Q|=1 on the support,

   ‖QA‖μ=‖A‖μ exactly,
   ‖G conjugate(F)A‖μ=(1+O(L^−227))‖A‖μ.

The second norm uses |G conjugate(F)|=|GF|; it does not require bounding F and G separately. For finitely many bounded-energy A,B, the replacement error is far below L^−8. If their energies grow with L, (2.1), rather than an unqualified O(L^−100), is the required ledger.

### 2.1 Exact new joint Gram and target ingredients

Fix A,B,J and set X=A, W=Zχψ conjugate(B), U=QA. Let

   N_A=H(A,A), N_B=H(B,B), N_J=H(J,J),
   D_AB=∫Zχψ^−1 GAB conjugate(F)dμ.

For the ordered trial list (X,W,U), the diagonal entries are (N_A,N_B,N_A). The upper triangular entries are

   G₁₂=C₀[A,B],
   G₁₃=−conjugate(H(GA,FA))+O(L^−100 N_A),
   G₂₃=−conjugate(D_AB)+O(L^−100√(N_A N_B)).

The target pairings ⟨X_i,J⟩ are

   v₁=H(A,J),
   v₂=conjugate(C₀[J,B]),
   v₃=−H(GA,FJ)+O(L^−100√(N_A N_J)).             (2.2)

These formulas retain every conjugation. In particular, D_AB cannot be replaced by H(GA,FB) or by a character-only root average. It contains a remaining single Zχψ phase and three analytic factors against one conjugate factor.

If G₀ is the nonsingular Gram matrix of (X,W), an actual gain from U is measured by its orthogonal residual U⊥=U−proj_span(X,W)U and the signed target residual ⟨U⊥,J⟩. One must compute both this pairing and ‖U⊥‖² using (2.2), with errors small relative to the residual. A negative sign in (2.1) by itself supplies neither. This is the exact target calibration required for this construction, rather than an argument from a previously optimized leading model.

### 2.2 Support and coefficient costs

For the arithmetic formula (2.5), the underlying coefficient sequences of A and B must be independent of p and ψ across the family and obey fixed uniform bounds |a(n)|,|b(n)|≤C. They may depend on D, χ, and the source's D-dependent shifts, with the same C. The arbitrary square-integrable W permitted in the pointwise/Cauchy identity (2.1) is not thereby covered by (2.5). For |a(n)|≤C and support n≤N, coefficients of GA and FA are υ_D*a and ν_D*a and are bounded by C d₃(n), not by a fixed C. Their support is at most D^4N. At N≤P^.504,

   log(D^4N)/log P≤.504+4L^−8,

which is less than 2/3 and less than log(PT^−2)/log P for all sufficiently large D, with T=exp(L^1.1). The cube of either product has length D^12P^1.512<P². This range is deliberately narrower than the broad endpoint of Proposition 7.1.

No D-dependent coefficient maximum is substituted for the fixed coefficient constant in that proposition. In particular, a rough D^ε bound for d₃ cannot be paid by an error exp(−L^.1).

### 2.3 A short-divisor moment lemma and a quantified family extension

Here is a direct additional estimate. Suppose |b(n)|≤d_r(n), b(n)=0 for n>Y, |a(n)|≤d_k(n), and X≥Y≥3. Then

   Σ_{n≤X}|(a*b)(n)|²/n
      ≪_{k,r} (log X)^(k²)(log Y)^(2kr+r²).     (2.3)

Proof: enlarge b to d_r on all Y-smooth integers. The resulting positive multiplicative majorant has local coefficients d_{k+r}(p^j) for p≤Y and d_k(p^j) for p>Y. Apply Rankin with σ=1+1/log X. The local squared-coefficient Euler factor is 1+k²p^−σ+O_k(p^−2σ) above Y, and 1+(k+r)²p^−σ+O_{k,r}(p^−2σ) below Y. The convergent quadratic-prime factors are bounded by an absolute constant depending on k,r. ζ(σ)^k² and the extra Mertens product up to Y give (2.3). This proves a logarithmic, rather than D-power, cost.

Use x=υ_D*a and y=ν_D*b, with a,b bounded and length ≤P^.504. On the right contour the first polynomial has coefficients κ*x. Since |κ|≤d₄, (2.3) with k=5,r=2 gives

   Σ_{m<P²}|(κ*x)(m)|²/m ≪ L^(9·25+24)=L^249.

For the sixth moment of Y, the coefficients of Y³ are bounded by d₃ convolved with a short d₆ sequence supported on D^12. Hence

   Σ |y*y*y(n)|²/n ≪ L^(9·9+72)=L^153.

By source Lemma 3.3, their character moments are at most P²L^249 and P²L^153 respectively. By Proposition 2.1, |Ψ₂|≪ML^−739. Hölder with exponents 2,6,3 therefore gives

   Σ_{ψ∈Ψ₂}|Σ_{m<P²}(κ*x)(m)ψ(m)m^−s| |Y(1−s,conjugate ψ)|
      ≪ (P²L^249)^(1/2)(P²L^153)^(1/6)(ML^−739)^(1/3)
      ≪ M L^−45,                              (2.4)

on Re s=1/2. Here P²/M≍L^77, and the exponent is exactly

   249/2+153/6−739/3+2·77/3=−45.

At Re s=1/2±α the coefficient weights change by only an absolute factor for the truncated polynomials, since log(m)≲log P and α=π/log P. The source's tail move beyond m=P² and its horizontal Gaussian decay still dominate the fixed divisor/log factors. The exact gamma multiplier used below is bounded on this near-central contour. Thus the extension of each of the two right-contour contributions to H(GA,FB) has error O(ML^−45), apart from exponentially small horizontal/tail terms.

The order of operations matters for this H statement. Start on the finite source segment Re s=3/2, where the κ*x series converges absolutely. Separate its m<P² polynomial from its tail there. Bound the tail by the source's rightward contour move, retaining the fixed divisor factors. For the exceptional-family contribution shift only the finite m<P² polynomial to Re s=1/2, apply (2.4), and shift it back. Finally restore the tail on Re s=3/2. The bad characters' reciprocal L-functions are never moved through their possible zeros: after truncation, only a finite polynomial and the analytic exact gamma multiplier are shifted.

For only one short factor the same calculation gives O(ML^−57); for neither, O(ML^−69). These are extension errors, not an assertion that the remaining arithmetic main sum has already been evaluated.

### 2.4 An actual arithmetic covariance formula with exact gamma weights

This avoids a precision trap in applying Lemma 8.1. Put

   E_{β,a}(s,p)=∏_{j=1}^3 h_a(s+β_j,p)/h_a(s,p),
   B_{β,a}(s,p)=E_{β,a}(s,p)^−1/2.

The analytic square-root branch is the one inherited from source Y and is asymptotic to (pt₀)^β₃ in the source window. For the full vertical kernel below, continue that branch uniquely through the simply connected strip 5/4<Re s<7/4. Each h_a(s,p) and h_a(s+β_j,p) is holomorphic and nonvanishing there: its gamma zeros and poles have integral real parts, unchanged by the purely imaginary shifts. Thus Eβ has a holomorphic logarithm in this strip, and fixing its branch where it meets the source's high upper-half-plane window defines Bβ on the entire line Re s=3/2. Its growth there is at most polynomial in |Im s|, which the Gaussian weight dominates. Root numbers cancel in Eβ. The exact meromorphic residue integrand in the original source window is

   c̃(s,ψ)=−i B_{β,a}(s,p) Z(s,ψ)^−1 Kψ(s),
   Kψ(s)=∏L(s+β_j,ψ)/L(s,ψ),

whose residues are exactly c*. No approximation to c* is made here.

Since Z(s,ψ)^−1=τ(conjugate ψ) z_a(s,p), with

   z_a(s,p)=(−i)^a p^−1/2 h_a(s,p)^−1,

define the exact Mellin kernel

   V_{a,p}(x)=(2πi)^−1∫_{Re s=3/2}
       B_{β,a}(s,p) z_a(s,p) x^−s ω(s) ds.

The vertical integral can equivalently be truncated with the source Gaussian tails retained as an exponentially small error. For polynomial coefficient sequences x,y, define

   R(x,y)=−i Σ_{p,a} Σ_{p∤mn}
       (κ*x)(m) conjugate(y(n))/n · V_{a,p}(m/n)
       · { (p−1)/2 [e(m·n^−1/p)+(−1)^a e(−m·n^−1/p)] + 1_{a=0} }.

All inverses in the exponentials are modulo p. The braces are the exact primitive fixed-parity identity

   Σ_{ψ primitive, parity a} τ(conjugate ψ)ψ(m)conjugate(ψ(n)).

In particular, the even principal-character correction is +1 here, not −1. The formula follows by opening the Gauss sum; the excluded principal character has τ(ψ₀)=−1.

For the short-divisor products in (2.4), the actual zero mean has the bounded representation

   H(X,Y)=[R(x,y)+conjugate(R(y,x))]/(aM)
              +O(a^−1L^−45),                 (2.5)

with the stronger stated exponents when fewer short factors occur. The source contour reflection establishes the conjugate second term; (2.4) pays for completing Ψ₁ to Ψ. This formula keeps the full additive/resonant arithmetic sum. It is not an evaluated asymptotic for that sum, and it does not assert a favorable sign.

The printed proof of Lemma 8.1 first replaces Bβ by (pt₀)^β₃. Its displayed estimates give L^−114·P²L^36=O(ML^−1), using P²/M≍L^77. Its conclusion o(M) therefore cannot simply be read as o(ML^−8). Formula (2.5) retains Bβ exactly, so it does not spend that inadequate freezing estimate. To pass from (2.5) to the source's S_j-style asymptotics at L^−8 precision requires a new calculation with this exact kernel or a separately improved freezing estimate.

### 2.5 A concrete near-null construction that fails without much finer means

The stronger source Lemma 4.4 says at the same zero

   F+Q^−1 conjugate(F)=O(L^−179).

Multiplication by the unit phase Q gives

   QF+conjugate(F)=O(L^−179).

Consequently

   ‖QFH+conjugate(F)H‖μ≤C L^−179 ‖H‖μ.

This is an exact source-supported relative cancellation bound. For ‖H‖μ=O(1), the residual norm is O(L^−179); more generally it is o(L^−8) only after an energy estimate such as ‖H‖μ=o(L^171). A target-pairing claim additionally pays ‖J‖μ by Cauchy–Schwarz. Bounded polynomial coefficients alone are not an energy estimate for this weighted zero measure. In the bounded-energy regime, normalizing this residual by L^179 or more requires correspondingly much finer entrywise means; the O(L^−45) or O(L^−100) errors above cannot certify the resulting residual. Thus this concrete compensated construction has no certified gain at the available precision; no impossibility is claimed for all normalized residuals or for unbounded-energy H.

## 3. Candidate two: exact κ transform and conditional resonance kernels

This candidate is the root-twisted trial rψA+Zχψ conjugate(B), hence C₁. Let β_j be the source's pure imaginary shifts. Define

   Kψ^−(1−s)=∏L(1−s−β_j,conjugate ψ)/L(1−s,conjugate ψ).

The exact functional equations give

   Kψ(s)=Z(s,ψ)^2 E_{β,a}(s,p) Kψ^−(1−s).     (3.1)

On Re s<0, Kψ^− has the absolutely convergent expansion

   Σ_{ℓ≥1} conjugate(κ(ℓ))conjugate(ψ(ℓ))ℓ^(s−1).

No Voronoi estimate or unproved cancellation is hidden in this identity.

The exact CRT ratio, including χ(p), is

   Z(s,ψ)/Z(s,χψ)
      =τ(χ)χ(p)D^(s−1)conjugate(ψ(D)) E_{χ,a}(s),

where Eχ,a=1 for even χ, Eχ,0=−i tan(πs/2) for odd χ/even ψ, and Eχ,1=i cot(πs/2) for odd χ/odd ψ. In the actual high window Eχ,a=1+O(exp(−πt)), but it is retained in the following formula.

Combining (3.1) with the exact c̃ multiplier yields

   rψ^k Zχψ^−1 c̃
    =−i τ(χ)χ(p)D^(s−1) Eχ,a(s) Eβ,a(s,p)^(1/2)
       ·rψ^k conjugate(ψ(D)) Kψ^−(1−s).        (3.2)

This is an exact identity of the meromorphic integrands, for every character and wherever the displayed factors are defined. On the good-family residue contour one may apply it while retaining both vertical contributions and the horizontal pieces. It does not pay for replacing Ψ₁ by all primitive characters, truncating the resulting series, or shifting the summed expressions to the half-planes used below. In particular, no C₁ actual-mean remainder has been established here. The primitive-family identities in §§3.1–3.3 are exact arithmetic identities, but their use as a formula for C₁ or T₁ is conditional on these additional analytic estimates.

The unproved C₁ ledger is:

* Right truncation/tails: the extra Zχψ^−1 produces the two-factor inverse-gamma scale Dp²t₀². The H argument's m<P² truncation cannot discard the resulting saddle blocks near ℓmn≈Dp²t₀²
* Right Ψ₂ completion: a new bound must control the full extra-gamma integrand and its retained long blocks; the 2,6,3 Hölder calculation in (2.4) proves only the single-inverse-Z H extension
* Left Ψ₂ completion and tails: (3.2) has a different dual coefficient arrangement and length geometry, including AB and conjugate(κ); it needs its own moment and tail bounds rather than reuse of (2.4)
* Shifts/horizontal pieces: transitions from the good-family residue contour to the absolutely convergent right and dual-left expansions must be justified with all crossed poles, boundary terms, and errors retained. The exact functional equation alone supplies no such summed estimate

Each of these contributions must ultimately be o(aM L^−8), or enter an explicitly retained main term, before the conditional kernels below can certify the intended precision.

### 3.1 Right contour: C₀ is Kloosterman, C₁ is congruence

Let N_a=(p−1)/2−1_{a=0}, and

   c_a=(−1)^(ca+a) χ(p)εχ,
   rψ=c_a ψ(D)τ(ψ)^2/p.

For p∤v define R_j(v)=N_a^−1Σ_{ψ primitive, parity a}rψ^jψ(v). Then

   R₀(v)=(p−1)/(2N_a)
          [1_{v≡1}+(−1)^a1_{v≡−1}]−1_{a=0}/N_a,

   R_{−1}(v)=conjugate(c_a)(p−1)/(2N_a√p)
          [Kl₂(v/D;p)+(−1)^a Kl₂(−v/D;p)]
          −1_{a=0}conjugate(c_a)/(pN_a).

For the completed primitive family, the right arithmetic kernel associated with C_k's integrand is therefore R_{k−1}(ℓmn), with the common inverse-gamma kernel g_a^−1 and exact Bβ. This is conditional as an actual-zero-mean reduction, as detailed above. The C₀ integrand gives the addendum's Kl₂(±ℓmn/D;p) structure; the C₁ integrand gives ℓmn≡±1 modulo p, including the even principal correction. Its formal inverse-gamma saddle remains ℓmn≈Dp²(t/2π)². Root cancellation does not remove this resonant length or supply an L^−8 bound.

### 3.2 Left contour: the new C₁ Kloosterman argument and short-ratio resonance

After expanding (3.2) and A,B, the character argument is

   v=mn/(Dℓ),

and the scalar Mellin factor is

   τ(χ)χ(p)/(Dℓ) ·
   (2πi)^−1∫ Eχ,a(s)Eβ,a(s,p)^(1/2)
       [mn/(Dℓ)]^−s ω(s) ds.                 (3.3)

After completion to all primitive characters, whose cost remains unproved here, the root kernel would be R_k(v). The exact positive first root moment is

   R₁(v)=c_a(p−1)/(2N_a√p)
         [Kl₂((Dv)^−1;p)+(−1)^a Kl₂(−(Dv)^−1;p)]
         −1_{a=0}c_a/(pN_a).

For the completed-family C₁ integrand, this becomes Kl₂(±ℓ/(mn);p). For the C₀ integrand, it is the congruence mn≡±Dℓ modulo p. The outside χ(p) in (3.3) cancels the χ(p) in c_a for C₁ only after this multiplication is explicitly made; discarding it earlier changes the family.

If the slowly varying exact multiplier in (3.3) were a constant, its Mellin transform would be exactly

   x^−s₀ exp(−L₂² log²x),  x=mn/(Dℓ),  L₂=L^400.

This constant-multiplier comparison suggests the formal resonance mn≈Dℓ, with logarithmic width about L^−400. No summed replacement error or tail bound for the retained exact multiplier is established here; replacing it by a constant and summing an unbounded absolute coefficient error is not justified. At MN=P^1.002 the formal resonance places ℓ at P^1.002/D; this is still a substantial structured variable, not a fixed scalar coefficient.

For the source χ-weighted A,B, the exact integer diagonal mn=Dℓ has χ(mn)=0 and hence vanishes when D>1. This does not kill neighboring integers in the Gaussian window, whose length grows exponentially in L^9, nor the congruence off-diagonals. For C₀ and products supported strictly below p, the simultaneous near-diagonal/congruence conditions can sometimes force the exact diagonal; the actual upper product length P^1.002 does not permit that shortcut. At this length, differences by multiples of p fit inside the resonant window for sufficiently large D.

The conditional left and right arithmetic sums can therefore both contain substantial resonances. Their identification is an exact algebraic/conditional analytic reduction, not a completed actual covariance formula. A bound for one, or removal of the exact diagonal, does not prove the combined C₁ is small or favorable. A bound on a fixed ℓ Kl₂ block alone does not pay this ℓ sum or evaluate the right congruence contribution.

### 3.3 Complete root-trial Gram/target ingredients and T₁'s distinct kernel

For the ordered trial list (A,W,rψA), the diagonal entries are again (N_A,N_B,N_A), while the upper triangular entries are exactly

   G₁₂=C₀[A,B],
   G₁₃=conjugate(T₁[A,A]),
   G₂₃=conjugate(C₁[A,B]),

and the target vector is

   (H(A,J), conjugate(C₀[J,B]), T₁[A,J]),
   T₁[A,J]=∫rψ A conjugate(J)dμ.

For the two-direction trial rψA+λW, only the corresponding 2-by-2 submatrix and these actual target pairings are required. If the source's J₂-based surrogate pairing is used instead, its transfer error must additionally be retained. It is not part of T₁ by definition.

On the right contour T₁ has the root factor rψ εψ^−1=εχψ, with the single gamma factor h_a(s,p)^−1 and exact Bβ. Set

   d_a=(−1)^(ca)χ(p)εχ,  v=ℓm/n.

Opening the one Gauss sum gives the exact primitive parity average

   N_a^−1Σ εχψ ψ(v)
     = d_a i^−a/(N_a√p)
       ·{(p−1)/2[e((Dv)^−1/p)+(−1)^a e(−(Dv)^−1/p)]+1_{a=0}}.

Thus the completed-family right integrand for T₁ has a single-Gauss additive kernel, distinct from the C₁ congruence kernel and C₀ Kl₂ kernel. Its even principal correction is positive. The argument and correction are independently checked in [the included review](INDEPENDENT_REVIEW.md) and [its finite checks](checks/check_independent.py), and agree with the same elementary character-orthogonality calculation used here. The actual T₁ mean additionally requires its own completion, tail, and contour ledger; the arithmetic identity alone does not supply it or evaluate the full right-minus-left zero mean.

## 4. Exact finite next theorem and stopping condition

For the Q test, (2.5) now gives a bounded arithmetic representation for the new analytic entries H(GA,FA) and H(GA,FJ), retaining both parity and the exact gamma weight. What remains is:

* Evaluate those explicit short-divisor resonance sums, the mixed D_AB, and the already needed ordinary C₀/target entries jointly with o(L^−8) normalized error
* Insert those actual entries into (2.2), compute the residual norm and target pairing, and show a signed margin at the claimed scale that survives all errors

For the root test C₁, the required theorem must first discharge the explicit completion/tail/shift ledger in Section 3. It must then evaluate the paired right-congruence and left-Kloosterman expressions associated with (3.2)–(3.3), including their resonant terms, and compute T₁[A,J]=∫rψ A conjugate(J)dμ and any old/new Gram cross terms needed by the complete target-calibrated trial. The exact integrand transform alone is not an actual-mean theorem, and the covariance C₁ alone would still be insufficient.

Stop this bounded branch here unless one of these explicit estimates can be proved. There is no source-certified favorable sign yet. The short-divisor sixth-moment extension and the full κ transform are useful new bridges; neither changes Assumption (A), the main exponents, the source parity/conductor scope, or the need to evaluate the actual zero-weighted joint moments.

## Source anchors and check scope

Primary source: [Yitang Zhang, *Discrete mean estimates and the Landau-Siegel zero*, arXiv:2211.02515v1](https://arxiv.org/abs/2211.02515v1). See [SOURCES.md](SOURCES.md) for immutable links and the audited TeX checksum. Relevant anchors: (2.2)–(2.5), (2.6)–(2.15), (2.31), Section 3's F/G and Lemma 3.3, Lemmas 4.1–4.4 and 4.8, Lemmas 5.2/5.7/5.9, Proposition 7.1 and Lemma 8.1, and the source's own three-term transformed covariance in (13.3)–(13.10). The source is evidence for these definitions and local analytic reductions, not validation of its final contradiction.

[checks/check_algebra.py](checks/check_algebra.py) verifies the rational exponent budget, exact primitive parity root/Gauss formulas at small primes and both χ parities, the Gram conjugations by pointwise complex algebra, and the mixed-moment support budget. It does not prove an asymptotic estimate or execute Lean.

Public-edition provenance and the preserved correction history are in [EDITION_NOTES.md](EDITION_NOTES.md) and [CORRECTIONS.md](CORRECTIONS.md).
