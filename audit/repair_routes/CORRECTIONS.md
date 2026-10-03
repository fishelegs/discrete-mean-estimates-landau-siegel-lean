# Corrections and normalization conventions

This file and the independent reviews govern the interpretation of the retained derivations. No contrary or incomplete interpretation is silently replaced. The corrections concern the two bounded routes in this package only.

## Prime sign and conductor

The exact phase pairing is

    [Z(s,ψ)/Z(s,χψ)] T_DH = τ(χ)χ(p)D⁻¹ E H,
    T_DH = D⁻ˢψ(D)H.

Its normalization is χ(p)EH, not a constant global multiple of H. Discarding χ(p) across the prime family would be an error. The [prime-sign addendum](phase-mechanism-repair/PRIME_SIGN_AND_BILINEAR.md) makes the correction explicit: compensation by χ(p) produces EH; without compensation a new weighted prime-sign question remains. Counting the χ(p)=1 primes does not control their weighted polynomial energy.

The actual conductor is D=|δ| for a signed fundamental discriminant δ. Its odd part is squarefree and v₂(D)∈{0,2,3}; χ may be odd. The original squarefree wording in the deletion derivation is retained as a valid special case, with an explicit review extension attached. The d₈(D)/D bound does not require squarefreeness. For all actual real primitive conductors,

    d₈(D) ≤ C√D,
    C = 30√2 Π(odd primes p<64) max(1,8/√p).

When 4|D, the removed D-divisible terms vanish because ρ=μ*(μχ) has ρ(2ʲ)=0 for j≥2. This is solely a fact about this diagonal deletion. BPZ's other parity, conductor, range, and weight restrictions are not thereby removed.

## C₀, C₁, and T₁ are different kernels

Use positive-exponential Gauss sums, ε(θ)=τ(θ)/(i^parity(θ)√cond(θ)), rψ=ε(ψ)ε(χψ). Fix ψ parity a and χ parity c. Set

    d_a=(−1)^(ca)χ(p)ε(χ),  c_a=(−1)^a d_a,
    N_a=(p−1)/2−1_(a=0),  p≥5,  p∤D.

The actual cross and target entries are

    C_k[A,B]=∫rψ^k Z(ρ,χψ)⁻¹ A B dμ,
    T_k[A,J]=∫rψ^k A conj(J)dμ.

In the right-contour proxy C_k has root factor rψ^(k−1). With v=ℓmn a unit modulo p and Kl₂(u;p)=p⁻¹ᐟ²Σ(x≠0)e_p(x+u/x), the exact full primitive parity-family averages are

    C₀ kernel:
    average rψ⁻¹ψ(v)
      = conj(c_a)(p−1)/(2N_a√p)
        [Kl₂(v/D;p)+(−1)^aKl₂(−v/D;p)]
        − 1_(a=0)conj(c_a)/(pN_a).

    C₁ kernel:
    average ψ(v)
      = (p−1)/(2N_a)[1_(v≡1)+(−1)^a1_(v≡−1)]
        − 1_(a=0)/N_a.

For T₁, use v=ℓm/n and J*(1−s,barψ), which includes n^(−(1−s)). Its residual root factor is ε(χψ), and

    average ε(χψ)ψ(v)
      = d_a i^(−a)/(N_a√p)
        {(p−1)/2[e_p((Dv)⁻¹)+(−1)^ae_p(−(Dv)⁻¹)]
          +1_(a=0)}.

All inverses in these expressions are modulo p. The principal correction is negative for C₀ and C₁ and positive for T₁. The gamma factor for C₀/C₁ is the inverse product factor g; T₁ has the inverse single factor G_a. Their analytic weights cannot be interchanged.

The earlier addendum's Section 5 bullet suggesting that its Kl₂ sum directly evaluates a root-twisted trial is incomplete. Its wording is retained and visibly flagged. [The independent review, Section 2](phase-arithmetic-independent-review/REVIEW.md), and [ERRATA.md](phase-arithmetic-independent-review/ERRATA.md) supply the precise replacement. The κβ coefficient and gamma integral remain, as do the Ψ₁-to-full-family, contour, and residue-conversion errors. These exact finite-character kernels are not actual weighted-zero mean formulas.

## Source weights, phase, and target normalization

For the altered shifts, b_j=(log P)β_j is purely imaginary, b₃=b₁+b₂, and the leading source weights are

    w_j=i b_j exp(b₃−b_j)/Π(ℓ≠j)(b_ℓ−b_j).

They follow from the source residue −β_j/Π(ℓ≠j)(β_ℓ−β_j) and exterior −i(pt₀)^β₃. Substituting the original real weights (1/2,2,3/2) at a new frequency triple is not justified. The reversed high-tail term carries conj(w_j), and the separate low endpoint term i exp(b₃)φ(0)ψ(0) must be retained. The complete high tail includes the cumulative tail where the reflected profile itself has vanished.

The phase exp(b₃−b_j) is exact in the leading model. At finite D the factors t₀^β₃ and p/P corrections still exist. The contour proxy residues differ from c* by the gamma-shift conversion factor; replacing it by 1 requires an integrated error estimate. A local single-shift radius does not generalize every fixed-triple contour or existing Lean theorem.

Periodic Fourier normalization uses interval length two and basis exp(−inπt), so E₀₂=2ΣP(nπ)|uₙ|². The true source tent J has support [0.5,0.504], width d=1/250, height 1, mass d/2, ∫J²=d/3, and ∫|J′|²=4/d. Recompute its norm with the new complex weights:

    Rw=N(J)=C(4/d+T_s d/3)−R_s Im(Σw_j)d²/4,
    Lw=BN(h,J).

This preserves the source target pairing and its linear-first polarization convention. It gives a matched leading ratio bound, not a bound for the actual arithmetic target-transfer defect.

## Meaning of the bilinear saving

The normalized bare-pair exponent −3/200 is valid. The earlier elementary p^.001 upper certificate was insufficient, not an impossibility theorem. For shorter dyadic blocks, orient the smaller length as M: the full third contribution p⁻²¹ᐟ⁶⁴(MN)⁵ᐟ¹⁶ decreases as MN decreases. The bracket alone need not retain its endpoint exponent −.016. This correction prevents an unsupported blockwise assertion while preserving the full-cutoff saving.

The much larger upper certificate after absolutely summing κβ and the gamma kernel is likewise not a lower bound or proof that cancellation is absent. No correction in this package supplies a favorable signed complete-ratio margin.
