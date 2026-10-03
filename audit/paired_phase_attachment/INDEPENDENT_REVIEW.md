# Independent review of the paired-phase weighted attachment

Verdict: ACCEPT at source level in the stated bounded finite trial class. This review checked the genuine repository inputs at commit61c82ec022a2a5c4e6bf356de14136c730a2d404. Its original reviewed derivation has SHA256 a316eb3c8d637068dd271043edad6b45cdbd3dd17b23da501c7edce0d5463cca; the portable rendering is [DERIVATION.md](DERIVATION.md). The original review fingerprint and the rendering fingerprints are in MANIFEST.json.

## 1. Accepted result and its limits

The source derivation genuinely closes the proposed weighted substitution:

    H = Zp Zχ G − Gd  →  Gd(𝒜−2),
    𝒜 = L(s,ψ)L(s,χψ)/F(s),

in the actual completed C1 and T1 integrals over the good family, with added
normalized errors

    O_C(a⁻¹ L⁻¹⁰⁵) + O_C(a⁻¹ L⁻⁴²).

The previously accepted finite-contour attachment, short-υ substitution, and
exceptional-family errors leave the total at O_C(a⁻¹L⁻¹⁴). The result is an
operator attachment. It does not evaluate a signed main integral, prove an
actual Gram eigenvalue or Schur norm lower bound, or certify a numerical gain.
It is not yet a new Lean theorem.

All source conductors, root numbers, parities, β shifts, the inherited Bβ
branch, the conjugate coefficients in Jd, the fixed support box, the original
assumption L(1,χ)<L⁻²⁰²², and the final requested exponent 2024 remain intact.
The support class does not automatically include the lower blocks of the
original broader H1/H2 candidates.

## 2. Exact algebra and the reflected good-family inputs

With δ=FG−1, δd=FdGd−1, and
e=LψLχψ−F−ZFd, the reported remainder is exactly

    R = [ZG(δ−δd)−eGGd]/(1+δ).

Clearing the nonzero denominator FG reduces the assertion to the polynomial
identity ZG(FG−FdGd)−eGGd. Independent symbolic simplification proves the
identity universally, rather than merely at sampled values. In particular the
sign of e and the constant −2 are correct. Setting 𝒜=0 at actual zeros cannot
remove 𝒜 from an integral over a contour.

The dual objects in this identity already include the argument 1−s. Reality
of ν and υ gives Fd(s)=conj(F(1−conj(s))) and likewise for Gd. The point
1−conj(s) is still at positive height near T0 and uses the same good ψ. No
membership statement for conjugate ψ in Ψ1 is required.

The repository definitions give the precise relevant open domains:

- Ω1: Re(s) > 1/2−log L/(100L), height < H+5
- Ω2: Re(s) > 1/2−1/L, height < H+4
- Ω3: Re(s) > 1/2−α, height < H+3

Their upper real boundaries lie beyond the narrow strip in use. The closed
strip between 1/2 and 1/2+α/2, its reflected strip, and its endpoint connectors
are therefore contained in all three domains eventually. The product error
≤4L⁻²²⁷ and raw AFE error O(L⁻¹⁷⁹) apply everywhere needed. FG is nonzero
throughout that closed strip, so both F and G are nonzero there.

The two-sided ratio bound is a valid new source inference from the existing
absolute logarithmic derivative estimate, not a misquotation of a one-sided
Lean interface. For f(x)=log|F(x+it)|,

    |f′(x)| ≤ 140800 L,
    |f(σ)−f(1−σ)| ≤ 281600 L(σ−1/2).

At σ=1/2+α/2 this is 140800αL→0. Exponentiating gives both |Fd/F|≪1 and
|F/Fd|≪1. Combining with FG=1+δ and FdGd=1+δd gives both G ratios. The
named `lemma45_horizontal_F_quotient_bound` in
`Lemma45HorizontalQuotient.lean:46` directly states only the first F ratio;
the reverse inequality follows by the other sign of the same derivative bound.
The candidate correctly presents the integration argument rather than claiming
a nonexistent two-sided named theorem.

## 3. The separated line and the weighted moment budgets

Lemma59Parameters.lean defines all-zero separation, not only separation from
zeros in Ω. On Re(s)=1/2+α/2, Proposition 2.2 puts every product zero inside
the original Ω on the critical line. In particular all Lψ zeros there are at
least α/2 away. A zero outside Ω has either vertical distance ≥2 from the
segment or horizontal distance ≥1/2−α/2; either exceeds α/2 eventually.
Thus the actual `lemma59_proved` applies with η=1/2 and the prescribed first
shift, giving |L(s+β1,ψ)/L(s,ψ)|≪log P=L⁹ uniformly on the entire segment.

The quotient is used only for a pointwise estimate on that separated line.
It is never analytically continued across a zero to justify a contour move.
The AFE and bounded F ratios first give |LψLχψG|≪1. Factoring Q there and
then using its exact functional equation gives

    |Qd Gd| ≪ L⁹ |L(s+β2,ψ)L(s+β3,ψ)|.

The actual fourth-moment theorem is exactly as the report says:
`Lemma81ActualLFunctionMoments.lean:23` has real width α and closed height
bound H+1, over the full actual Ψ. Because the βj are pure and |βj|≤4α<1
eventually, both shifted arguments belong to that domain. No χψ moment,
degree-four product moment, or eighth L moment has been assumed.

The polynomial moment derivations also have the right lengths and powers:

- Fourth moments for A,B,Jd cost P²L³⁶; support ceilings P^.504 are below P
- Their cubes have length at most P^1.512<P²; τ3²≤τ9 costs L⁸¹
- G³ has length at most D¹²<P² and coefficient envelope τ6; τ6²≤τ36
  gives harmonic energy O((1+12L)³⁶)=O(L³⁶)

For dual Jd, reflection returns to the same positive height and thin real
strip, or one may use the full-family inverse-character moment. This does not
require a good-family conjugation assertion. The short G bound uses its actual
υ coefficients, not a false bounded-coefficient hypothesis.

The two Hölder estimates are therefore

    Σ|QdGdAV| ≪ P² L^[9+4·36/4] = P²L⁴⁵,
    Σ|QdGdGAV| ≪ P² L^[9+36/4+36/4+36/6+81/6+81/6]
                  = P²L⁶⁰.

The second uses reciprocals 1/4,1/4,1/6,1/6,1/6, which sum exactly to one.
Using the two-sided G ratio on the δ part of R, the two absolute bounds before
normalization are P²L⁻¹⁸² and P²L⁻¹¹⁹. The exact Gaussian mass has no W or H
loss. The actual M≥P²/(4L⁷⁷) gives −105 and −42.

Crucially the analytic error integrand, with denominator 1+δ=FG, is moved
from the central line to the separated line. Its denominator is nonzero on
the whole intervening strip. The argument does not assert these absolute
moment estimates on the central line. Horizontal errors are absorbed by
W⁻¹exp(−L¹⁰/4+o(1)) against an exp(O(L⁹)) envelope.

## 4. Bad-family restriction and the legal resummation order

The report correctly writes κshort=κ−Δκ before estimating Ψ2. The accepted
positive whole-family Δκ estimate restricts to any subset and costs
O_C(a⁻¹L⁻²²⁵). The genuine original κ harmonic energy is O(L³⁶). Using that
energy, A/V sixth moments, and the source cardinality |Ψ2|≪ML⁻⁷³⁹ gives

    36/2+81/6+81/6−739/6+77·5/6 = −14.

Using P²L⁻⁷³⁹ in place of ML⁻⁷³⁹ would be an error; the candidate does not
do so. Using the τ6 envelope to retain an original κ moment exponent would
also be an error; the candidate explicitly avoids it.

The resummation is sound as an integrated identity with paid errors:

1. Start with finite, common q cutoffs on the central line; restore any deleted
   low blocks using their accepted integrated exponential bounds
2. Remove Ψ2 while everything is a finite polynomial
3. Move the finite expressions to the safe lines Re(s)=3/2 and −1/2
4. Insert the full absolutely convergent short-κ series on their convergence
   sides; estimate the difference as a tail moved outward
5. Identify full products GQ and GdQd there, and only then move the entire
   product integrands back to the central line

The exact strict support gaps are, in C-right/C-left/T-right/T-left order,
1/2000, 1/1000, 3/1000, 1/1000. The unsimplified conductor ratios retain D,
p, t and t0. Their subpower factors are absorbed by those fixed gaps before
the outward shifts to 1/2±L⁹. Replacing log³ by log⁵ in the τ6 tail estimate
does not consume a gap. The wide-strip Stirling error O((1+L⁹)²/t) tends to
zero at t≈2πL⁵¹⁹. The inherited Bβ branch remains in the same high rectangle.
Far vertical sides are exponentially small on the L¹⁸ scale, horizontal
sides on the L¹⁰ scale, even after the family summation.

The low-block estimate is integrated, not pointwise. No factorwise truncation
replaces the joint product constraint d r0 r1 r2 r3=q. The full Q products
contain four entire nonprincipal L-functions and no reciprocal L-function.
There is therefore no hidden continuation of a bad character's reciprocal L
through its poles, and no claim that a truncated κ polynomial equals GQ
pointwise on the critical line.

## 5. Gamma, branch, Fourier and conjugation checks

The exact degree-four multiplier is

    Q = Zχ Zp³ Bβ⁻² Qd.

Substituting it in the right-minus-left pair gives exactly

    T: −i rψ Bβ⁻¹ Zp Qd A Jd (ZpZχG−Gd),
    C: −i rψ Bβ⁻¹ (Zp/Zχ) Qd A B (ZpZχG−Gd).

The conductor-Dp gamma and χψ parity in Zχ survive. Neither common Kl2
transforms nor primitive root phases cancel this degree-two defect. βj stays
in the dual arguments as 1−s−βj; Jd contains conjugate j coefficients.
The Schur combination Vx=Jd−x1Ad−x2Zχ⁻¹B is also consistent with the stated
Gram convention: x=E⁻¹b, and the correlation is q−(t,u)x. There is no missing
conjugation of β, J, or x in this combination.

The finite Mellin identity retains the half-endpoint corrections with correct
signs for inclusive lower/exclusive upper endpoints. Γ4 is evaluated at s+z,
while the external multiplier stays at s. Global Mellin use must keep the
canonical gamma product and any removable gamma poles canceled with Qd;
the report states this. It does not assert a new global square-root branch.

The Fourier and CRT formulas, including h=0, the −1/p Kl3 correction,
τ(χ)χ(p)χ(h), and the possibility p|h, are correct. They do not provide a
signed aggregate estimate. Completion of the χ factor retains modulus Dp;
no spurious coprimality with D is added to d or the pure-power factors.

## 6. Minimal genuinely new obligation and the numerical margin

For a fixed bounded trial and bounded old projection x, the next new signed
quantity is precisely the report's explicit

    𝒮_D(A,Vx) = (aM)⁻¹ Σ_{Ψ1} ∫ −i rψ Bβ⁻¹ Zp Qd A Vx Gd(𝒜−2) ω ds/(2πi).

It needs an evaluated surviving term and a quantified error, jointly with the
old entries used to determine x. The finite inverse-additive-minus-Kl3
representation is an equivalent target, not a main-term evaluation. Current
P7/P14 interfaces and positive moment bounds do not fix its phase or a
nonzero target residual.

Independently required are the actual old-block invertibility, the new Schur
norm s=H(A,A)−k*E⁻¹k, and an error certificate covering the augmented
Gram/target matrix. Positive diagonal entries alone allow s=0. The theorem
`lemma171_actual_first_log_normalized_mass_lower_uniform` in
FirstLogMomentLower.lean:137 really proves an arithmetic scalar lower bound
of order L⁻¹³; its own statement explicitly says it is not a matrix or
projected gain. Nothing in that theorem identifies its scalar with s or with
𝒮_D(A,Vx). Consequently it cannot certify R5 or the desired numerical margin.

If each actual matrix entry has error ε and a coefficient vector is z, then
the quadratic error is at most ε||z||₁². At residual squared norm s≈L⁻γ,
bounded projection coefficients lead to normalized error O(ε/s). A margin
of size L⁻δ requires, sufficiently, ε=o(L⁻γ⁻δ). In the report's illustrative
γ=δ=8 case, the inherited L⁻¹⁴ error becomes L⁻⁶ after normalization and is
too large; the new L⁻⁴² substitution error is small enough but does not erase
the inherited errors. No inference about the actual residual scale is made
from the M1 scalar bound.

This review establishes neither a paper-level repair nor a paper-level
counterexample. It accepts the specific weighted attachment and leaves the
signed evaluation, actual nondegeneracy, and normalized margin unresolved.

## 7. Reproducibility

`REPLAYED_CANDIDATE_CHECKS.json` exactly equals the candidate CHECKS.json,
including all frozen input hashes. The independent script and CHECKS.json add:

- Universal symbolic proof of the defect identity and both FE pairings
- Exact rational Hölder, exceptional-family, normalization, and support budgets
- 656 exact Fourier identities over integer coefficient vectors in Q[ζp],
  for p=5,7,11,13
- 20,259 CRT tests against every residue-coordinate basis function, covering
  conductors 3,4,5,8,12,24 and coprime test primes; maximum error <7·10⁻¹⁵
- Eight actual Dirichlet-L FE product tests at 38-digit precision, with
  nonreal primitive characters, both parities, central/off-central points,
  and conductor-Dp twists; relative error <2·10⁻³⁸

These tests check algebra and finite examples. They do not numerically test
assumption (A), the asymptotic large-D theorem, any Gram lower bound, or Lean
kernel acceptance. The uniform analytic reasoning is audited above.
