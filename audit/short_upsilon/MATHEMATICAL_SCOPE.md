# Actual short-upsilon: proved interface and analytic boundary

## Mathematical interface

The implementation uses the actual `RealPrimitiveCharacter D`,
`lemma23UpsilonArithmeticFunction`, `lemma23NuArithmeticFunction`, and
`lemma83Kappa`. It proves `(μχ)*χ=1`, `υ*χ=μ`, and
`κ=υ*(χ*powerβ₀*powerβ₁*powerβ₂)`. The proof divides by no character value.
The local/global bound `‖υ(n)‖≤ν(n).re=‖ν(n)‖` includes χ(p)=0, all ramified
prime powers, and n=0 under the arithmetic-function zero convention.

`shortUpsilon` cuts only υ at the actual closed bound d≤D⁴.
`shortUpsilonKappa` convolves this short arithmetic function with the actual
fourfold χ/power coefficient. Its exact divisor and nested-factor formulas
retain every multiplicative equality. The residual is precisely the divisor
sum with d>D⁴. For pure shifts, the fourfold coefficient is bounded by τ₄ and
the short κ by τ₆.

The finite harmonic energy is

    S_N = Σ_{1≤n≤N} ‖κ(n)−κshort(n)‖²/n.

The generic finite proof gives

    S_N² ≤ (Σ_{D⁴<d≤N} ‖ν(d)‖²/d) (harmonic N)^80.

It uses divisor Cauchy and the actual submultiplicativity of τ₂, followed by
ν²τ₂²≤τ₁₆ and τ₄²τ₂≤τ₃₂. Rectangular enlargement occurs only in a nonnegative
error bound, never in a defining κ product constraint.

`shortUpsilon_error_energy_sq_le` attaches the genuine proved L3.1 tail at
floor(P²), obtaining exactly

    S_N² ≤ 1260 · 3^80 · L^(-1291).

Its hypotheses are the original `NormalizedAssumptionA χ`, D>1, L≥1,
D^(-1/2)≤L^(-2013), purely imaginary shifts (`∀j, (β j).re=0`), and
N≤floor(P²). N=0 is included. No β₂=β₀+β₁ relation, shift smallness, or
D⁸-only extrapolation occurs. An explicit algebraic consequence is

    S_N ≤ 36 · 3^40 · L^(-640).

`shortUpsilon_uniform_actual_error_energy` chooses one absolute conductor
threshold before χ, β, and N. It discharges both L≥1 and the exponential
absorption condition using the existing proved
`lemma31_exponential_absorption_threshold`. The same coefficient energy
bound holds under every common mask with modulus at most one.

## Optional actual family estimate

The full primitive-character family estimate uses the actual L3.3 second
moment and the actual L8.1 fourth moments of two finite polynomials of lengths
X,Y≤floor(P), with coefficient bounds B₁,B₂≥0. The residual polynomial is
supported in floor(P²); its mask is chosen independently of the family member.
At every s with Re(s)=1/2 it gives

    Σ_ψ ‖Eψ Aψ Bψ‖ ≤ (CE+CF) B₁B₂ P² L^(-302),
    CE=(32+π²)(36·3^40),
    CF=lemma81FourthMomentConstant = 81(32+π²) exp(4π).

The stronger explicit squared estimate uses CE·CF and L^(-604).
A separate corollary provides the identical bound with the second polynomial
complex conjugated, matching the target pairing at the level of norms.
The residual second moment and the fourth moments are proved inputs, not
assumptions repeating the desired family estimate.

R3 is explicitly split: its finite actual arithmetic and character-family mean
value wrapper are the Lean portion delivered here. The actual finite C1/T1
contour attachment is still source-level and depends on the unformalized R2
attachment. The entire R3 node must not be labeled fully Lean-complete.

No theorem here introduces or claims the source-level C1/T1 contour
attachment, unit gamma multipliers, branch identities, or Gaussian-mass
wrapper. In particular this is not a completed Lean theorem for the
normalized contour error L^(-225), nor a gain or cancellation estimate for
the surviving main operators.

