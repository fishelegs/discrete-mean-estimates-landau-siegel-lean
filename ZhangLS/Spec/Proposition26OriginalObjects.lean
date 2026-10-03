import ZhangLS.Spec.Proposition26EnergyObjects
import ZhangLS.Spec.Lemma82Definitions
import ZhangLS.Spec.Lemma171Target

/-! Literal Proposition 2.6 objects from (2.20), (2.21), (2.22),
(2.24)--(2.31). Only the independently documented Z-tilde=Z convention from
Lemma 8.1 is retained. The actual target is defined, not claimed proved. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex ComplexConjugate Finset
open scoped Classical

noncomputable def proposition26PaperP2 (D : ℕ) : ℝ :=
  lemma23PaperP D^(1/2:ℝ)*lemma56PaperT D^(-10:ℤ)
noncomputable def proposition26PaperP3 (D : ℕ) : ℝ :=
  lemma23PaperP D^(249/500:ℝ)
noncomputable def proposition26IotaThree : ℂ := -(100635/100000:ℂ)-(22789/100000:ℂ)*I
noncomputable def proposition26IotaFour : ℂ := -(68738/100000:ℂ)+(160688/100000:ℂ)*I

noncomputable def proposition26HComponent {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (X : ℝ) (μ : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ lemma82StrictCutoff X,
    lemma112Coefficient χ ψ n/(n:ℂ)^s *
      ((1-Real.log (n:ℝ)/Real.log X:ℝ):ℂ) *
        ((X/(n:ℝ):ℝ):ℂ)^(lemma82SmoothingBeta D μ)

noncomputable def proposition26H2 {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ) : ℂ :=
  conj proposition26IotaThree*proposition26HComponent χ ψ (proposition26PaperP3 D) 6 s+
    conj proposition26IotaFour*proposition26HComponent χ ψ (proposition26PaperP2 D) 7 s

noncomputable def proposition26TildeAlpha (D : ℕ) : ℝ :=
  Real.log ((D:ℝ)*lemma51PaperT0 D)/Real.log (lemma23PaperP D)

/-- The positive-index convention is exactly LSeries.term at n=0. -/
noncomputable def proposition26J1 {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ) : ℂ :=
  ∑' n : ℕ, LSeries.term (lemma112Coefficient χ ψ) s n *
    (lemma111Tent (Real.log (n:ℝ)/Real.log (lemma23PaperP D)):ℂ)
noncomputable def proposition26J2 {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ) : ℂ :=
  ∑' n : ℕ, LSeries.term (lemma112Coefficient χ ψ) s n *
    (lemma111Tent (Real.log (n:ℝ)/Real.log (lemma23PaperP D)+
      1/250-proposition26TildeAlpha D):ℂ)

noncomputable def proposition26JDefect {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ) : ℂ :=
  letI : NeZero (D*p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  proposition26J1 χ ψ s-lemma23DirichletZ (lemma44CharacterTwist χ ψ) s*
    conj (proposition26J2 χ ψ s)

noncomputable def proposition26XiThreeStar {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (Y : (ψ : lemma33CharacterIndex D) → ℂ → ℂ) : ℝ :=
  ∑ ψ ∈ lemma81GoodFamily χ, ∑ ρ ∈ lemma81ZeroFinset D ψ.2,
    proposition26Weight c Y ψ ρ * ‖proposition26JDefect χ ψ.2 ρ‖ *
      ‖proposition26H2 χ ψ.2 ρ‖

/-- Original uniform o(a·𝒫), with actual χ/(A), original prime mass,
the actual a, a fixed compatible shift constant, and every genuine branch.
No mean bound or estimate equivalent to this target occurs as a premise. -/
def Proposition26Target : Prop :=
  ∃ c : ℝ, 0<c ∧ Lemma52CompatibleConstant c ∧
    ∀ ε : ℝ, 0<ε → ∃ N : ℕ, 2≤N ∧
      ∀ D : ℕ, N≤D → ∀ χ : RealPrimitiveCharacter D,
        NormalizedAssumptionA χ →
        ∀ Y : (ψ : lemma33CharacterIndex D) → ℂ → ℂ,
          (∀ ψ ∈ lemma81GoodFamily χ, Lemma23ActualBranch ψ.2 (Y ψ)) →
          |proposition26XiThreeStar χ c Y| ≤
            ε*lemma171MainTerm χ*lemma33ActualPrimeMass D

/-- Exact finite weighted Cauchy on the original Xi3, with the actual H₂ and
J₁−Zχψ conjugate(J₂). Positivity is the sole local input; it is proved above
uniformly from the compatible constant and genuine branches. -/
theorem proposition26_original_cauchy {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (Y : (ψ : lemma33CharacterIndex D) → ℂ → ℂ)
    (hw : ∀ ψ ∈ lemma81GoodFamily χ, ∀ ρ ∈ lemma81ZeroFinset D ψ.2,
      0≤proposition26Weight c Y ψ ρ) :
    proposition26XiThreeStar χ c Y^2 ≤
      proposition26Energy χ c Y (fun ψ ρ => proposition26JDefect χ ψ.2 ρ)*
        proposition26Energy χ c Y (fun ψ ρ => proposition26H2 χ ψ.2 ρ) := by
  unfold proposition26XiThreeStar proposition26Energy
  apply sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro ψ hψ
    exact sum_nonneg (fun ρ hρ => mul_nonneg (hw ψ hψ ρ hρ) (sq_nonneg _))
  · intro ψ hψ
    exact sum_nonneg (fun ρ hρ => mul_nonneg (hw ψ hψ ρ hρ) (sq_nonneg _))
  · intro ψ hψ
    apply sum_sq_le_sum_mul_sum_of_sq_le_mul
    · intro ρ hρ
      exact mul_nonneg (hw ψ hψ ρ hρ) (sq_nonneg _)
    · intro ρ hρ
      exact mul_nonneg (hw ψ hψ ρ hρ) (sq_nonneg _)
    · intro ρ hρ
      exact le_of_eq (by ring)

end ZhangLS.Spec
