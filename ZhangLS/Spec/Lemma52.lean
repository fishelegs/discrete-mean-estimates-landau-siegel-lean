import ZhangLS.Spec.Lemma52Product

/-! # Lemma 5.2 for the original shifts and every actual branch

The shift constant is the same one that proves the strict zero-gap
bound and coefficient nonnegativity in Lemma 2.3. Genuine Ψ and the
entire original closed real strip and height window are retained.
-/

namespace ZhangLS.Spec

open Complex

set_option maxHeartbeats 1000000

/-- The exact property of the shift constant selected in Lemma 2.3. -/
def Lemma52CompatibleConstant (c : ℝ) : Prop :=
  ∃ D₀ : ℕ, ∀ {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p),
    D₀ ≤ D → Lemma23InPsi1 χ ψ →
    (∀ ρ ρ' : ℂ, Proposition22ConsecutiveZeros χ ψ ρ ρ' →
      |ρ'.im - ρ.im - lemma44PaperAlpha D| <
        c * lemma44PaperAlpha D ^ 2 * lemma23PaperL D) ∧
    (∃ Y : ℂ → ℂ, Lemma23ActualBranch ψ Y) ∧
    (∀ Y : ℂ → ℂ, Lemma23ActualBranch ψ Y → ∀ ρ : ℂ,
      Lemma23InZeroWindow D ρ → DirichletCharacter.LFunction ψ ρ = 0 →
      deriv (lemma23DirichletNormalizedM ψ Y) ρ ≠ 0 ∧
        (lemma23ActualCoefficient ψ Y D c ρ).im = 0 ∧
        0 ≤ (lemma23ActualCoefficient ψ Y D c ρ).re)

def Lemma52AtConstants (c C : ℝ) (D₀ : ℕ) : Prop :=
  ∀ (D p : ℕ) [NeZero p] (ψ : DirichletCharacter ℂ p),
    D₀ ≤ D → Lemma23InPsi (D := D) ψ →
    (∃ Y : ℂ → ℂ, Lemma23ActualBranch ψ Y) ∧
    ∀ Y : ℂ → ℂ, Lemma23ActualBranch ψ Y → ∀ s : ℂ,
      Lemma51InRegion D s → Lemma52Estimate (D := D) ψ Y c s C

/-- The estimate holds for any fixed positive shift constant once the
modulus is sufficiently large; the relative-error constant is absolute. -/
theorem lemma52_for_every_positive_constant {c : ℝ} (hc : 0 < c) :
    ∃ D₀ : ℕ, Lemma52AtConstants c lemma52ErrorConstant D₀ := by
  obtain ⟨D₀, hsection, hsmall⟩ := lemma52_exists_shift_threshold hc
  refine ⟨D₀, ?_⟩
  intro D p hp ψ hD hψ
  have hL := (lemma44_parameters_at_explicit_threshold (hsection.trans hD)).1
  refine ⟨lemma23_exists_continuous_actual_square_root ψ hψ.2.1 hψ.1.ne_one, ?_⟩
  intro Y hY s hs
  exact lemma52_actual_product_estimate ψ hψ.2.1 hψ.1.ne_one Y hY hL hc (hsmall D hD) hs

def Lemma52Target : Prop :=
  ∃ c : ℝ, 0 < c ∧ Lemma52CompatibleConstant c ∧
    ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℕ, Lemma52AtConstants c C D₀

theorem lemma52_proved : Lemma52Target := by
  obtain ⟨c, hc, D₂₃, h₂₃⟩ := lemma23_proved
  obtain ⟨D₀, h₅₂⟩ := lemma52_for_every_positive_constant hc
  exact ⟨c, hc, ⟨D₂₃, h₂₃⟩, lemma52ErrorConstant, lemma52_error_constant_pos, D₀, h₅₂⟩

end ZhangLS.Spec
