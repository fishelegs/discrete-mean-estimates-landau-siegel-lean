import ZhangLS.Spec.Lemma23SuccessiveZeros
import ZhangLS.Spec.Lemma23ZeroGapArithmetic

/-! # The actual zero-free offset intervals for Lemma 2.3

Consecutive actual product zeros and their proved strict spacing bounds
place the paper's offsets in the first and third gaps. Nonvanishing is
then transferred to the actual Dirichlet L-function.
-/

namespace ZhangLS.Spec

open Complex Set

theorem lemma23_critical_point_in_omega_between
    {D : ℕ} {ρ ζ₁ ζ₂ : ℂ} (hre : ρ.re = 1 / 2)
    (h₁ : Lemma48InOmega D ζ₁) (h₂ : Lemma48InOmega D ζ₂)
    {x : ℝ} (hlo : ζ₁.im < (criticalLinePoint ρ x).im)
    (hhi : (criticalLinePoint ρ x).im < ζ₂.im) :
    Lemma48InOmega D (criticalLinePoint ρ x) := by
  constructor
  · simp [criticalLinePoint, hre]
  · apply abs_lt.mpr
    have hl := abs_lt.mp h₁.2
    have hr := abs_lt.mp h₂.2
    exact ⟨by linarith [hl.1], by linarith [hr.2]⟩

theorem lemma23_actual_offset_nonzero_of_successors
    {D p : ℕ} [NeZero p] (χ : RealPrimitiveCharacter D)
    (ψ : DirichletCharacter ℂ p) {ρ ρ₁ ρ₂ ρ₃ : ℂ}
    (hre : ρ.re = 1 / 2)
    (h₁ : Proposition22ConsecutiveZeros χ ψ ρ ρ₁)
    (h₂ : Proposition22ConsecutiveZeros χ ψ ρ₁ ρ₂)
    (h₃ : Proposition22ConsecutiveZeros χ ψ ρ₂ ρ₃)
    {δ : ℝ} (ha : 0 < lemma44PaperAlpha D) (hδ : 0 ≤ δ) (hδlt : δ < 1 / 5)
    (hg₁ : |ρ₁.im - ρ.im - lemma44PaperAlpha D| < lemma44PaperAlpha D * δ)
    (hg₂ : |ρ₂.im - ρ₁.im - lemma44PaperAlpha D| < lemma44PaperAlpha D * δ)
    (hg₃ : |ρ₃.im - ρ₂.im - lemma44PaperAlpha D| < lemma44PaperAlpha D * δ) :
    (∀ ⦃x : ℝ⦄, 0 < x → x ≤ lemma44PaperAlpha D * (1 - 5 * δ) →
      DirichletCharacter.LFunction ψ (criticalLinePoint ρ x) ≠ 0) ∧
    (∀ x ∈ Icc (2 * lemma44PaperAlpha D * (1 + δ))
        (3 * lemma44PaperAlpha D * (1 - δ)),
      DirichletCharacter.LFunction ψ (criticalLinePoint ρ x) ≠ 0) := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  let F : ℝ → ℂ := fun x => DirichletCharacter.LFunction ψ (criticalLinePoint ρ x)
  let G : ℝ → ℂ := fun x =>
    DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) (criticalLinePoint ρ x)
  have hb₁ := abs_lt.mp hg₁
  have hb₂ := abs_lt.mp hg₂
  have hb₃ := abs_lt.mp hg₃
  have hgap₁ : ∀ x : ℝ, 0 < x → x < ρ₁.im - ρ.im → F x * G x ≠ 0 := by
    intro x hx hhi
    have him : (criticalLinePoint ρ x).im = ρ.im + x := by simp [criticalLinePoint]
    have hlo : ρ.im < (criticalLinePoint ρ x).im := by rw [him]; linarith
    have hupper : (criticalLinePoint ρ x).im < ρ₁.im := by rw [him]; linarith
    exact h₁.between_nonzero _
      (lemma23_critical_point_in_omega_between hre h₁.left_mem h₁.right_mem hlo hupper)
      hlo hupper
  have hgap₃ : ∀ x : ℝ, (ρ₁.im - ρ.im) + (ρ₂.im - ρ₁.im) < x →
      x < (ρ₁.im - ρ.im) + (ρ₂.im - ρ₁.im) + (ρ₃.im - ρ₂.im) →
      F x * G x ≠ 0 := by
    intro x hlo hhi
    have him : (criticalLinePoint ρ x).im = ρ.im + x := by simp [criticalLinePoint]
    have hlower : ρ₂.im < (criticalLinePoint ρ x).im := by rw [him]; linarith
    have hupper : (criticalLinePoint ρ x).im < ρ₃.im := by rw [him]; linarith
    exact h₃.between_nonzero _
      (lemma23_critical_point_in_omega_between hre h₂.right_mem h₃.right_mem hlower hupper)
      hlower hupper
  exact lemma23_offset_factor_nonzero_of_product_gap_exclusion F G ha hδ hδlt
    (by nlinarith only [hb₁.1]) (by nlinarith only [hb₁.2])
    (by nlinarith only [hb₂.1]) (by nlinarith only [hb₂.2])
    (by nlinarith only [hb₃.1]) hgap₁ hgap₃

end ZhangLS.Spec
