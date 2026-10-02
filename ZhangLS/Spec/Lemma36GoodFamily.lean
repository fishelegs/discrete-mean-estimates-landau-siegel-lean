import ZhangLS.Spec.Lemma34
import ZhangLS.Spec.Lemma35
import ZhangLS.Spec.Lemma36
set_option autoImplicit false
namespace ZhangLS.Spec
open scoped Classical
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

/-- The actual complement of the three defining good-character conditions. -/
noncomputable def lemma36ActualNotGoodFamily {D : ℕ} (χ : RealPrimitiveCharacter D) :
    Finset (lemma33CharacterIndex D) :=
  (lemma33ActualFamily D).filter (fun ψ => ¬Lemma23GoodPartialSums χ ψ.2)

lemma lemma36_good_partial_sums_iff_bounds {D q : ℕ} (χ : RealPrimitiveCharacter D)
    (ψ : DirichletCharacter ℂ q) :
    Lemma23GoodPartialSums χ ψ ↔
      lemma34ActualB χ ψ < lemma23PaperL D^1171 ∧
      lemma35ActualB χ ψ < lemma23PaperL D^(-585 : ℤ) ∧
      lemma36ActualB χ ψ < lemma23PaperL D^(-633 : ℤ) := by
  constructor
  · intro h
    exact ⟨h.condition34,h.condition35,h.condition36⟩
  · rintro ⟨h34,h35,h36⟩
    exact ⟨h34,h35,h36⟩

lemma lemma36_not_good_family_eq_union {D : ℕ} (χ : RealPrimitiveCharacter D) :
    lemma36ActualNotGoodFamily χ =
      (lemma34ActualBadFamily χ ∪ lemma35ActualBadFamily χ) ∪ lemma36ActualBadFamily χ := by
  ext ψ
  simp only [lemma36ActualNotGoodFamily,lemma34ActualBadFamily,lemma35ActualBadFamily,
    lemma36ActualBadFamily,Finset.mem_filter,Finset.mem_union,
    lemma36_good_partial_sums_iff_bounds,not_and_or,not_lt]
  tauto

lemma lemma36_not_good_count_le_sum {D : ℕ} (χ : RealPrimitiveCharacter D) :
    (lemma36ActualNotGoodFamily χ).card ≤
      (lemma34ActualBadFamily χ).card + (lemma35ActualBadFamily χ).card +
        (lemma36ActualBadFamily χ).card := by
  rw [lemma36_not_good_family_eq_union]
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add_right (Finset.card_union_le _ _) _)

/-- Combining the three proved exceptional-set estimates bounds the actual
complement of Ψ₁ inside Ψ, ready for the explicit finite-family bridge to Proposition 2.1. -/
theorem lemma36_actual_not_good_count :
    ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℕ,
      ∀ D : ℕ, D₀ ≤ D → ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
        ((lemma36ActualNotGoodFamily χ).card : ℝ) ≤
          C*lemma33ActualPrimeMass D*lemma23PaperL D^(-739 : ℤ) := by
  obtain ⟨C34,hC34,D34,h34⟩ := lemma34_proved
  obtain ⟨C35,hC35,D35,h35⟩ := lemma35_proved
  obtain ⟨C36,hC36,D36,h36⟩ := lemma36_proved
  refine ⟨C34+C35+C36,by positivity,max (max D34 D35) (max D36 ⌈Real.exp 3⌉₊),?_⟩
  intro D hD χ hA
  have hD34 : D34 ≤ D := (le_max_left _ _).trans ((le_max_left _ _).trans hD)
  have hD35 : D35 ≤ D := (le_max_right _ _).trans ((le_max_left _ _).trans hD)
  have hD36 : D36 ≤ D := (le_max_left _ _).trans ((le_max_right _ _).trans hD)
  have hL : 3 ≤ lemma23PaperL D := lemma33_parameters_at_threshold
    ((le_max_right _ _).trans ((le_max_right _ _).trans hD))
  have hM : 0 ≤ lemma33ActualPrimeMass D :=
    Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have h34' : ((lemma34ActualBadFamily χ).card : ℝ) ≤
      C34*lemma33ActualPrimeMass D*lemma23PaperL D^(-739 : ℤ) := by
    apply (h34 D hD34 χ).trans
    exact mul_le_mul_of_nonneg_left
      (zpow_le_zpow_right₀ (show 1 ≤ lemma23PaperL D by linarith) (by norm_num))
      (mul_nonneg hC34.le hM)
  calc
    _ ≤ ((lemma34ActualBadFamily χ).card : ℝ) +
        ((lemma35ActualBadFamily χ).card : ℝ) + ((lemma36ActualBadFamily χ).card : ℝ) := by
      exact_mod_cast lemma36_not_good_count_le_sum χ
    _ ≤ C34*lemma33ActualPrimeMass D*lemma23PaperL D^(-739 : ℤ) +
        C35*lemma33ActualPrimeMass D*lemma23PaperL D^(-739 : ℤ) +
        C36*lemma33ActualPrimeMass D*lemma23PaperL D^(-739 : ℤ) :=
      add_le_add (add_le_add h34' (h35 D hD35 χ hA)) (h36 D hD36 χ hA)
    _ = _ := by ring

end ZhangLS.Spec
