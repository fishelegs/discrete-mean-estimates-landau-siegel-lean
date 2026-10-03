import ZhangLS.Spec.Lemma171

/-! A lower bound for the actual main term a from the proved original 17.1.
The proof uses the genuine nonnegative n=1 term and retains Assumption (A).
No existence assertion for an (A)-character or contradiction shortcut occurs. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset

/-- The source sum contains the actual term 1 when D>1. -/
theorem lemma171_actual_short_sum_ge_one {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) : 1≤lemma171ShortHarmonicSum χ := by
  have hD4 : 1<D^4 := one_lt_pow₀ hD (by norm_num)
  have hm : 1∈Finset.Ico 1 (D^4) := by simp [hD4]
  have hh := Finset.single_le_sum
    (f := fun n : ℕ => lemma171Coefficient χ n/(n : ℝ))
    (s := Finset.Ico 1 (D^4)) (a := 1)
    (fun n _ => div_nonneg (lemma171_coefficient_nonneg χ n) (Nat.cast_nonneg n)) hm
  simpa only [lemma171ShortHarmonicSum,lemma171_coefficient_one,Nat.cast_one,div_one] using hh

/-- For each epsilon the threshold precedes D and chi, as in original 17.1. -/
theorem lemma171_actual_main_lower_uniform (ε : ℝ) (hε : 0<ε) :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ → 1-ε<lemma171MainTerm χ := by
  obtain ⟨D₀,hD₀,h⟩ := lemma171_proved ε hε
  refine ⟨D₀,hD₀,?_⟩
  intro D hD χ hA
  have hs := lemma171_actual_short_sum_ge_one χ (by omega)
  have he := (abs_lt.mp (h D hD χ hA)).2
  unfold lemma171Error at he
  linarith

/-- An eventual absolute lower bound for the actual source a in (2.31). -/
theorem lemma171_actual_main_gt_half :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ → (1:ℝ)/2<lemma171MainTerm χ := by
  simpa only [show (1:ℝ)-1/2=1/2 by norm_num] using
    lemma171_actual_main_lower_uniform (1/2) (by norm_num)

/-- The original actual harmonic-sum error is also uniformly relatively small.
This theorem divides only after proving positivity of the genuine a. -/
theorem lemma171_actual_relative_error_uniform (ε : ℝ) (hε : 0<ε) :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ →
        |(lemma171ShortHarmonicSum χ-lemma171MainTerm χ)/lemma171MainTerm χ|<ε := by
  obtain ⟨D₁,hD₁,hlower⟩ := lemma171_actual_main_gt_half
  obtain ⟨D₂,_,herror⟩ := lemma171_proved (ε/2) (by positivity)
  refine ⟨max D₁ D₂,hD₁.trans (le_max_left _ _),?_⟩
  intro D hD χ hA
  have h1 : D₁≤D := (le_max_left _ _).trans hD
  have h2 : D₂≤D := (le_max_right _ _).trans hD
  have hl := hlower D h1 χ hA
  have hp : 0<lemma171MainTerm χ := by linarith
  have he := herror D h2 χ hA
  unfold lemma171Error at he
  rw [abs_div,abs_of_pos hp]
  apply (div_lt_iff₀ hp).mpr
  exact he.trans (by nlinarith)

end ZhangLS.Spec
