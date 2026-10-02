import ZhangLS.Spec.Lemma34BSecondMoment
import ZhangLS.Spec.Lemma33
set_option autoImplicit false
namespace ZhangLS.Spec
open MeasureTheory Set
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def lemma34ActualBadFamily {D : ℕ} (χ : RealPrimitiveCharacter D) :
    Finset (lemma33CharacterIndex D) :=
  (lemma33ActualFamily D).filter (fun ψ => lemma23PaperL D^1171 ≤ lemma34ActualB χ ψ.2)

def Lemma34Target : Prop := ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℕ,
  ∀ D : ℕ, D₀ ≤ D → ∀ χ : RealPrimitiveCharacter D,
    ((lemma34ActualBadFamily χ).card : ℝ) ≤
      C * lemma33ActualPrimeMass D * lemma23PaperL D^(-740 : ℤ)

lemma lemma34_mem_bad_family {D : ℕ} (χ : RealPrimitiveCharacter D)
    (p : lemma33PrimeIndex D) (ψ : DirichletCharacter ℂ p.val) :
    (⟨p,ψ⟩ : lemma33CharacterIndex D) ∈ lemma34ActualBadFamily χ ↔
      Lemma23InPsi (D := D) ψ ∧ ¬(lemma34ActualB χ ψ < lemma23PaperL D^1171) := by
  constructor
  · intro h
    have hh := Finset.mem_filter.mp h
    exact ⟨(lemma33_actual_family_mem p ψ).mp hh.1,not_lt.mpr hh.2⟩
  · intro h
    exact Finset.mem_filter.mpr ⟨(lemma33_actual_family_mem p ψ).mpr h.1,not_lt.mp h.2⟩

lemma lemma34_bad_count_times_threshold {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hL : 3 ≤ lemma23PaperL D) :
    ((lemma34ActualBadFamily χ).card : ℝ) * lemma23PaperL D^2342 ≤
      (51208*81^1600) * lemma33ActualPrimeMass D * lemma23PaperL D^1602 := by
  calc
    _ = ∑ ψ ∈ lemma34ActualBadFamily χ, lemma23PaperL D^2342 := by simp
    _ ≤ ∑ ψ ∈ lemma34ActualBadFamily χ, lemma34ActualB χ ψ.2^2 := by
      apply Finset.sum_le_sum
      intro ψ hψ
      have hh := (Finset.mem_filter.mp hψ).2
      calc
        _ = (lemma23PaperL D^1171)^2 := by rw [← pow_mul]
        _ ≤ _ := (sq_le_sq₀ (pow_nonneg (by linarith) _)
          (lemma34_actual_B_nonneg χ ψ.2)).mpr hh
    _ ≤ ∑ ψ ∈ lemma33ActualFamily D, lemma34ActualB χ ψ.2^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => sq_nonneg _)
    _ ≤ _ := lemma34_actual_B_mean_square χ hL

lemma lemma34_actual_bad_count {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hL : 3 ≤ lemma23PaperL D) :
    ((lemma34ActualBadFamily χ).card : ℝ) ≤
      (51208*81^1600) * lemma33ActualPrimeMass D * lemma23PaperL D^(-740 : ℤ) := by
  have hL0 : 0 < lemma23PaperL D := by linarith
  have hh := (le_div_iff₀ (pow_pos hL0 2342)).mpr
    (lemma34_bad_count_times_threshold χ hL)
  calc
    _ ≤ ((51208*81^1600) * lemma33ActualPrimeMass D * lemma23PaperL D^1602) /
        lemma23PaperL D^2342 := hh
    _ = _ := by
      rw [mul_div_assoc]
      congr 1
      have hz := zpow_sub₀ (ne_of_gt hL0) (1602 : ℤ) (2342 : ℤ)
      norm_num only [Int.reduceSub,zpow_natCast] at hz
      exact hz.symm

theorem lemma34_proved : Lemma34Target := by
  refine ⟨51208*81^1600,
    mul_pos (by norm_num) (pow_pos (by norm_num : 0 < (81 : ℝ)) 1600),⌈Real.exp 3⌉₊,?_⟩
  intro D hD χ
  exact lemma34_actual_bad_count χ (lemma33_parameters_at_threshold hD)

end ZhangLS.Spec
