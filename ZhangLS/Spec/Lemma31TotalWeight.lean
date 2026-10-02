import ZhangLS.Spec.Lemma31NormalizedTail
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset
set_option maxHeartbeats 2000000

lemma lemma31_nu_weighted_sum_le_harmonic_sq {D : ℕ}
    (χ : RealPrimitiveCharacter D) (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, lemma31NuReal χ n*(n : ℝ)⁻¹) ≤ (harmonic X : ℝ)^2 := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 X, ((Nat.divisors n).card : ℝ)*(n : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      rw [lemma31_nu_real_eq_norm]
      exact lemma23NuArithmeticFunction_norm_le_card_divisors χ n
    _ ≤ _ := lemma23_divisor_weighted_sum_le_harmonic_sq X

lemma lemma31_nu_small_weighted_sum_le {D : ℕ}
    (χ : RealPrimitiveCharacter D) (hL : 1 ≤ lemma23PaperL D) :
    (∑ n ∈ Finset.Icc 1 (D^2), lemma31NuReal χ n*(n : ℝ)⁻¹) ≤ 9*lemma23PaperL D^2 := by
  have hH : 0 ≤ (harmonic (D^2) : ℝ) := by
    simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
    exact Finset.sum_nonneg (fun _ _ => by positivity)
  have hb : (harmonic (D^2) : ℝ) ≤ 3*lemma23PaperL D := by
    have he := harmonic_le_one_add_log (D^2)
    rw [Nat.cast_pow,Real.log_pow] at he
    change (harmonic (D^2) : ℝ) ≤ 1+2*lemma23PaperL D at he
    linarith
  calc
    _ ≤ (harmonic (D^2) : ℝ)^2 := lemma31_nu_weighted_sum_le_harmonic_sq χ (D^2)
    _ ≤ (3*lemma23PaperL D)^2 := pow_le_pow_left₀ hH hb 2
    _ = _ := by ring

lemma lemma31_nu_total_paper_weight_le {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 1 ≤ lemma23PaperL D) (hA : NormalizedAssumptionA χ)
    (hAbs : (Real.sqrt (D : ℝ))⁻¹ ≤ lemma23PaperL D^(-2013 : ℤ)) :
    (∑ n ∈ Finset.Icc 1 (lemma31PaperCutoff D), lemma31NuReal χ n*(n : ℝ)⁻¹) ≤
      30*lemma23PaperL D^2 := by
  have hc := lemma31_D_square_le_paper_cutoff hD hL
  have hsetN : Finset.Icc 1 (lemma31PaperCutoff D) = Finset.Ioc 0 (lemma31PaperCutoff D) :=
    Finset.Icc_add_one_left_eq_Ioc (0 : ℕ) _
  have hsetM : Finset.Icc 1 (D^2) = Finset.Ioc 0 (D^2) :=
    Finset.Icc_add_one_left_eq_Ioc (0 : ℕ) _
  have hs : (∑ n ∈ Finset.Icc 1 (lemma31PaperCutoff D), lemma31NuReal χ n*(n : ℝ)⁻¹) =
      (∑ n ∈ Finset.Icc 1 (D^2), lemma31NuReal χ n*(n : ℝ)⁻¹) +
        (∑ n ∈ Finset.Ioc (D^2) (lemma31PaperCutoff D), lemma31NuReal χ n*(n : ℝ)⁻¹) := by
    rw [hsetN,hsetM]
    exact (Finset.sum_Ioc_consecutive (fun n => lemma31NuReal χ n*(n : ℝ)⁻¹)
      (Nat.zero_le (D^2)) hc).symm
  have hn : lemma23PaperL D^(-2013 : ℤ) ≤ 1 :=
    zpow_le_one_of_nonpos₀ hL (by norm_num)
  have hl2 : 1 ≤ lemma23PaperL D^2 := one_le_pow₀ hL
  rw [hs]
  calc
    _ ≤ 9*lemma23PaperL D^2 + 21*lemma23PaperL D^(-2013 : ℤ) :=
      add_le_add (lemma31_nu_small_weighted_sum_le χ hL)
        (lemma31_nu_linear_paper_tail_le χ hD hL hA hAbs)
    _ ≤ _ := by nlinarith

end ZhangLS.Spec
