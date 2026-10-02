import ZhangLS.Spec.Lemma34DivisorSquare
import ZhangLS.Spec.Lemma34WeightedConvolution
import ZhangLS.Spec.Lemma34TupleConvolution
set_option autoImplicit false
namespace ZhangLS.Spec
set_option maxHeartbeats 2000000

lemma lemma34_actual_tau40_square_le_tau1600 (n : ℕ) :
    lemma23Tau40 n^2 ≤ (lemma34Tau 1600 n : ℝ) := by
  have hn : 0 ≤ lemma23Tau40 n := by
    unfold lemma23Tau40
    apply Finset.sum_nonneg
    intro p hp
    apply Finset.prod_nonneg
    intro i hi
    positivity
  calc
    _ ≤ (lemma34Tau 40 n : ℝ)^2 :=
      (sq_le_sq₀ hn (by positivity)).mpr (lemma34_actual_tau40_le_standard n)
    _ ≤ _ := by exact_mod_cast lemma34_tau40_square_le_tau1600 n

lemma lemma34_actual_tau40_weighted_sum_le (X : ℕ) (hX : 1 ≤ X) :
    (∑ n ∈ Finset.Icc 1 X, lemma23Tau40 n^2 * (n : ℝ)⁻¹) ≤
      (1 + Real.log (X : ℝ))^1600 := by
  have hH : 0 ≤ (harmonic X : ℝ) := by
    simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
    exact Finset.sum_nonneg (fun _ _ => by positivity)
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 X, (lemma34Tau 1600 n : ℝ) * (n : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      exact mul_le_mul_of_nonneg_right (lemma34_actual_tau40_square_le_tau1600 n)
        (by positivity)
    _ ≤ (harmonic X : ℝ)^1600 := lemma34_tau_weighted_sum_le_harmonic_pow 1600 X hX
    _ ≤ _ := pow_le_pow_left₀ hH (harmonic_le_one_add_log X) _

lemma lemma34_majorized_coefficient_weighted_sum (c : ℕ → ℂ)
    (hc : ∀ n, ‖c n‖ ≤ lemma23Tau40 n) (X : ℕ) (hX : 1 ≤ X) :
    (∑ n ∈ Finset.Icc 1 X, ‖c n‖^2 * (n : ℝ)⁻¹) ≤
      (1 + Real.log (X : ℝ))^1600 := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 X, lemma23Tau40 n^2 * (n : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans (hc n))).mpr (hc n)
    _ ≤ _ := lemma34_actual_tau40_weighted_sum_le X hX

end ZhangLS.Spec
