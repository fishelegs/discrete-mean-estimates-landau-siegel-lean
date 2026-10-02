import ZhangLS.Spec.Lemma32TermMellinIdentity
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma32_Gamma_mellin_tsum_integrable (c : ℕ → ℂ) (B : ℝ) (hB : 0 < B)
    (hc : LSeriesSummable c 2) :
    Integrable (fun t : ℝ => ∑' n : ℕ, lemma32GammaMellinTerm c B n t) := by
  let C := B*∑' n : ℕ, ‖LSeries.term c 2 n‖
  apply (lemma32_gamma_one_vertical_integrable.norm.const_mul C).mono'
  · exact AEStronglyMeasurable.tsum (fun n =>
      (lemma32_Gamma_mellin_term_integrable c B hB n).aestronglyMeasurable)
  · filter_upwards [] with t
    have hn : Summable (fun n => ‖lemma32GammaMellinTerm c B n t‖) := by
      apply (hc.norm.mul_left (B*‖Complex.Gamma (1+(t : ℂ)*I)‖)).congr
      intro n
      rw [lemma32_Gamma_mellin_term_norm c B hB n t]
      ring
    calc
      _ ≤ ∑' n : ℕ, ‖lemma32GammaMellinTerm c B n t‖ := norm_tsum_le_tsum_norm hn
      _ = ∑' n : ℕ, (B*‖Complex.Gamma (1+(t : ℂ)*I)‖)*‖LSeries.term c 2 n‖ := by
        apply tsum_congr
        intro n
        rw [lemma32_Gamma_mellin_term_norm c B hB n t]
        ring
      _ = C*‖Complex.Gamma (1+(t : ℂ)*I)‖ := by rw [tsum_mul_left]; dsimp [C]; ring

lemma lemma32_full_series_gamma_mellin (c : ℕ → ℂ) (B : ℝ) (hB : 0 < B)
    (hc : LSeriesSummable c 2) :
    Summable (fun n : ℕ => LSeries.term c 1 n*(Real.exp (-(n : ℝ)/B) : ℂ)) ∧
    ((1/(2*Real.pi) : ℝ) : ℂ)*(∫ t : ℝ, ∑' n : ℕ, lemma32GammaMellinTerm c B n t) =
      ∑' n : ℕ, LSeries.term c 1 n*(Real.exp (-(n : ℝ)/B) : ℂ) := by
  have hi := hasSum_integral_of_summable_integral_norm
    (fun n => lemma32_Gamma_mellin_term_integrable c B hB n)
    (lemma32_Gamma_mellin_term_integral_norm_summable c B hB hc)
  have hs := hi.mul_left (((1/(2*Real.pi) : ℝ) : ℂ))
  simp_rw [lemma32_Gamma_mellin_term_normalized_integral c B hB] at hs
  exact ⟨hs.summable,hs.tsum_eq.symm⟩

end ZhangLS.Spec
