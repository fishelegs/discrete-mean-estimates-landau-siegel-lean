import ZhangLS.Spec.Proposition71CoefficientEnergy
import ZhangLS.Spec.Proposition71DivisorWeights
import ZhangLS.Spec.Lemma32SeriesConvergence

/-! # Genuine summable τ₅ envelopes for the infinite Section7 coefficient tails -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex
set_option maxHeartbeats 2000000

lemma proposition71_tau_five_quadratic_summable :
    Summable (fun n : ℕ => (lemma34Tau 5 n : ℝ)/(n : ℝ)^2) := by
  have hs := (lemma32_tau_lseries_summable 4 (2 : ℂ) (by norm_num)).norm
  apply hs.congr
  intro n
  by_cases hn : n=0
  · subst n; simp
  · simp [LSeries.norm_term_eq,hn,Complex.norm_natCast,Real.rpow_two]

noncomputable def proposition71TauFiveQuadraticMass : ℝ :=
  ∑' n : ℕ, (lemma34Tau 5 n : ℝ)/(n : ℝ)^2

lemma proposition71_tau_five_quadratic_mass_pos : 0<proposition71TauFiveQuadraticMass := by
  have hh := proposition71_tau_five_quadratic_summable.le_tsum 1 (fun n hn => by positivity)
  have he : lemma34Tau 5 1=1 := (lemma34_tau_multiplicative 5).map_one
  have h1 : 1≤proposition71TauFiveQuadraticMass := by
    simpa [he,proposition71TauFiveQuadraticMass] using hh
  linarith

lemma proposition71_actual_dilated_kappa_majorant (D : ℕ) (c : ℝ) (d : ℕ)
    {B : ℝ} (hB : 0≤B) (a : ℕ → ℂ) (ha : ∀n, ‖a n‖≤B) (n : ℕ) :
    ‖(lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a) (d*n)‖≤
      B*(lemma34Tau 5 d : ℝ)*(lemma34Tau 5 n : ℝ) := by
  have hh := proposition71_actual_convolution_le_tau_five (lemma83PaperBeta D c)
    (lemma83_beta_re D c) hB a ha (d*n)
  have ht : (lemma34Tau 5 (d*n) : ℝ)≤(lemma34Tau 5 d : ℝ)*(lemma34Tau 5 n : ℝ) := by
    exact_mod_cast proposition71_tau_submultiplicative 5 d n
  exact (hh.trans (mul_le_mul_of_nonneg_left ht hB)).trans_eq (by ring)

/-- Absolute convergence from a proved pointwise τ₅/n² majorant. -/
theorem proposition71_tau_dominated_series_summable {f : ℕ → ℂ} {K : ℝ}
    (hK : 0≤K) (hf : ∀n, ‖f n‖≤K*((lemma34Tau 5 n : ℝ)/(n : ℝ)^2)) :
    Summable f := by
  apply summable_norm_iff.mp
  exact (proposition71_tau_five_quadratic_summable.mul_left K).of_nonneg_of_le
    (fun n => norm_nonneg _) hf

/-- The majorizing constant is an actual fixed convergent series independent
of D, coefficients, characters, heights, and conductor variables. -/
theorem proposition71_tau_dominated_tsum_bound {f : ℕ → ℂ} {K : ℝ}
    (hK : 0≤K) (hf : ∀n, ‖f n‖≤K*((lemma34Tau 5 n : ℝ)/(n : ℝ)^2)) :
    ‖∑' n, f n‖≤K*proposition71TauFiveQuadraticMass := by
  have hs := proposition71_tau_dominated_series_summable hK hf
  apply (norm_tsum_le_tsum_norm hs.norm).trans
  have hh := Summable.tsum_le_tsum hf hs.norm (proposition71_tau_five_quadratic_summable.mul_left K)
  simpa only [tsum_mul_left,proposition71TauFiveQuadraticMass] using hh

end ZhangLS.Spec
