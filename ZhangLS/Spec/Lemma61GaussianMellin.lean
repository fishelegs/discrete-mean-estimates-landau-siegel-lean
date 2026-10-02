import ZhangLS.Spec.Lemma61GaussianWeights

/-! # Actual Gaussian inputs for the original Lemma 6.1

The original family, strict region, actual K/N and actual E1 are retained.
Gaussian inversion and both cutoff errors are proved for the actual weights.
The full Lemma61Target remains unproved: contour and Z-difference bounds remain.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Real Topology
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

lemma lemma61_right_mellin_integrand_eq_tsum {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (s : ℂ) (B : ℝ) {σ : ℝ}
    (hs : 1 < s.re + σ) (t : ℝ) :
    lemma61RightMellinIntegrand (D := D) ψ s B σ t * I =
      ∑' n : ℕ, lemma44MellinSeriesTerm D (fun n => ψ (n : ZMod p)) s B σ n t := by
  have hsr : 1 < (s + ((σ : ℂ) + (t : ℂ) * I)).re := by simpa using hs
  rw [lemma61RightMellinIntegrand,DirichletCharacter.LFunction_eq_LSeries ψ hsr]
  unfold LSeries lemma44MellinSeriesTerm
  simp_rw [div_eq_mul_inv,mul_assoc]
  rw [tsum_mul_right]

lemma lemma61_actual_right_gaussian_mellin {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (s : ℂ) (hD : 1 < D)
    {B σ : ℝ} (hB : 0 < B) (hσ : 0 < σ) (hs : 1 < s.re + σ) :
    Integrable (lemma61RightMellinIntegrand (D := D) ψ s B σ) ∧
      Summable (fun n : ℕ => LSeries.term (fun m => ψ (m : ZMod p)) s n *
        (zhangGaussianWeight D (B / n) : ℂ)) ∧
      (2 * (Real.pi : ℂ) * I)⁻¹ *
        (∫ t : ℝ, lemma61RightMellinIntegrand (D := D) ψ s B σ t * I) =
          ∑' n : ℕ, LSeries.term (fun m => ψ (m : ZMod p)) s n *
            (zhangGaussianWeight D (B / n) : ℂ) := by
  let c : ℕ → ℂ := fun n => ψ (n : ZMod p)
  have habs : LSeriesSummable c ((s.re + σ : ℝ) : ℂ) :=
    DirichletCharacter.LSeriesSummable_of_one_lt_re ψ (by simpa using hs)
  have ht := lemma44MellinSeriesTerm_tsum_integrable hD c s B hσ.ne' habs
  have hti : Integrable (fun t : ℝ =>
      lemma61RightMellinIntegrand (D := D) ψ s B σ t * I) := by
    apply ht.congr
    filter_upwards [] with t
    exact (lemma61_right_mellin_integrand_eq_tsum ψ s B hs t).symm
  have hi : Integrable (lemma61RightMellinIntegrand (D := D) ψ s B σ) := by
    simpa only [mul_assoc,I_mul_I,mul_neg,mul_one,neg_neg] using (hti.mul_const (-I))
  refine ⟨hi,(lemma44_full_series_gaussian_mellin hD c s hB hσ habs).1,?_⟩
  simp_rw [lemma61_right_mellin_integrand_eq_tsum ψ s B hs]
  exact (lemma44_full_series_gaussian_mellin hD c s hB hσ habs).2

lemma lemma61_actual_right_mellin_with_cutoff_correction {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (s : ℂ) (hD : 1 < D)
    {B σ : ℝ} (hB : 0 < B) (hσ : 0 < σ) (hs : 1 < s.re + σ) :
    (2 * (Real.pi : ℂ) * I)⁻¹ *
      (∫ t : ℝ, lemma61RightMellinIntegrand (D := D) ψ s B σ t * I) =
        lemma61WeightedPolynomial D ψ B s + lemma61GaussianCutoffCorrection D ψ B s := by
  have hg := (lemma61_actual_right_gaussian_mellin ψ s hD hB hσ hs).2.1
  have ht := lemma61_actual_weighted_terms_summable (D := D) ψ B s
  have he : lemma61GaussianCutoffCorrection D ψ B s =
      (∑' n : ℕ, LSeries.term (fun m => ψ (m : ZMod p)) s n *
        (zhangGaussianWeight D (B / n) : ℂ)) - lemma61WeightedPolynomial D ψ B s := by
    rw [lemma61GaussianCutoffCorrection]
    simp_rw [Complex.ofReal_sub,mul_sub]
    rw [hg.tsum_sub ht]
    congr 1
    rw [← lemma61_actual_weighted_tsum_eq_finite ψ B s]
    exact tsum_congr (fun n => (lemma61_weighted_term_eq_LSeries_term ψ B s n).symm)
  rw [(lemma61_actual_right_gaussian_mellin ψ s hD hB hσ hs).2.2,he]
  ring

lemma lemma61_actual_K_right_mellin_identity {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (s : ℂ) (hD : 1 < D)
    {σ : ℝ} (hσ : 0 < σ) (hs : 1 < s.re + σ) :
    (2 * (Real.pi : ℂ) * I)⁻¹ *
      (∫ t : ℝ, lemma61RightMellinIntegrand (D := D) ψ s (lemma61PaperP4 D) σ t * I) =
        lemma61ActualK D ψ s + lemma61GaussianCutoffCorrection D ψ (lemma61PaperP4 D) s :=
  lemma61_actual_right_mellin_with_cutoff_correction ψ s hD (lemma61_P4_pos hD) hσ hs

end ZhangLS.Spec
