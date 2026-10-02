import ZhangLS.Spec.Lemma54GaussianMoments

/-! # Exterior mass estimates with reserved Gaussian damping -/

namespace ZhangLS.Spec

open MeasureTheory Set Filter

set_option maxHeartbeats 1000000

theorem lemma54_gaussian_exterior_pointwise {B W t x : ℝ}
    (hB : 0 < B) (hW : 0 ≤ W) (hgap : W ≤ |x - t|) :
    lemma54GaussianDensity B t x ≤
      (2 * Real.exp (-((Real.pi * W / B) ^ 2) / 2)) *
        lemma54GaussianDensity (2 * B) t x := by
  have hsq : W ^ 2 ≤ (x - t) ^ 2 := by
    have h := (sq_le_sq₀ hW (abs_nonneg (x - t))).2 hgap
    simpa only [sq_abs] using h
  have hc : 0 ≤ (Real.pi / B) ^ 2 := sq_nonneg _
  have heqW : (Real.pi * W / B) ^ 2 = (Real.pi / B) ^ 2 * W ^ 2 := by ring
  have heqB : (Real.pi / (2 * B)) ^ 2 = (Real.pi / B) ^ 2 / 4 := by
    field_simp
    norm_num
  have harg : -(Real.pi / B) ^ 2 * (x - t) ^ 2 ≤
      -((Real.pi * W / B) ^ 2) / 2 -
        (Real.pi / (2 * B)) ^ 2 * (x - t) ^ 2 := by
    rw [heqW, heqB]
    nlinarith [mul_le_mul_of_nonneg_left hsq hc,
      mul_nonneg hc (sq_nonneg (x - t))]
  rw [lemma54_gaussian_density_factor, lemma54_gaussian_density_factor]
  calc
    _ ≤ Real.sqrt Real.pi / B *
        Real.exp (-((Real.pi * W / B) ^ 2) / 2 -
          (Real.pi / (2 * B)) ^ 2 * (x - t) ^ 2) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (by positivity)
    _ = _ := by
      rw [sub_eq_add_neg, Real.exp_add]
      ring

theorem lemma54_gaussian_exterior_mass {B W t : ℝ} {S : Set ℝ}
    (hB : 0 < B) (hW : 0 ≤ W) (hS : MeasurableSet S)
    (hgap : ∀ x ∈ S, W ≤ |x - t|) :
    (∫ x : ℝ in S, lemma54GaussianDensity B t x) ≤
      2 * Real.exp (-((Real.pi * W / B) ^ 2) / 2) := by
  let F : ℝ := 2 * Real.exp (-((Real.pi * W / B) ^ 2) / 2)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  calc
    _ ≤ ∫ x : ℝ in S, F * lemma54GaussianDensity (2 * B) t x := by
      apply setIntegral_mono_on
        (lemma54_gaussian_density_integrable hB t).integrableOn
        ((lemma54_gaussian_density_integrable (by positivity : 0 < 2 * B) t).const_mul F).integrableOn hS
      intro x hx
      exact lemma54_gaussian_exterior_pointwise hB hW (hgap x hx)
    _ = F * ∫ x : ℝ in S, lemma54GaussianDensity (2 * B) t x := integral_const_mul _ _
    _ ≤ F * ∫ x : ℝ, lemma54GaussianDensity (2 * B) t x := by
      apply mul_le_mul_of_nonneg_left _ hF
      apply setIntegral_le_integral (lemma54_gaussian_density_integrable (by positivity) t)
      exact Eventually.of_forall fun x => (lemma54_gaussian_density_pos (by positivity) t x).le
    _ = _ := by rw [lemma54_gaussian_density_integral (by positivity : 0 < 2 * B), mul_one]

theorem lemma54_gaussian_exterior_quadratic_mass {B W t : ℝ} {S : Set ℝ}
    (hB : 0 < B) (hW : 0 ≤ W) (hS : MeasurableSet S)
    (hgap : ∀ x ∈ S, W ≤ |x - t|) :
    (∫ x : ℝ in S, (1 + x ^ 2) * lemma54GaussianDensity B t x) ≤
      (8 * (1 + t ^ 2) * (1 + 8 * B ^ 2 / Real.pi ^ 2)) *
        Real.exp (-((Real.pi * W / B) ^ 2) / 2) := by
  let F : ℝ := 2 * Real.exp (-((Real.pi * W / B) ^ 2) / 2)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  calc
    _ ≤ ∫ x : ℝ in S, F * ((1 + x ^ 2) * lemma54GaussianDensity (2 * B) t x) := by
      apply setIntegral_mono_on (lemma54_gaussian_quadratic_integrable hB t).integrableOn
        ((lemma54_gaussian_quadratic_integrable (by positivity : 0 < 2 * B) t).const_mul F).integrableOn hS
      intro x hx
      calc
        _ ≤ (1 + x ^ 2) * (F * lemma54GaussianDensity (2 * B) t x) :=
          mul_le_mul_of_nonneg_left (lemma54_gaussian_exterior_pointwise hB hW (hgap x hx))
            (by positivity)
        _ = _ := by ring
    _ = F * ∫ x : ℝ in S, (1 + x ^ 2) * lemma54GaussianDensity (2 * B) t x := integral_const_mul _ _
    _ ≤ F * ∫ x : ℝ, (1 + x ^ 2) * lemma54GaussianDensity (2 * B) t x := by
      apply mul_le_mul_of_nonneg_left _ hF
      apply setIntegral_le_integral (lemma54_gaussian_quadratic_integrable (by positivity) t)
      exact Eventually.of_forall fun x => mul_nonneg (by positivity)
        (lemma54_gaussian_density_pos (by positivity) t x).le
    _ ≤ F * (4 * (1 + t ^ 2) * (1 + 2 * (2 * B) ^ 2 / Real.pi ^ 2)) :=
      mul_le_mul_of_nonneg_left (lemma54_gaussian_quadratic_integral_bound (by positivity) t) hF
    _ = _ := by dsimp [F]; ring

end ZhangLS.Spec
