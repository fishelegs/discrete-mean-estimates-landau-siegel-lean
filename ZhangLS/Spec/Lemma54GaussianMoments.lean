import ZhangLS.Spec.Lemma54GaussianNormalization

/-! # Polynomial moments of the actual shifted Gaussian -/

namespace ZhangLS.Spec

open MeasureTheory Set Filter

set_option maxHeartbeats 1000000

theorem lemma54_gaussian_density_continuous (B t : ℝ) :
    Continuous (lemma54GaussianDensity B t) := by
  unfold lemma54GaussianDensity
  fun_prop

theorem lemma54_gaussian_quadratic_envelope {B : ℝ} (hB : 0 < B) (t x : ℝ) :
    (1 + x ^ 2) * lemma54GaussianDensity B t x ≤
      (4 * (1 + t ^ 2) * (1 + 2 * B ^ 2 / Real.pi ^ 2)) *
        lemma54GaussianDensity (2 * B) t x := by
  let b : ℝ := (Real.pi / B) ^ 2 / 2
  have hb : 0 < b := by dsimp [b]; positivity
  have hpoly : 1 + x ^ 2 ≤ 2 * (1 + t ^ 2) * (1 + (x - t) ^ 2) := by
    nlinarith [sq_nonneg (x - 2 * t), sq_nonneg (x - t), sq_nonneg t,
      mul_nonneg (sq_nonneg t) (sq_nonneg (x - t))]
  have hbinv : b⁻¹ = 2 * B ^ 2 / Real.pi ^ 2 := by
    dsimp [b]
    field_simp
  have hdamp : -b * (x - t) ^ 2 ≤ -(Real.pi / (2 * B)) ^ 2 * (x - t) ^ 2 := by
    have heq : (Real.pi / (2 * B)) ^ 2 = b / 2 := by
      dsimp [b]
      field_simp
    rw [heq]
    nlinarith [mul_nonneg hb.le (sq_nonneg (x - t))]
  have htwo : (Real.pi / B) ^ 2 = 2 * b := by dsimp [b]; ring
  rw [lemma54_gaussian_density_factor, lemma54_gaussian_density_factor, htwo]
  calc
    (1 + x ^ 2) * (Real.sqrt Real.pi / B * Real.exp (-(2 * b) * (x - t) ^ 2)) =
        (Real.sqrt Real.pi / B) *
          ((1 + x ^ 2) * Real.exp (-(2 * b) * (x - t) ^ 2)) := by ring
    _ ≤ (Real.sqrt Real.pi / B) *
          (2 * (1 + t ^ 2) * ((1 + (x - t) ^ 2) *
            Real.exp (-(2 * b) * (x - t) ^ 2))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc
        _ ≤ (2 * (1 + t ^ 2) * (1 + (x - t) ^ 2)) *
            Real.exp (-(2 * b) * (x - t) ^ 2) :=
          mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
        _ = _ := by ring
    _ ≤ (Real.sqrt Real.pi / B) *
          (2 * (1 + t ^ 2) * ((1 + b⁻¹) * Real.exp (-b * (x - t) ^ 2))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (one_add_sq_mul_gaussian_le hb (x - t))
          (by positivity)) (by positivity)
    _ ≤ (Real.sqrt Real.pi / B) *
          (2 * (1 + t ^ 2) * ((1 + b⁻¹) *
            Real.exp (-(Real.pi / (2 * B)) ^ 2 * (x - t) ^ 2))) := by
      gcongr
    _ = (4 * (1 + t ^ 2) * (1 + 2 * B ^ 2 / Real.pi ^ 2)) *
          (Real.sqrt Real.pi / (2 * B) *
            Real.exp (-(Real.pi / (2 * B)) ^ 2 * (x - t) ^ 2)) := by
      rw [hbinv]
      ring

theorem lemma54_gaussian_quadratic_integrable {B : ℝ} (hB : 0 < B) (t : ℝ) :
    Integrable (fun x : ℝ => (1 + x ^ 2) * lemma54GaussianDensity B t x) := by
  apply ((lemma54_gaussian_density_integrable (by positivity : 0 < 2 * B) t).const_mul
    (4 * (1 + t ^ 2) * (1 + 2 * B ^ 2 / Real.pi ^ 2))).mono'
  · exact ((continuous_const.add (continuous_id.pow 2)).mul
      (lemma54_gaussian_density_continuous B t)).aestronglyMeasurable
  · apply Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity)
      (lemma54_gaussian_density_pos hB t x).le)]
    exact lemma54_gaussian_quadratic_envelope hB t x

theorem lemma54_gaussian_quadratic_integral_bound {B : ℝ} (hB : 0 < B) (t : ℝ) :
    (∫ x : ℝ, (1 + x ^ 2) * lemma54GaussianDensity B t x) ≤
      4 * (1 + t ^ 2) * (1 + 2 * B ^ 2 / Real.pi ^ 2) := by
  calc
    _ ≤ ∫ x : ℝ, (4 * (1 + t ^ 2) * (1 + 2 * B ^ 2 / Real.pi ^ 2)) *
        lemma54GaussianDensity (2 * B) t x := by
      apply integral_mono_of_nonneg
        (Eventually.of_forall fun x => mul_nonneg (by positivity)
          (lemma54_gaussian_density_pos hB t x).le)
        ((lemma54_gaussian_density_integrable (by positivity : 0 < 2 * B) t).const_mul _)
      exact Eventually.of_forall (lemma54_gaussian_quadratic_envelope hB t)
    _ = _ := by
      rw [integral_const_mul, lemma54_gaussian_density_integral (by positivity : 0 < 2 * B),
        mul_one]

end ZhangLS.Spec
