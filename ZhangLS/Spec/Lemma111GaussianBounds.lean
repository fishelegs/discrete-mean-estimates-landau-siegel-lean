import ZhangLS.Spec.Lemma111GaussianPrimitive

/-! # Quantitative primitive error for the actual Lemma 11.1 Gaussian -/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace ZhangLS.Spec

open MeasureTheory
open scoped Real

lemma lemma111_sqrt_pi_ge_one : (1 : ℝ) ≤ Real.sqrt Real.pi := by
  simpa using Real.sqrt_le_sqrt (by linarith [Real.one_le_pi_div_two] : 1 ≤ Real.pi)

/-- A Mills-type bound sufficient for the primitive approximation.  Multiplying
by the displacement cancels the denominator in the Gaussian tail estimate. -/
lemma lemma111_negative_weighted_tail {D : ℕ} (hD : 1 < D) {t : ℝ} (ht : t ≤ 0) :
    (-t) * lemma111Profile D t ≤
      Real.exp (-((lemma111Scale D * t) ^ 2)) / lemma111Scale D := by
  have hA := lemma111_scale_pos hD
  by_cases ht0 : t = 0
  · simp [ht0]
    positivity
  have ht' : t < 0 := lt_of_le_of_ne ht ht0
  have hK : 0 < -(lemma111Scale D * t) := neg_pos.mpr (mul_neg_of_pos_of_neg hA ht')
  have hend : zhangGaussianEndpoint D
      (Real.exp (lemma23PaperL D ^ 9 * t)) ≤ 0 := by
    rw [lemma111_endpoint]
    exact (neg_pos.mp hK).le
  have hg := zhangGaussianWeight_eq_tail_of_endpoint_nonpos hend
  rw [lemma111_endpoint] at hg
  have hb := zhangGaussianTail_le_exp_linear hK (le_refl _)
  have hs : (Real.sqrt Real.pi)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ lemma111_sqrt_pi_ge_one
  calc
    (-t) * lemma111Profile D t =
        (-t) * ((Real.sqrt Real.pi)⁻¹ *
          ∫ x in Set.Ioi (-(lemma111Scale D * t)), Real.exp (-(x ^ 2))) := by
            rw [lemma111Profile, hg]
    _ ≤ (-t) * ((Real.sqrt Real.pi)⁻¹ *
        (Real.exp (-(-(lemma111Scale D * t)) * (-(lemma111Scale D * t))) /
          (-(lemma111Scale D * t)))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (Real.sqrt_nonneg _))) (neg_nonneg.mpr ht)
    _ = (Real.sqrt Real.pi)⁻¹ *
        (Real.exp (-((lemma111Scale D * t) ^ 2)) / lemma111Scale D) := by
      have hex : -(-(lemma111Scale D * t)) * (-(lemma111Scale D * t)) =
          -((lemma111Scale D * t) ^ 2) := by ring
      rw [hex]
      field_simp
    _ ≤ _ := by
      simpa using mul_le_mul_of_nonneg_right hs
        (div_nonneg (Real.exp_pos _).le hA.le)

lemma lemma111_linear_primitive_error {D : ℕ} (hD : 1 < D) (t : ℝ) :
    |t * lemma111Profile D t - max t 0| ≤
      Real.exp (-((lemma111Scale D * t) ^ 2)) / lemma111Scale D := by
  by_cases ht : t ≤ 0
  · rw [max_eq_right ht, sub_zero, abs_of_nonpos
      (mul_nonpos_of_nonpos_of_nonneg ht (lemma111_profile_nonneg hD t))]
    simpa only [neg_mul] using lemma111_negative_weighted_tail hD ht
  · have ht' : 0 ≤ t := le_of_not_ge ht
    rw [max_eq_left ht', abs_of_nonpos]
    · have hc := lemma111_profile_complement D t
      have hb := lemma111_negative_weighted_tail hD (neg_nonpos.mpr ht')
      have he : (lemma111Scale D * -t) ^ 2 = (lemma111Scale D * t) ^ 2 := by ring
      rw [he] at hb
      have hct := congrArg (fun x : ℝ => t * x) hc
      nlinarith only [hct, hb]
    · have hg := mul_le_mul_of_nonneg_left (lemma111_profile_le_one hD t) ht'
      linarith

/-- The primitive differs from the positive part by an explicitly bounded
Gaussian error, uniformly even at the transition point. -/
lemma lemma111_primitive_error {D : ℕ} (hD : 1 < D) (t : ℝ) :
    |lemma111Primitive D t - max t 0| ≤
      2 * Real.exp (-((lemma111Scale D * t) ^ 2)) / lemma111Scale D := by
  have hA := lemma111_scale_pos hD
  have hπ := lemma111_sqrt_pi_ge_one
  have hden : lemma111Scale D ≤ 2 * lemma111Scale D * Real.sqrt Real.pi := by
    nlinarith only [hA, hπ]
  have he : 0 ≤ Real.exp (-((lemma111Scale D * t) ^ 2)) := (Real.exp_pos _).le
  calc
    _ = |(t * lemma111Profile D t - max t 0) +
        Real.exp (-((lemma111Scale D * t) ^ 2)) /
          (2 * lemma111Scale D * Real.sqrt Real.pi)| := by
      congr 1
      unfold lemma111Primitive
      ring
    _ ≤ |t * lemma111Profile D t - max t 0| +
        |Real.exp (-((lemma111Scale D * t) ^ 2)) /
          (2 * lemma111Scale D * Real.sqrt Real.pi)| := abs_add_le _ _
    _ ≤ Real.exp (-((lemma111Scale D * t) ^ 2)) / lemma111Scale D +
        Real.exp (-((lemma111Scale D * t) ^ 2)) / lemma111Scale D := by
      apply add_le_add (lemma111_linear_primitive_error hD t)
      rw [abs_of_nonneg (by positivity)]
      exact div_le_div_of_nonneg_left he hA hden
    _ = _ := by ring

lemma lemma111_primitive_error_uniform {D : ℕ} (hD : 1 < D) (t : ℝ) :
    |lemma111Primitive D t - max t 0| ≤ 2 / lemma111Scale D := by
  refine (lemma111_primitive_error hD t).trans ?_
  apply div_le_div_of_nonneg_right _ (lemma111_scale_pos hD).le
  have he := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg (lemma111Scale D * t)))
  linarith

lemma lemma111_primitive_error_away {D : ℕ} (hD : 1 < D) {t R : ℝ}
    (hR : 0 ≤ R) (ht : R ≤ |lemma111Scale D * t|) :
    |lemma111Primitive D t - max t 0| ≤
      2 * Real.exp (-(R ^ 2)) / lemma111Scale D := by
  refine (lemma111_primitive_error hD t).trans ?_
  apply div_le_div_of_nonneg_right _ (lemma111_scale_pos hD).le
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  nlinarith only [hR, ht, sq_abs (lemma111Scale D * t)]

end ZhangLS.Spec
