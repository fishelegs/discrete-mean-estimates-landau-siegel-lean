import ZhangLS.Spec.Lemma84Definitions
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex
set_option maxHeartbeats 1000000

/-- Taylor errors in a quotient remain additive; no main-term coefficient
is divided out in the statement. -/
lemma lemma84_quotient_error_identity (A s a b F₀ F₁ F₂ : ℂ)
    (hs : s ≠ 0) (hF : F₀ ≠ 0) :
    F₁*F₂/F₀-A*(s+a)*(s+b)/s =
      ((F₁-A*(s+a))*F₂ + A*(s+a)*(F₂-A*(s+b)) -
        (A*(s+a)*(s+b)/s)*(F₀-A*s))/F₀ := by
  field_simp
  <;> ring

lemma lemma84_quotient_taylor_error
    (A s a b F₀ F₁ F₂ : ℂ) (α E : ℝ)
    (hα : 0 < α) (hA : 0 < ‖A‖) (hE : 0 ≤ E)
    (hs : ‖s‖ = 5*α) (ha : ‖a‖ ≤ 3*α) (hb : ‖b‖ ≤ 3*α)
    (hsmall : E ≤ ‖A‖*α)
    (h₀ : ‖F₀-A*s‖ ≤ E) (h₁ : ‖F₁-A*(s+a)‖ ≤ E)
    (h₂ : ‖F₂-A*(s+b)‖ ≤ E) :
    ‖F₁*F₂/F₀-A*(s+a)*(s+b)/s‖ ≤ 8*E := by
  have hsa : ‖s+a‖ ≤ 8*α := (norm_add_le _ _).trans (by linarith)
  have hsb : ‖s+b‖ ≤ 8*α := (norm_add_le _ _).trans (by linarith)
  have hs0 : s ≠ 0 := by intro h; rw [h,norm_zero] at hs; linarith
  have hFbound : 4*‖A‖*α ≤ ‖F₀‖ := by
    have h := norm_sub_norm_le (A*s) F₀
    rw [norm_mul,hs,norm_sub_rev] at h
    nlinarith only [h,h₀,hsmall]
  have hFpos : 0 < ‖F₀‖ := (by positivity : 0 < 4*‖A‖*α).trans_le hFbound
  have hF0 : F₀ ≠ 0 := norm_pos_iff.mp hFpos
  have hF₂bound : ‖F₂‖ ≤ 9*‖A‖*α := by
    have h : ‖F₂‖ ≤ ‖F₂-A*(s+b)‖+‖A*(s+b)‖ := by
      simpa using norm_add_le (F₂-A*(s+b)) (A*(s+b))
    rw [norm_mul] at h
    have hmul := mul_le_mul_of_nonneg_left hsb hA.le
    nlinarith only [h,hmul,h₂,hsmall]
  rw [lemma84_quotient_error_identity A s a b F₀ F₁ F₂ hs0 hF0,norm_div]
  apply (div_le_iff₀ hFpos).mpr
  have hmain : ‖A*(s+a)*(s+b)/s‖ ≤ 13*‖A‖*α := by
    rw [norm_div,norm_mul,norm_mul,hs]
    apply (div_le_iff₀ (by positivity : 0 < 5*α)).mpr
    have hprod := mul_le_mul hsa hsb (norm_nonneg _) (by positivity : 0 ≤ 8*α)
    have hmul := mul_le_mul_of_nonneg_left hprod hA.le
    nlinarith only [hmul,mul_pos hA (sq_pos_of_pos hα)]
  have hfirst : ‖(F₁-A*(s+a))*F₂‖ ≤ 9*‖A‖*α*E := by
    rw [norm_mul]
    have h := mul_le_mul h₁ hF₂bound (norm_nonneg _) hE
    nlinarith only [h]
  have hsecond : ‖A*(s+a)*(F₂-A*(s+b))‖ ≤ 8*‖A‖*α*E := by
    simp only [norm_mul]
    have h := mul_le_mul (mul_le_mul_of_nonneg_left hsa hA.le) h₂
      (norm_nonneg _) (by positivity : 0 ≤ ‖A‖*(8*α))
    nlinarith only [h]
  have hthird : ‖(A*(s+a)*(s+b)/s)*(F₀-A*s)‖ ≤ 13*‖A‖*α*E := by
    rw [norm_mul]
    have h := mul_le_mul hmain h₀ (norm_nonneg _) (by positivity : 0 ≤ 13*‖A‖*α)
    nlinarith only [h]
  have hsum := (norm_sub_le ((F₁-A*(s+a))*F₂ + A*(s+a)*(F₂-A*(s+b)))
    ((A*(s+a)*(s+b)/s)*(F₀-A*s))).trans
      (add_le_add (norm_add_le _ _) le_rfl)
  have hscale := mul_le_mul_of_nonneg_right hFbound hE
  nlinarith only [hsum,hfirst,hsecond,hthird,hscale,mul_nonneg (mul_nonneg hA.le hα.le) hE]

end ZhangLS.Spec
