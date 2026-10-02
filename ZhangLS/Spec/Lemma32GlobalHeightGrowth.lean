import ZhangLS.Spec.Lemma32StripLSeriesGrowth
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Metric Set Filter
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma32_smoothing_strip_growth (D : ℕ) (hD : 0 < D) (w : ℂ) (hw : w.re ≤ 1) :
    ‖lemma32SmoothingDifference (lemma23PaperL D) w‖ ≤ 2*(D : ℝ)^8 := by
  have hd : 0 < (D : ℝ) := Nat.cast_pos.mpr hD
  have hl : 0 ≤ lemma23PaperL D := Real.log_nonneg (Nat.one_le_cast.mpr hD)
  have he : Real.exp (8*lemma23PaperL D) = (D : ℝ)^8 := by
    change Real.exp (8*Real.log (D : ℝ)) = (D : ℝ)^8
    simpa only [Nat.cast_ofNat,Real.exp_log hd] using Real.exp_nat_mul (Real.log (D : ℝ)) 8
  have h8 : ‖Complex.exp (8*(lemma23PaperL D : ℂ)*w)‖ ≤ Real.exp (8*lemma23PaperL D) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    norm_num [Complex.mul_re,Complex.mul_im]
    nlinarith
  have h4 : ‖Complex.exp (4*(lemma23PaperL D : ℂ)*w)‖ ≤ Real.exp (8*lemma23PaperL D) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    norm_num [Complex.mul_re,Complex.mul_im]
    nlinarith
  unfold lemma32SmoothingDifference
  calc
    _ ≤ ‖Complex.exp (8*(lemma23PaperL D : ℂ)*w)‖+
        ‖Complex.exp (4*(lemma23PaperL D : ℂ)*w)‖ := norm_sub_le _ _
    _ ≤ Real.exp (8*lemma23PaperL D)+Real.exp (8*lemma23PaperL D) := add_le_add h8 h4
    _ = _ := by rw [he];ring

noncomputable def lemma32GlobalHeightConstant (D : ℕ) : ℝ :=
  2*lemma32RegularProductBound (3/4)*32^8*(1+((20 : ℕ).factorial : ℝ))*(D : ℝ)^20

lemma lemma32_global_height_constant_pos (D : ℕ) (hD : 0 < D) :
    0 < lemma32GlobalHeightConstant D := by
  have hk := lemma32_regular_product_bound_pos (3/4)
  unfold lemma32GlobalHeightConstant
  positivity

lemma lemma32_actual_integrand_height_decay {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (w : ℂ) (hlo : -1/4 ≤ w.re) (hhi : w.re ≤ 1) (ht : 1 ≤ |w.im|) :
    ‖lemma32CircleIntegrand χ w‖ ≤ lemma32GlobalHeightConstant D/|w.im|^4 := by
  have hslo : 3/4 ≤ (1+w).re := by simp only [Complex.add_re,Complex.one_re];linarith
  have hshi : (1+w).re ≤ 2 := by simp only [Complex.add_re,Complex.one_re];linarith
  have ht' : 1 ≤ |(1+w).im| := by simpa using ht
  have hc := lemma32_analytic_correction_global_growth χ (3/4) (by norm_num) (1+w) hslo
  have hz := lemma32_actual_zeta_L_strip_high_growth χ hD (1+w) hslo hshi ht'
  simp only [Complex.add_im,Complex.one_im,zero_add] at hz
  have h0 : w.im ≠ 0 := by intro h;rw [h,abs_zero] at ht;linarith
  have hg := lemma32_gamma_strip_polynomial_decay w hlo hhi h0 20 (by norm_num)
  have hsm := lemma32_smoothing_strip_growth D (by omega) w hhi
  have hk := lemma32_regular_product_bound_pos (3/4)
  have hb1 : ‖lemma32AnalyticCorrection χ (1+w)*(riemannZeta (1+w)*dirichletLFunction χ (1+w))^8‖ ≤
      ((D : ℝ)^4*lemma32RegularProductBound (3/4))*(32*(D : ℝ)*|w.im|^2)^8 := by
    rw [norm_mul,norm_pow]
    exact mul_le_mul hc (pow_le_pow_left₀ (norm_nonneg _) hz 8) (by positivity) (by positivity)
  have hb2 : ‖lemma32SmoothingDifference (lemma23PaperL D) w*Complex.Gamma w‖ ≤
      (2*(D : ℝ)^8)*((1+((20 : ℕ).factorial : ℝ))/|w.im|^20) := by
    rw [norm_mul]
    exact mul_le_mul hsm hg (norm_nonneg _) (by positivity)
  unfold lemma32CircleIntegrand
  rw [norm_mul]
  calc
    _ ≤ ((D : ℝ)^4*lemma32RegularProductBound (3/4))*(32*(D : ℝ)*|w.im|^2)^8*
        ((2*(D : ℝ)^8)*((1+((20 : ℕ).factorial : ℝ))/|w.im|^20)) := by
      exact mul_le_mul hb1 hb2 (norm_nonneg _) (by positivity)
    _ = _ := by
      unfold lemma32GlobalHeightConstant
      have ht0 : |w.im| ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one ht)
      field_simp [ht0]
      <;> ring

end ZhangLS.Spec
