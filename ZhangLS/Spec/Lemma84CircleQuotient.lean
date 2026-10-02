import ZhangLS.Spec.Lemma84QuotientAlgebra
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Metric
set_option maxHeartbeats 1000000

lemma lemma84_actual_derivative_norm_lower {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hDN : lemma57ExplicitModulusThreshold ≤ D) (hA : NormalizedAssumptionA χ) :
    (1 : ℝ)/16 ≤ ‖LDerivAtOne χ‖ := by
  have hD := lemma57_one_lt_of_explicit_threshold hDN
  have hder := lemma57_one_sixteenth_at_explicit_threshold χ hDN hA
  have hscale := lemma57Scale_ge_one hD
  rw [LDerivAtOne_eq_realLDerivAtOne χ hD,Complex.norm_real,Real.norm_eq_abs]
  exact (show (1 : ℝ)/16 ≤ realLDerivAtOne χ by nlinarith only [hder,hscale]).trans
    (le_abs_self _)

lemma lemma84_circle_taylor_budget {D : ℕ}
    (hL : 2000 ≤ lemma23PaperL D) (hC : lemma58ErrorConstant ≤ lemma23PaperL D) :
    lemma58ErrorConstant * lemma23PaperL D^(-15 : ℤ) ≤ lemma44PaperAlpha D/16 := by
  let L := lemma23PaperL D
  have hLp : 0 < L := by dsimp [L]; linarith
  have hL1 : 1 ≤ L := by dsimp [L]; linarith
  have h5 : L ≤ L^5 := by simpa using pow_le_pow_right₀ hL1 (show 1 ≤ 5 by norm_num)
  have hlarge : 16 ≤ Real.pi*L^5 := by
    have hp := mul_le_mul_of_nonneg_left h5 Real.pi_pos.le
    have hpi := Real.two_le_pi
    dsimp [L] at *
    nlinarith only [hL,hp,hpi]
  calc
    _ ≤ L*L^(-15 : ℤ) := mul_le_mul_of_nonneg_right hC (zpow_nonneg hLp.le _)
    _ = L^(-14 : ℤ) := by simpa using (zpow_add₀ hLp.ne' 1 (-15)).symm
    _ ≤ lemma44PaperAlpha D/16 := by
      rw [lemma58_alpha_eq_log_power]
      change L^(-14 : ℤ) ≤ Real.pi*L^(-9 : ℤ)/16
      rw [zpow_neg,zpow_ofNat,zpow_neg,zpow_ofNat]
      have hp14 : L^14 = L^5*L^9 := by ring
      rw [hp14]
      apply (le_div_iff₀ (by norm_num : (0:ℝ)<16)).mpr
      rw [mul_comm ((L^5*L^9)⁻¹) 16, ← div_eq_mul_inv, ← div_eq_mul_inv]
      apply (div_le_div_iff₀ (mul_pos (pow_pos hLp 5) (pow_pos hLp 9)) (pow_pos hLp 9)).mpr
      nlinarith only [mul_le_mul_of_nonneg_right hlarge (pow_pos hLp 9).le]

/-- A logarithmic-square derivative bound, proved by an actual Cauchy circle. -/
lemma lemma84_actual_derivative_norm_upper {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 2 ≤ lemma23PaperL D) :
    ‖LDerivAtOne χ‖ ≤ 16*Real.exp 1*lemma23PaperL D^2 := by
  let L := lemma23PaperL D
  let R := 1/(4*L)
  have hLp : 0 < L := by dsimp [L]; linarith
  have hRp : 0 < R := by dsimp [R]; positivity
  have hdiff := differentiable_dirichletLFunction_of_one_lt_modulus χ hD
  have hbound (z : ℂ) (hz : z ∈ sphere 1 R) :
      ‖dirichletLFunction χ z‖ ≤ 4*Real.exp 1*L := by
    have hdist := mem_sphere_iff_norm.mp hz
    have hR : R ≤ 1/L := by dsimp [R]; apply one_div_le_one_div_of_le hLp; linarith
    have hR2 : R ≤ 1 := by
      dsimp [R]
      apply (div_le_one (by positivity : 0 < 4*L)).mpr
      dsimp [L]; linarith
    have hre := Complex.abs_re_le_norm (z-1)
    simp only [Complex.sub_re,Complex.one_re,hdist] at hre
    apply lemma55_actual_L_near_one_bound χ hD hL
    · have hlow := (abs_le.mp hre).1
      change 1-1/L ≤ z.re
      linarith
    · have hh : ‖z‖ ≤ ‖z-1‖+1 := by simpa using norm_add_le (z-1) (1:ℂ)
      rw [hdist] at hh
      linarith
  have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    (f := dirichletLFunction χ) (c := 1) (R := R) (C := 4*Real.exp 1*L)
    1 hRp hdiff.diffContOnCl hbound
  change ‖deriv (dirichletLFunction χ) 1‖ ≤ _
  calc
    _ ≤ (4*Real.exp 1*L)/R := by simpa using hc
    _ = _ := by dsimp [R,L]; field_simp; ring

/-- The ratio asserted in the proof of original 8.4, on the full circle.
The Taylor input is completed Lemma 5.8, and the denominator lower bound is
proved from (A) and completed Lemma 5.7. -/
lemma lemma84_actual_circle_quotient {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hDN : lemma57ExplicitModulusThreshold ≤ D) (hA : NormalizedAssumptionA χ)
    (hC : lemma58ErrorConstant ≤ lemma23PaperL D)
    (a b s : ℂ) (ha : ‖a‖ ≤ 3*lemma44PaperAlpha D)
    (hb : ‖b‖ ≤ 3*lemma44PaperAlpha D) (hs : ‖s‖ = 5*lemma44PaperAlpha D) :
    ‖dirichletLFunction χ (1+s+a)*dirichletLFunction χ (1+s+b)/
        dirichletLFunction χ (1+s) - LDerivAtOne χ*(s+a)*(s+b)/s‖ ≤
      (8*lemma58ErrorConstant)*lemma23PaperL D^(-15 : ℤ) := by
  have hD := lemma57_one_lt_of_explicit_threshold hDN
  have hL : 2000 ≤ lemma23PaperL D := by
    have hh := lemma57_log_ge_ten_million hDN
    change 2000 ≤ Real.log (D:ℝ)
    linarith
  have hLp : 0 < lemma23PaperL D := by linarith
  have hα := (lemma83_alpha_small (by linarith only [hL] : 100 ≤ lemma23PaperL D)).1
  have hder := lemma84_actual_derivative_norm_lower χ hDN hA
  have htaylor (w : ℂ) (hw : ‖w‖ ≤ 10*lemma44PaperAlpha D) :
      ‖dirichletLFunction χ (1+w)-LDerivAtOne χ*w‖ ≤
        lemma58ErrorConstant*lemma23PaperL D^(-15 : ℤ) := by
    simpa only [add_sub_cancel_left] using
      lemma58_actual_full_disk_linear_error χ hD hL hA
        (s := 1+w) (by simpa only [add_sub_cancel_left] using hw)
  have h := lemma84_quotient_taylor_error (LDerivAtOne χ) s a b
    (dirichletLFunction χ (1+s)) (dirichletLFunction χ (1+s+a))
    (dirichletLFunction χ (1+s+b)) (lemma44PaperAlpha D)
    (lemma58ErrorConstant*lemma23PaperL D^(-15 : ℤ)) hα (by linarith) (by positivity [lemma58_error_constant_pos])
    hs ha hb ?_ ?_ ?_ ?_
  · simpa only [mul_assoc] using h
  · exact (lemma84_circle_taylor_budget hL hC).trans (by nlinarith only [mul_le_mul_of_nonneg_right hder hα.le])
  · exact htaylor s (by linarith)
  · simpa only [add_assoc] using htaylor (s+a)
      ((norm_add_le _ _).trans (by linarith))
  · simpa only [add_assoc] using htaylor (s+b)
      ((norm_add_le _ _).trans (by linarith))

lemma lemma84_actual_circle_denominator_ne_zero {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hDN : lemma57ExplicitModulusThreshold ≤ D) (hA : NormalizedAssumptionA χ)
    (hC : lemma58ErrorConstant ≤ lemma23PaperL D)
    {s : ℂ} (hs : ‖s‖ = 5*lemma44PaperAlpha D) :
    dirichletLFunction χ (1+s) ≠ 0 := by
  have hD := lemma57_one_lt_of_explicit_threshold hDN
  have hL : 2000 ≤ lemma23PaperL D := by
    change 2000 ≤ Real.log (D:ℝ)
    linarith [lemma57_log_ge_ten_million hDN]
  have hα := (lemma83_alpha_small (by linarith only [hL] : 100 ≤ lemma23PaperL D)).1
  have hder := lemma84_actual_derivative_norm_lower χ hDN hA
  have ht := lemma58_actual_full_disk_linear_error χ hD hL hA
    (s := 1+s) (by simp only [add_sub_cancel_left]; linarith)
  have hb := lemma84_circle_taylor_budget hL hC
  intro he
  rw [he,zero_sub,norm_neg,add_sub_cancel_left,norm_mul,hs] at ht
  change ‖LDerivAtOne χ‖*(5*lemma44PaperAlpha D) ≤
    lemma58ErrorConstant*lemma23PaperL D^(-15 : ℤ) at ht
  nlinarith only [ht,hb,mul_le_mul_of_nonneg_right hder hα.le,hα]

end ZhangLS.Spec
