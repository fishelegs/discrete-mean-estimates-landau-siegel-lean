import ZhangLS.Spec.Lemma162TwoPoleCircle

/-! Cancellation estimates obtained from genuine circle integrals. Bounds
depend on an ordinary sup bound for H, never on the target Taylor remainder. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Metric Set
set_option maxHeartbeats 1000000

theorem lemma162_two_pole_circle_bound (H : ℂ → ℂ) {γ : ℂ} {R M : ℝ}
    (hγR : ‖γ‖<R) (hM : ∀ w∈sphere (0 : ℂ) R, ‖H w‖≤M) :
    ‖(2*Real.pi*I : ℂ)⁻¹*circleIntegral (fun w => H w/(w^3*(w-γ))) 0 R‖≤
      M/(R^2*(R-‖γ‖)) := by
  have hR : 0<R := (norm_nonneg _).trans_lt hγR
  have hgap : 0<R-‖γ‖ := sub_pos.mpr hγR
  have hb := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR.le
    (f := fun w => H w/(w^3*(w-γ))) (C := M/(R^3*(R-‖γ‖))) (c := 0) (by
      intro w hw
      have hwR : ‖w‖=R := by simpa using mem_sphere_iff_norm.mp hw
      have hg : R-‖γ‖≤‖w-γ‖ := by simpa [hwR] using norm_sub_norm_le w γ
      rw [norm_div,norm_mul,norm_pow,hwR]
      exact div_le_div₀ ((norm_nonneg _).trans (hM w hw)) (hM w hw) (by positivity)
        (mul_le_mul_of_nonneg_left hg (by positivity)))
  simp only [smul_eq_mul] at hb
  calc
    _ ≤ R*(M/(R^3*(R-‖γ‖))) := hb
    _ = _ := by field_simp

/-- The bound remains finite as the genuine nonzero shift tends to zero. -/
theorem lemma162_third_divided_difference_bound (H : ℂ → ℂ) {γ : ℂ} {R M : ℝ}
    (hγ : γ≠0) (hγR : ‖γ‖<R) (hH : DifferentiableOn ℂ H (closedBall 0 R))
    (hM : ∀ w∈sphere (0 : ℂ) R, ‖H w‖≤M) :
    ‖lemma162ThirdDividedDifference H γ‖≤M/(R^2*(R-‖γ‖)) := by
  rw [← lemma162_two_pole_circle H hγ hγR hH]
  exact lemma162_two_pole_circle_bound H hγR hM

/-- Exact fourth-order Taylor remainder estimate for the third divided
difference. Every derivative remains that of the complete numerator H. -/
theorem lemma162_third_divided_difference_cubic_error (H : ℂ → ℂ)
    {γ : ℂ} {R M : ℝ} (hγ : γ≠0) (hγR : ‖γ‖<R)
    (hH : DifferentiableOn ℂ H (closedBall 0 R))
    (hM : ∀ w∈sphere (0 : ℂ) R, ‖H w‖≤M) :
    ‖lemma162ThirdDividedDifference H γ-iteratedDeriv 3 H 0/6‖≤
      M*‖γ‖/(R^3*(R-‖γ‖)) := by
  have hR : 0<R := (norm_nonneg _).trans_lt hγR
  have hgap : 0<R-‖γ‖ := sub_pos.mpr hγR
  have h0 : (0 : ℂ)∉sphere 0 R := by simpa using ne_of_lt hR
  have hγs : γ∉sphere 0 R := by simpa [mem_sphere] using ne_of_lt hγR
  have hcont := hH.continuousOn.mono sphere_subset_closedBall
  have hfour := lemma162_cauchy_pole_integrable H hR hcont h0 4
  simp only [sub_zero] at hfour
  have htwo : CircleIntegrable (fun w => H w/(w^3*(w-γ))) 0 R := by
    apply ContinuousOn.circleIntegrable hR.le
    apply hcont.div (by fun_prop)
    intro w hw
    apply mul_ne_zero
    · exact pow_ne_zero _ (by intro h; subst w; exact h0 hw)
    · exact sub_ne_zero.mpr (by intro h; subst w; exact hγs hw)
  have hc := lemma162_cauchy_center H hR hH 3
  norm_num only [sub_zero,Nat.reduceAdd,Nat.factorial, Nat.cast_ofNat] at hc
  rw [← lemma162_two_pole_circle H hγ hγR hH,← hc,← mul_sub,
    ← circleIntegral.integral_sub htwo hfour]
  have hi : circleIntegral (fun w => H w/(w^3*(w-γ))-H w/w^4) 0 R =
      circleIntegral (fun w => γ*H w/(w^4*(w-γ))) 0 R := by
    apply circleIntegral.integral_congr hR.le
    intro w hw
    have hw0 : w≠0 := by intro h; subst w; exact h0 hw
    have hwγ : w-γ≠0 := sub_ne_zero.mpr (by intro h; subst w; exact hγs hw)
    field_simp
    ring
  rw [hi]
  have hb := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR.le
    (f := fun w => γ*H w/(w^4*(w-γ))) (C := ‖γ‖*M/(R^4*(R-‖γ‖))) (c := 0) (by
      intro w hw
      have hwR : ‖w‖=R := by simpa using mem_sphere_iff_norm.mp hw
      have hg : R-‖γ‖≤‖w-γ‖ := by simpa [hwR] using norm_sub_norm_le w γ
      rw [norm_div,norm_mul,norm_mul,norm_pow,hwR]
      exact div_le_div₀ (mul_nonneg (norm_nonneg _) ((norm_nonneg _).trans (hM w hw)))
        (mul_le_mul_of_nonneg_left (hM w hw) (norm_nonneg _)) (by positivity)
        (mul_le_mul_of_nonneg_left hg (by positivity)))
  simp only [smul_eq_mul] at hb
  calc
    _ ≤ R*(‖γ‖*M/(R^4*(R-‖γ‖))) := hb
    _ = _ := by field_simp

end ZhangLS.Spec
