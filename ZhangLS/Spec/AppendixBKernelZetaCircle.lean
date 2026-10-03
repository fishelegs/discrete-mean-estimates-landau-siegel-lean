import ZhangLS.Spec.AppendixBKernelModelCircle
import ZhangLS.Spec.Section15AnalyticFactorBounds
import ZhangLS.Spec.Proposition71ZetaRegularizedReciprocal

/-! A genuine local analytic comparison of the zeta-ratio circle with the
rational source model. All estimates are unconditional and explicitly scaled. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace ZhangLS.Spec
open Complex Metric Set

noncomputable def appendixBZetaIntegrand (x : ℝ) (β γ s : ℂ) : ℂ :=
  riemannZeta (1+s)/riemannZeta (1+s-β)*(x : ℂ)^s/(s-γ)^2

noncomputable def appendixBZetaCircle (X x : ℝ) (β γ : ℂ) (R : ℝ) : ℂ :=
  ((2*Real.pi*I : ℂ)⁻¹*circleIntegral (appendixBZetaIntegrand x β γ) 0 R)/(Real.log X : ℂ)

lemma appendixB_zeta_ratio_regularized {s β : ℂ}
    (hs : s≠0) (hs1 : 1+s≠0) (hb : s≠β) (hsb1 : 1+s-β≠0) :
    riemannZeta (1+s)/riemannZeta (1+s-β) =
      (s-β)/s*(zetaPoleRemoved (1+s)/zetaPoleRemoved (1+s-β)) := by
  have h1 : 1+s≠1 := by intro h; apply hs; linear_combination h
  have h2 : 1+s-β≠1 := by intro h; apply hb; linear_combination h
  rw [zetaPoleRemoved_eq_mul_riemannZeta hs1 h1,
    zetaPoleRemoved_eq_mul_riemannZeta hsb1 h2]
  simp only [add_sub_cancel_left,show 1+s-β-1=s-β by ring]
  field_simp [hs,sub_ne_zero.mpr hb]

/-- Explicit O(alpha) error in the actual zeta quotient on |s|=5 alpha.
The denominator's nonvanishing follows from the proved local zeta estimate. -/
lemma appendixB_zeta_ratio_circle_error {α : ℝ} (hα : 0<α) (hsmall : α≤1/100)
    {β s : ℂ} (hβ : ‖β‖≤3*α) (hs : ‖s‖=5*α) :
    riemannZeta (1+s-β)≠0 ∧
      ‖riemannZeta (1+s)/riemannZeta (1+s-β)-(s-β)/s‖≤220*α := by
  have hsb : ‖s-β‖≤8*α := (norm_sub_le _ _).trans (by linarith)
  have he1 : ‖zetaPoleRemoved (1+s)-1‖≤25*α := by
    have h := section15_zeta_regular_error (z := 1+s) (by simp; linarith)
    simp only [add_sub_cancel_left,hs] at h
    linarith
  have he2 : ‖zetaPoleRemoved (1+s-β)-1‖≤40*α := by
    have he : 1+s-β-1=s-β := by ring
    have h := section15_zeta_regular_error (z := 1+s-β) (by rw [he]; linarith)
    rw [he] at h
    linarith
  have hlow : 1/2≤‖zetaPoleRemoved (1+s-β)‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (zetaPoleRemoved (1+s-β))
    rw [norm_one,norm_sub_rev] at h
    linarith
  have hR : zetaPoleRemoved (1+s-β)≠0 := norm_pos_iff.mp (by linarith)
  have hs0 : s≠0 := norm_pos_iff.mp (by rw [hs]; positivity)
  have hsb0 : s≠β := by intro h; rw [h] at hs; linarith
  have hs1 : 1+s≠0 := by
    intro h
    have he : s= -1 := by linear_combination h
    rw [he,norm_neg,norm_one] at hs
    linarith
  have hsb1 : 1+s-β≠0 := by
    intro h
    have he : s-β= -1 := by linear_combination h
    rw [he,norm_neg,norm_one] at hsb
    linarith
  have hζ : riemannZeta (1+s-β)≠0 := by
    have h2 : 1+s-β≠1 := by intro h; apply hsb0; linear_combination h
    rw [zetaPoleRemoved_eq_mul_riemannZeta hsb1 h2] at hR
    exact right_ne_zero_of_mul hR
  refine ⟨hζ,?_⟩
  have hdiff : ‖zetaPoleRemoved (1+s)-zetaPoleRemoved (1+s-β)‖≤65*α := by
    have h := norm_sub_le (zetaPoleRemoved (1+s)-1) (zetaPoleRemoved (1+s-β)-1)
    rw [sub_sub_sub_cancel_right] at h
    linarith
  have hq : ‖zetaPoleRemoved (1+s)/zetaPoleRemoved (1+s-β)-1‖≤130*α := by
    rw [div_sub_one hR,norm_div]
    apply (div_le_iff₀ (norm_pos_iff.mpr hR)).mpr
    nlinarith
  have hm : ‖(s-β)/s‖≤2 := by
    rw [norm_div,hs]
    apply (div_le_iff₀ (by positivity : 0<5*α)).mpr
    linarith
  have hm' : ‖(s-β)/s‖≤8/5 := by
    rw [norm_div,hs]
    apply (div_le_iff₀ (by positivity : 0<5*α)).mpr
    linarith
  rw [appendixB_zeta_ratio_regularized hs0 hs1 hsb0 hsb1,
    show (s-β)/s*(zetaPoleRemoved (1+s)/zetaPoleRemoved (1+s-β))-(s-β)/s =
      ((s-β)/s)*(zetaPoleRemoved (1+s)/zetaPoleRemoved (1+s-β)-1) by ring,norm_mul]
  calc
    _ ≤ (8/5)*(130*α) := mul_le_mul hm' hq (norm_nonneg _) (by norm_num)
    _ ≤ _ := by linarith

/-- The true zeta circle differs from the exact rational leading expression by
at most 275 exp(5H)/log X. The finite-D shifts remain unchanged. -/
theorem appendixB_actual_circle_leading_error {α X x H : ℝ}
    (hα : 0<α) (hsmall : α≤1/100) (hX : 1<X) (hx : 1≤x)
    (hscale : α*Real.log x≤H) {β γ : ℂ}
    (hβ : ‖β‖≤3*α) (hγ : ‖γ‖≤3*α) (hγ0 : γ≠0) :
    ‖appendixBZetaCircle X x β γ (5*α)-appendixBModelLeading X x β γ‖≤
      275*Real.exp (5*H)/Real.log X := by
  have hR : 0<5*α := by positivity
  have hxp : 0<x := lt_of_lt_of_le zero_lt_one hx
  have hlog : 0<Real.log X := Real.log_pos hX
  have hgR : ‖γ‖<5*α := by linarith
  let f := appendixBZetaIntegrand x β γ
  let g : ℂ → ℂ := fun s => (s-β)/s*(x : ℂ)^s/(s-γ)^2
  have hnorm (s : ℂ) (hs : s∈sphere 0 (5*α)) : ‖s‖=5*α := by
    simpa using mem_sphere_iff_norm.mp hs
  have hs0 (s : ℂ) (hs : s∈sphere 0 (5*α)) : s≠0 :=
    norm_pos_iff.mp (by rw [hnorm s hs]; positivity)
  have hsg (s : ℂ) (hs : s∈sphere 0 (5*α)) : s≠γ := by
    intro h; have he := hnorm s hs; rw [h] at he; linarith
  have hs1 (s : ℂ) (hs : s∈sphere 0 (5*α)) : 1+s≠1 := by
    intro h; apply hs0 s hs; linear_combination h
  have hsb1 (s : ℂ) (hs : s∈sphere 0 (5*α)) : 1+s-β≠1 := by
    intro h
    have he : s=β := by linear_combination h
    have hn := hnorm s hs
    rw [he] at hn
    linarith
  have hznum : ContinuousOn (fun s : ℂ => riemannZeta (1+s)) (sphere 0 (5*α)) := by
    intro s hs
    exact ((differentiableAt_riemannZeta (hs1 s hs)).continuousAt.comp (by fun_prop)).continuousWithinAt
  have hzden : ContinuousOn (fun s : ℂ => riemannZeta (1+s-β)) (sphere 0 (5*α)) := by
    intro s hs
    exact ((differentiableAt_riemannZeta (hsb1 s hs)).continuousAt.comp (f := fun z : ℂ => 1+z-β) (x := s)
      (show ContinuousAt (fun z : ℂ => 1+z-β) s by fun_prop)).continuousWithinAt
  have hp : Continuous (fun s : ℂ => (x : ℂ)^s) := by
    simp_rw [lemma84_positive_cpow_eq_exp hxp]
    fun_prop
  have hf : CircleIntegrable f 0 (5*α) := by
    apply ContinuousOn.circleIntegrable hR.le
    exact ((hznum.div hzden (fun s hs =>
      (appendixB_zeta_ratio_circle_error hα hsmall hβ (hnorm s hs)).1)).mul hp.continuousOn).div
        (by fun_prop) (fun s hs => pow_ne_zero _ (sub_ne_zero.mpr (hsg s hs)))
  have hg : CircleIntegrable g 0 (5*α) := by
    apply ContinuousOn.circleIntegrable hR.le
    exact ((((continuousOn_id.sub continuousOn_const).div continuousOn_id hs0).mul
      hp.continuousOn).div (by fun_prop) (fun s hs => pow_ne_zero _ (sub_ne_zero.mpr (hsg s hs))))
  have he : appendixBZetaCircle X x β γ (5*α)-appendixBModelLeading X x β γ =
      ((2*Real.pi*I : ℂ)⁻¹*circleIntegral (fun s =>
        (riemannZeta (1+s)/riemannZeta (1+s-β)-(s-β)/s)*
          exp (s*(Real.log x : ℂ))/(s-γ)^2) 0 (5*α))/(Real.log X : ℂ) := by
    rw [←appendixB_model_circle_eq_leading X hxp β γ hγ0 hgR]
    unfold appendixBZetaCircle
    rw [←sub_div,←mul_sub,←circleIntegral.integral_sub hf hg]
    congr 2
    apply circleIntegral.integral_congr hR.le
    intro s _
    dsimp [f,g,appendixBZetaIntegrand]
    rw [lemma84_positive_cpow_eq_exp hxp]
    ring
  have hb := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR.le
    (f := fun s => (riemannZeta (1+s)/riemannZeta (1+s-β)-(s-β)/s)*
      exp (s*(Real.log x : ℂ))/(s-γ)^2) (c := 0)
    (C := (220*α)*(Real.exp (5*H)/(4*α^2))) (by
      intro s hs
      dsimp only
      rw [mul_div_assoc,norm_mul]
      exact mul_le_mul
        (appendixB_zeta_ratio_circle_error hα hsmall hβ (hnorm s hs)).2
        (by simpa only [sub_eq_add_neg] using (lemma84_circle_kernel_bound s (-γ) hα
          (Real.log_nonneg hx) hscale (hnorm s hs) (by simpa using hγ)))
        (norm_nonneg _) (by positivity))
  have hb' : ‖(2*Real.pi*I : ℂ)⁻¹*circleIntegral (fun s =>
      (riemannZeta (1+s)/riemannZeta (1+s-β)-(s-β)/s)*
        exp (s*(Real.log x : ℂ))/(s-γ)^2) 0 (5*α)‖≤275*Real.exp (5*H) := by
    simpa only [smul_eq_mul,show (5*α)*((220*α)*(Real.exp (5*H)/(4*α^2)))=275*Real.exp (5*H) by
      field_simp; ring] using hb
  rw [he,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hlog]
  exact div_le_div_of_nonneg_right hb' hlog.le

end ZhangLS.Spec
