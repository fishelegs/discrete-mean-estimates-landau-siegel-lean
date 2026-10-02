import ZhangLS.Spec.Lemma53FiniteContours

/-! # Quantitative finite stationary-contour estimates for the actual kernel -/

namespace ZhangLS.Spec

open Complex MeasureTheory Set

set_option maxHeartbeats 1000000

noncomputable def lemma53StationaryHeight (D : ℕ) (x : ℝ) : ℝ :=
  Real.pi * (lemma51PaperT0 D - x) / lemma53PaperScale D ^ 2

noncomputable def lemma53ContourRadius (D : ℕ) (x r : ℝ) : ℝ :=
  r + |lemma53StationaryHeight D x|

noncomputable def lemma53ContourErrorBound (D : ℕ) (x r : ℝ) : ℝ :=
  lemma53ContourRadius D x r + 4 * Real.pi * x * lemma53ContourRadius D x r ^ 2

theorem lemma53_contour_error_nonneg (D : ℕ) {x r : ℝ} (hx : 0 ≤ x) (hr : 0 ≤ r) :
    0 ≤ lemma53ContourErrorBound D x r := by
  unfold lemma53ContourErrorBound lemma53ContourRadius
  positivity

theorem lemma53_contour_radius_le_error (D : ℕ) {x r : ℝ} (hx : 0 ≤ x) :
    lemma53ContourRadius D x r ≤ lemma53ContourErrorBound D x r := by
  unfold lemma53ContourErrorBound
  have hh : 0 ≤ 4 * Real.pi * x * lemma53ContourRadius D x r ^ 2 := by positivity
  linarith

theorem lemma53_perturbation_rectangle_bound (D : ℕ) {x r u v : ℝ}
    (hx : 0 ≤ x) (hr : 0 ≤ r) (hu : |u| ≤ r)
    (hv : v ∈ uIcc 0 (lemma53StationaryHeight D x))
    (hη : lemma53ContourErrorBound D x r ≤ 1) :
    ‖lemma53Perturbation x ((u : ℂ) + (v : ℂ) * I) - 1‖ ≤
      lemma53ContourErrorBound D x r := by
  let R := lemma53ContourRadius D x r
  have hR : 0 ≤ R := by dsimp [R, lemma53ContourRadius]; positivity
  have hvabs : |v| ≤ |lemma53StationaryHeight D x| := by
    simpa using abs_sub_left_of_mem_uIcc hv
  have hw : ‖(u : ℂ) + (v : ℂ) * I‖ ≤ R := by
    apply (norm_add_le _ _).trans
    simp only [norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs]
    dsimp [R, lemma53ContourRadius]
    linarith
  have hR1 : R ≤ 1 := (lemma53_contour_radius_le_error D hx).trans hη
  have hsq : ‖(u : ℂ) + (v : ℂ) * I‖ ^ 2 ≤ R ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hw 2
  have hmul := mul_le_mul_of_nonneg_left hsq
    (show 0 ≤ 2 * Real.pi * x by positivity)
  have hsmall : ‖(u : ℂ) + (v : ℂ) * I‖ / 2 +
      2 * Real.pi * x * ‖(u : ℂ) + (v : ℂ) * I‖ ^ 2 ≤ 1 := by
    dsimp [lemma53ContourErrorBound] at hη
    change R + 4 * Real.pi * x * R ^ 2 ≤ 1 at hη
    nlinarith
  apply (lemma53_perturbation_sub_one_bound hx (hw.trans hR1) hsmall).trans
  unfold lemma53ContourErrorBound
  change _ ≤ R + 4 * Real.pi * x * R ^ 2
  nlinarith [mul_le_mul_of_nonneg_left hsq (show 0 ≤ 4 * Real.pi * x by positivity)]

theorem lemma53_gaussian_between_stationary_bound {D : ℕ} (hD : 1 < D)
    (x u : ℝ) {v : ℝ} (hv : v ∈ uIcc 0 (lemma53StationaryHeight D x)) :
    ‖lemma53GaussianPhase D x ((u : ℂ) + (v : ℂ) * I)‖ ≤
      Real.exp (-(lemma53PaperScale D ^ 2 * u ^ 2)) := by
  let V := lemma53StationaryHeight D x
  have hcross : v ^ 2 ≤ V * v := by
    by_cases hV : 0 ≤ V
    · rw [uIcc_of_le hV] at hv
      have hh := mul_nonneg (show 0 ≤ v from hv.1) (sub_nonneg.mpr hv.2)
      nlinarith
    · rw [uIcc_of_ge (le_of_not_ge hV)] at hv
      have hh := mul_nonneg (show 0 ≤ -v by linarith [hv.2])
        (show 0 ≤ v - V by linarith [hv.1])
      nlinarith
  have he : lemma53PaperScale D ^ 2 * V = Real.pi * (lemma51PaperT0 D - x) := by
    dsimp [V, lemma53StationaryHeight]
    field_simp [(lemma53_scale_pos hD).ne']
  rw [lemma53_gaussian_phase_norm_shifted]
  apply Real.exp_le_exp.mpr
  have hm := mul_nonneg (sq_nonneg (lemma53PaperScale D))
    (show 0 ≤ 2 * V * v - v ^ 2 by nlinarith)
  have he' := congrArg (fun z : ℝ => z * v) he
  nlinarith

theorem lemma53_stationary_gaussian_norm {D : ℕ} (hD : 1 < D) (x u : ℝ) :
    ‖lemma53GaussianPhase D x ((u : ℂ) + (lemma53StationaryHeight D x : ℂ) * I)‖ =
      Real.exp (-((Real.pi * (lemma51PaperT0 D - x) / lemma53PaperScale D) ^ 2)) *
        Real.exp (-lemma53PaperScale D ^ 2 * u ^ 2) := by
  rw [lemma53StationaryHeight, lemma53_gaussian_phase_norm_at_stationary_line hD,
    ← Real.exp_add]
  congr 1
  ring

theorem lemma53_stationary_gaussian_integrable {D : ℕ} (hD : 1 < D) (x : ℝ) :
    Integrable (fun u : ℝ =>
      ‖lemma53GaussianPhase D x ((u : ℂ) + (lemma53StationaryHeight D x : ℂ) * I)‖) := by
  have hB := lemma53_scale_pos hD
  have hg := (integrable_exp_neg_mul_sq (sq_pos_of_pos hB)).const_mul
    (Real.exp (-((Real.pi * (lemma51PaperT0 D - x) / lemma53PaperScale D) ^ 2)))
  simpa only [lemma53_stationary_gaussian_norm hD] using hg

theorem lemma53_stationary_gaussian_integral {D : ℕ} (hD : 1 < D) (x : ℝ) :
    (∫ u : ℝ,
      ‖lemma53GaussianPhase D x ((u : ℂ) + (lemma53StationaryHeight D x : ℂ) * I)‖) =
        ‖lemma53PaperOmega D ((1 / 2 : ℂ) + (2 * Real.pi : ℂ) * I * (x : ℂ))‖ := by
  simp_rw [lemma53_stationary_gaussian_norm hD]
  rw [integral_const_mul, integral_gaussian, Real.sqrt_div Real.pi_pos.le,
    Real.sqrt_sq (lemma53_scale_pos hD).le, lemma53_omega_critical_gaussian,
    Complex.norm_of_nonneg (by have := lemma53_scale_pos hD; positivity)]
  rw [mul_comm]
  congr 1
  congr 1
  ring

theorem lemma53_error_vertical_bound {D : ℕ} (hD : 1 < D) {x r u : ℝ}
    (hx : 0 ≤ x) (hr : 0 ≤ r) (hu : |u| ≤ r)
    (hη : lemma53ContourErrorBound D x r ≤ 1) :
    ‖∫ v : ℝ in 0..lemma53StationaryHeight D x,
      lemma53ErrorKernel D x ((u : ℂ) + (v : ℂ) * I)‖ ≤
        lemma53ContourErrorBound D x r * Real.exp (-(lemma53PaperScale D ^ 2 * u ^ 2)) *
          |lemma53StationaryHeight D x| := by
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := lemma53StationaryHeight D x)
    (f := fun v : ℝ => lemma53ErrorKernel D x ((u : ℂ) + (v : ℂ) * I))
    (C := lemma53ContourErrorBound D x r * Real.exp (-(lemma53PaperScale D ^ 2 * u ^ 2)))
    (fun v hv => by
    dsimp only [lemma53ErrorKernel]
    rw [lemma53_kernel_error_factorization, norm_mul]
    have hpert := lemma53_perturbation_rectangle_bound D hx hr hu (uIoc_subset_uIcc hv) hη
    have hg := lemma53_gaussian_between_stationary_bound hD x u (uIoc_subset_uIcc hv)
    exact (mul_le_mul hg hpert (norm_nonneg _)
      (Real.exp_pos _).le).trans_eq (mul_comm _ _))
  simpa only [sub_zero] using hh

theorem lemma53_error_stationary_middle_bound {D : ℕ} (hD : 1 < D) {x r : ℝ}
    (hx : 0 ≤ x) (hr : 0 ≤ r) (hη : lemma53ContourErrorBound D x r ≤ 1) :
    ‖∫ u : ℝ in -r..r,
      lemma53ErrorKernel D x ((u : ℂ) + (lemma53StationaryHeight D x : ℂ) * I)‖ ≤
        lemma53ContourErrorBound D x r *
          ‖lemma53PaperOmega D ((1 / 2 : ℂ) + (2 * Real.pi : ℂ) * I * (x : ℂ))‖ := by
  rw [intervalIntegral.integral_of_le (by linarith : -r ≤ r)]
  have hg := lemma53_stationary_gaussian_integrable hD x
  have hη0 := lemma53_contour_error_nonneg D hx hr
  have hpoint (u : ℝ) (hu : u ∈ Ioc (-r) r) :
      ‖lemma53ErrorKernel D x ((u : ℂ) + (lemma53StationaryHeight D x : ℂ) * I)‖ ≤
        lemma53ContourErrorBound D x r *
          ‖lemma53GaussianPhase D x ((u : ℂ) + (lemma53StationaryHeight D x : ℂ) * I)‖ := by
    unfold lemma53ErrorKernel
    rw [lemma53_kernel_error_factorization, norm_mul]
    have hpert := lemma53_perturbation_rectangle_bound D hx hr
      (abs_le.mpr ⟨hu.1.le, hu.2⟩) (right_mem_uIcc) hη
    exact (mul_le_mul_of_nonneg_left hpert (norm_nonneg _)).trans_eq (mul_comm _ _)
  apply (norm_integral_le_of_norm_le (hg.const_mul (lemma53ContourErrorBound D x r)).integrableOn
    (ae_restrict_of_forall_mem measurableSet_Ioc hpoint)).trans
  rw [integral_const_mul, ← lemma53_stationary_gaussian_integral hD x]
  exact mul_le_mul_of_nonneg_left
    (setIntegral_le_integral hg (Filter.Eventually.of_forall (fun _ => norm_nonneg _))) hη0

end ZhangLS.Spec
