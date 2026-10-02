import ZhangLS.Spec.Lemma54EighthWeightedKernels

/-! # The three actual downward weighted contour bounds -/

namespace ZhangLS.Spec

open Complex MeasureTheory Set Filter

set_option maxHeartbeats 1000000

theorem lemma54_eighth_weighted_kernel_norm_left {n : ℕ} (hn : n ≤ 8) (D : ℕ)
    (x : ℝ) {u : ℝ} (hu : u ≤ 0) :
    ‖lemma54WeightedKernel D x n (u : ℂ)‖ ≤
      2 * lemma54EighthConstant * Real.exp (u / 2 - lemma53PaperScale D ^ 2 * u ^ 2) := by
  apply (lemma54_eighth_weighted_kernel_norm_real hn D x u).trans
  rw [← lemma54_eighth_weighted_majorant_factorization]
  have he : Real.exp (8 * u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hc : lemma54EighthConstant * (Real.exp (8 * u) + 1) ≤ 2 * lemma54EighthConstant := by
    nlinarith [lemma54_eighth_weighted_constant_pos]
  exact mul_le_mul_of_nonneg_right hc (Real.exp_nonneg _)

theorem lemma54_eighth_weighted_left_tail_bound {D : ℕ} {n : ℕ} (hn : n ≤ 8)
    {x : ℝ} (hx : 1 ≤ x) :
    ‖∫ u : ℝ in Iic (lemma53LargeEndpoint x), lemma54WeightedKernel D x n (u : ℂ)‖ ≤
      4 * lemma54EighthConstant * Real.exp (-((lemma53PaperScale D * Real.log x / 100) ^ 2)) := by
  have ha := lemma53_large_endpoint_nonpos hx
  let A := Real.exp (-(lemma53PaperScale D ^ 2 * lemma53LargeEndpoint x ^ 2))
  have hi := (integrableOn_exp_mul_Iic (by norm_num : (0 : ℝ) < 1 / 2)
    (lemma53LargeEndpoint x)).const_mul (2 * lemma54EighthConstant * A)
  have hnorm : ∀ u ∈ Iic (lemma53LargeEndpoint x),
      ‖lemma54WeightedKernel D x n (u : ℂ)‖ ≤
        (2 * lemma54EighthConstant * A) * Real.exp ((1 / 2 : ℝ) * u) := by
    intro u hu
    have hu0 : u ≤ 0 := hu.trans ha
    have hsq : lemma53LargeEndpoint x ^ 2 ≤ u ^ 2 := by
      nlinarith [show u ≤ lemma53LargeEndpoint x from hu]
    apply (lemma54_eighth_weighted_kernel_norm_left hn D x hu0).trans
    have he : Real.exp (u / 2 - lemma53PaperScale D ^ 2 * u ^ 2) ≤
        A * Real.exp ((1 / 2 : ℝ) * u) := by
      dsimp only [A]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hsq (sq_nonneg (lemma53PaperScale D))]
    have hm := mul_le_mul_of_nonneg_left he (show 0 ≤ 2 * lemma54EighthConstant by
      exact mul_nonneg (by norm_num) lemma54_eighth_weighted_constant_pos.le)
    convert hm using 1 <;> ring
  have h := norm_integral_le_of_norm_le hi
    (by filter_upwards [ae_restrict_mem measurableSet_Iic] with u hu; exact hnorm u hu)
  rw [integral_const_mul, integral_exp_mul_Iic (by norm_num : (0 : ℝ) < 1 / 2)] at h
  have he : Real.exp ((1 / 2 : ℝ) * lemma53LargeEndpoint x) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have hA : A = Real.exp (-((lemma53PaperScale D * Real.log x / 100) ^ 2)) := by
    dsimp only [A, lemma53LargeEndpoint]
    congr 1
    ring
  rw [hA] at h
  have hm := mul_le_mul_of_nonneg_left he
    (show 0 ≤ 4 * lemma54EighthConstant *
      Real.exp (-((lemma53PaperScale D * Real.log x / 100) ^ 2)) by
      exact mul_nonneg (mul_nonneg (by norm_num) lemma54_eighth_weighted_constant_pos.le)
        (Real.exp_nonneg _))
  nlinarith only [h, hm]

theorem lemma54_eighth_weighted_vertical_point_bound {D : ℕ} (hB : 1 ≤ lemma53PaperScale D)
    {n : ℕ} (hn : n ≤ 8) {x u v : ℝ} (hx : 0 < x)
    (hX : 4 * lemma51PaperT0 D ≤ lemma53LargePower x) (ht : 0 ≤ lemma51PaperT0 D)
    (hu : lemma53LargeEndpoint x ≤ u) (hv : v ∈ uIcc 0 (lemma53LargeHeight D)) :
    ‖lemma54WeightedKernel D x n ((u : ℂ) + (v : ℂ) * I)‖ ≤
      Real.exp 1 * lemma54EighthMajorant D u := by
  have hv0 := (lemma53_large_height_interval hB hv).2.1
  have hX0 : 0 ≤ lemma53LargePower x := Real.rpow_nonneg hx.le _
  have hk : ‖lemma53OscillatoryKernel D x ((u : ℂ) + (v : ℂ) * I)‖ ≤
      Real.exp 1 * Real.exp (u / 2 - lemma53PaperScale D ^ 2 * u ^ 2) := by
    apply (lemma53_large_shifted_norm_bound hB hx hX ht hu hv).trans
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hX0 hv0]
  have hf := lemma54_eighth_contour_factor_pow_bound hn u v
  unfold lemma54WeightedKernel
  rw [norm_mul, norm_pow]
  apply (mul_le_mul hf hk (norm_nonneg _)
    (mul_nonneg lemma54_eighth_weighted_constant_pos.le (by positivity))).trans
  apply le_of_eq
  rw [← lemma54_eighth_weighted_majorant_factorization]
  ring

theorem lemma54_eighth_weighted_vertical_bound {D : ℕ} (hB : 1 ≤ lemma53PaperScale D)
    {n : ℕ} (hn : n ≤ 8) {x u : ℝ} (hx : 0 < x)
    (hX : 4 * lemma51PaperT0 D ≤ lemma53LargePower x) (ht : 0 ≤ lemma51PaperT0 D)
    (hu : lemma53LargeEndpoint x ≤ u) :
    ‖∫ v : ℝ in 0..lemma53LargeHeight D,
      lemma54WeightedKernel D x n ((u : ℂ) + (v : ℂ) * I)‖ ≤
        (Real.exp 1 / lemma53PaperScale D) * lemma54EighthMajorant D u := by
  have hB0 : 0 < lemma53PaperScale D := by linarith
  have hh : lemma53LargeHeight D ≤ 0 := by
    unfold lemma53LargeHeight
    exact div_nonpos_of_nonpos_of_nonneg (by norm_num) hB0.le
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := lemma53LargeHeight D)
    (f := fun v : ℝ => lemma54WeightedKernel D x n ((u : ℂ) + (v : ℂ) * I))
    (C := Real.exp 1 * lemma54EighthMajorant D u) (by
      intro v hv
      exact lemma54_eighth_weighted_vertical_point_bound hB hn hx hX ht hu (uIoc_subset_uIcc hv))
  rw [sub_zero, abs_of_nonpos hh] at h
  dsimp only [lemma53LargeHeight] at h
  rw [neg_div, neg_neg] at h
  simpa only [lemma53LargeHeight, neg_div, one_div, div_eq_mul_inv, one_mul, neg_mul, mul_assoc,
    mul_comm, mul_left_comm] using h

theorem lemma54_eighth_weighted_left_vertical_bound {D : ℕ} (hB : 1 ≤ lemma53PaperScale D)
    {n : ℕ} (hn : n ≤ 8) {x : ℝ} (hx : 1 < x)
    (hX : 4 * lemma51PaperT0 D ≤ lemma53LargePower x) (ht : 0 ≤ lemma51PaperT0 D) :
    ‖∫ v : ℝ in 0..lemma53LargeHeight D,
      lemma54WeightedKernel D x n ((lemma53LargeEndpoint x : ℂ) + (v : ℂ) * I)‖ ≤
        2 * lemma54EighthConstant * Real.exp 1 *
          Real.exp (-((lemma53PaperScale D * Real.log x / 100) ^ 2)) := by
  have h := lemma54_eighth_weighted_vertical_bound hB hn (by linarith : 0 < x) hX ht le_rfl
  have ha := lemma53_large_endpoint_nonpos hx.le
  have hm : lemma54EighthMajorant D (lemma53LargeEndpoint x) ≤
      2 * lemma54EighthConstant * Real.exp (-((lemma53PaperScale D * Real.log x / 100) ^ 2)) := by
    rw [← lemma54_eighth_weighted_majorant_factorization]
    have he1 : Real.exp (8 * lemma53LargeEndpoint x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have he2 : Real.exp (lemma53LargeEndpoint x / 2 -
        lemma53PaperScale D ^ 2 * lemma53LargeEndpoint x ^ 2) ≤
          Real.exp (-((lemma53PaperScale D * Real.log x / 100) ^ 2)) := by
      apply Real.exp_le_exp.mpr
      have hs : lemma53PaperScale D ^ 2 * lemma53LargeEndpoint x ^ 2 =
          (lemma53PaperScale D * Real.log x / 100) ^ 2 := by unfold lemma53LargeEndpoint; ring
      rw [hs]
      linarith
    have hc : lemma54EighthConstant * (Real.exp (8 * lemma53LargeEndpoint x) + 1) ≤
        2 * lemma54EighthConstant := by nlinarith [lemma54_eighth_weighted_constant_pos]
    exact mul_le_mul hc he2 (Real.exp_nonneg _)
      (mul_nonneg (by norm_num) lemma54_eighth_weighted_constant_pos.le)
  have hc : Real.exp 1 / lemma53PaperScale D ≤ Real.exp 1 := div_le_self (Real.exp_nonneg _) hB
  apply h.trans
  have hp : 0 ≤ lemma54EighthMajorant D (lemma53LargeEndpoint x) := by
    unfold lemma54EighthMajorant
    exact mul_nonneg lemma54_eighth_weighted_constant_pos.le (by positivity)
  have hh := mul_le_mul hc hm hp (Real.exp_nonneg _)
  convert hh using 1 <;> ring

theorem lemma54_eighth_weighted_ray_integrable {D : ℕ} (hD : 1 < D) (hB : 1 ≤ lemma53PaperScale D)
    {n : ℕ} (hn : n ≤ 8) {x : ℝ} (hx : 0 < x)
    (hX : 4 * lemma51PaperT0 D ≤ lemma53LargePower x) (ht : 0 ≤ lemma51PaperT0 D) :
    IntegrableOn (fun u : ℝ => lemma54WeightedKernel D x n
      ((u : ℂ) + (lemma53LargeHeight D : ℂ) * I)) (Ioi (lemma53LargeEndpoint x)) := by
  have hg := ((lemma54_eighth_weighted_majorant_integrable hD).const_mul
    (Real.exp (1 - lemma53LargePower x / lemma53PaperScale D))).integrableOn
      (s := Ioi (lemma53LargeEndpoint x))
  apply hg.mono'
  · apply Continuous.aestronglyMeasurable
    unfold lemma54WeightedKernel lemma54ContourFactor lemma53OscillatoryKernel
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact lemma54_eighth_weighted_ray_norm_bound hB hn hx hX ht hu.le

theorem lemma54_eighth_weighted_right_ray_bound {D : ℕ} (hD : 1 < D) (hB : 1 ≤ lemma53PaperScale D)
    {n : ℕ} (hn : n ≤ 8) {x : ℝ} (hx : 0 < x)
    (hX : 4 * lemma51PaperT0 D ≤ lemma53LargePower x) (ht : 0 ≤ lemma51PaperT0 D) :
    ‖∫ u : ℝ in Ioi (lemma53LargeEndpoint x), lemma54WeightedKernel D x n
      ((u : ℂ) + (lemma53LargeHeight D : ℂ) * I)‖ ≤
        2 * lemma54EighthConstant * Real.sqrt Real.pi * Real.exp 20 *
          Real.exp (-lemma53LargePower x / lemma53PaperScale D) := by
  have hi := (lemma54_eighth_weighted_majorant_integrable hD).const_mul
    (Real.exp (1 - lemma53LargePower x / lemma53PaperScale D))
  have h := norm_integral_le_of_norm_le hi.integrableOn
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        exact lemma54_eighth_weighted_ray_norm_bound hB hn hx hX ht hu.le)
  apply h.trans
  apply (setIntegral_le_integral hi (by
    filter_upwards [] with u
    unfold lemma54EighthMajorant
    exact mul_nonneg (Real.exp_nonneg _)
      (mul_nonneg lemma54_eighth_weighted_constant_pos.le (by positivity)))).trans
  rw [integral_const_mul]
  have hm := (lemma54_eighth_weighted_majorant_integral_bound hD hB).trans
    (div_le_self (show 0 ≤ 2 * lemma54EighthConstant * Real.sqrt Real.pi * Real.exp 19 by
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) lemma54_eighth_weighted_constant_pos.le)
        (Real.sqrt_nonneg _)) (Real.exp_nonneg _)) hB)
  apply (mul_le_mul_of_nonneg_left hm (Real.exp_nonneg _)).trans
  apply le_of_eq
  have he : Real.exp (1 - lemma53LargePower x / lemma53PaperScale D) =
      Real.exp 1 * Real.exp (-lemma53LargePower x / lemma53PaperScale D) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he, show (20 : ℝ) = 1 + 19 by norm_num, Real.exp_add]
  ring

end ZhangLS.Spec
