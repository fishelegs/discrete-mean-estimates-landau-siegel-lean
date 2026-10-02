import ZhangLS.Spec.Lemma171CorrectionBounds

/-! # Uniform error in the actual Lemma 17.1 residue

Cauchy bounds at radius 1/(4(log D)²) control the actual regular prefactor.
All constants are absolute and every small factor comes from the original (A).
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex Metric Set
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def lemma171ResidueRadius (D : ℕ) : ℝ :=
  1/(4*lemma23PaperL D^2)

noncomputable def lemma171PrefactorBound : ℝ :=
  64*Real.exp 1*lemma32RegularProductBound (3/4)

lemma lemma171_prefactor_bound_pos : 0 < lemma171PrefactorBound := by
  unfold lemma171PrefactorBound
  exact mul_pos (mul_pos (by norm_num) (Real.exp_pos _)) (lemma32_regular_product_bound_pos _)

lemma lemma171_residue_radius_properties {D : ℕ} (hL : 2 ≤ lemma23PaperL D) :
    0 < lemma171ResidueRadius D ∧ lemma171ResidueRadius D ≤ 1/4 ∧
      lemma171ResidueRadius D*lemma23PaperL D ≤ 1 ∧
      lemma23PaperL D^(11/10 : ℝ)*lemma171ResidueRadius D ≤ 1/4 := by
  let L := lemma23PaperL D
  have hL0 : 0 < L := by dsimp [L]; linarith
  have hL1 : 1 ≤ L := by dsimp [L]; linarith
  have hL2 : 1 ≤ L^2 := one_le_pow₀ hL1
  have hqa : L^(11/10 : ℝ) ≤ L^2 := by
    convert Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (11/10 : ℝ) ≤ 2) using 1; norm_num
  have hd : 0 < 4*L^2 := by positivity
  refine ⟨by unfold lemma171ResidueRadius; positivity,?_,?_,?_⟩
  · change 1/(4*L^2) ≤ 1/4
    apply (div_le_iff₀ hd).mpr
    nlinarith
  · change (1/(4*L^2))*L ≤ 1
    rw [one_div,mul_comm,← div_eq_mul_inv]
    apply (div_le_iff₀ hd).mpr
    nlinarith
  · change L^(11/10 : ℝ)*(1/(4*L^2)) ≤ 1/4
    rw [mul_one_div]
    apply (div_le_iff₀ hd).mpr
    nlinarith

lemma lemma171_gaussian_factor_local_bound {D : ℕ} (hL : 2 ≤ lemma23PaperL D)
    (w : ℂ) (hw : ‖w‖ ≤ lemma171ResidueRadius D) :
    ‖lemma171GaussianMellinFactor D w‖ ≤ Real.exp 1 := by
  let L := lemma23PaperL D
  have hL0 : 0 < L := by dsimp [L]; linarith
  have hL1 : 1 ≤ L := by dsimp [L]; linarith
  have hR := lemma171_residue_radius_properties hL
  have hqa : 0 ≤ L^(11/10 : ℝ) := Real.rpow_nonneg hL0.le _
  have hlin : ‖((L^(11/10 : ℝ) : ℝ) : ℂ)*w‖ ≤ 1/4 := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hqa]
    exact (mul_le_mul_of_nonneg_left hw hqa).trans hR.2.2.2
  have hden : ‖(4 : ℂ)*(L : ℂ)^30‖ = 4*L^30 := by
    simp [norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL0]
  have hquad : ‖w^2/((4 : ℂ)*(L : ℂ)^30)‖ ≤ 1/4 := by
    rw [norm_div,norm_pow,hden]
    apply (div_le_iff₀ (by positivity : 0 < 4*L^30)).mpr
    have hw1 : ‖w‖ ≤ 1 := hw.trans (hR.2.1.trans (by norm_num))
    have hs : ‖w‖^2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hw1
    have h30 : 1 ≤ L^30 := one_le_pow₀ hL1
    nlinarith
  unfold lemma171GaussianMellinFactor
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  change ((((L^(11/10 : ℝ) : ℝ) : ℂ)*w) + w^2/((4 : ℂ)*(L : ℂ)^30)).re ≤ 1
  have hr := Complex.re_le_norm (((L^(11/10 : ℝ) : ℝ) : ℂ)*w + w^2/((4 : ℂ)*(L : ℂ)^30))
  have hn := norm_add_le ((((L^(11/10 : ℝ) : ℝ) : ℂ)*w)) (w^2/((4 : ℂ)*(L : ℂ)^30))
  linarith

lemma lemma171_prefactor_local_bound {D : ℕ} (hL : 2 ≤ lemma23PaperL D)
    (w : ℂ) (hw : ‖w‖ ≤ lemma171ResidueRadius D) :
    ‖lemma171ResiduePrefactor D w‖ ≤ lemma171PrefactorBound := by
  have hR := lemma171_residue_radius_properties hL
  have hw4 := hw.trans hR.2.1
  have hre : 3/4 ≤ (1+w).re := by
    have hh := (abs_le.mp ((Complex.abs_re_le_norm w).trans hw4)).1
    simp only [Complex.add_re,Complex.one_re]
    linarith
  have hphase : |(1+w).im| *lemma23PaperL D ≤ 1 := by
    simp only [Complex.add_im,Complex.one_im,zero_add]
    exact (mul_le_mul_of_nonneg_right ((Complex.abs_im_le_norm w).trans hw)
      (by linarith : 0 ≤ lemma23PaperL D)).trans hR.2.2.1
  have hc := lemma171_correction_sector_bound D (3/4) (by norm_num) (1+w) hre hphase
  have hz := lemma32_zeta_pole_removed_local_bound (1+w) (by simpa using hw4)
  have hg := lemma171_gaussian_factor_local_bound hL w hw
  have hK := lemma32_regular_product_bound_pos (3/4)
  unfold lemma171ResiduePrefactor lemma171PrefactorBound
  rw [norm_mul,norm_mul,norm_pow]
  calc
    _ ≤ lemma32RegularProductBound (3/4)*8^2*Real.exp 1 := by
      gcongr
    _ = _ := by ring

lemma lemma171_prefactor_differentiableAt (D : ℕ) (w : ℂ) (hw : -1/2 < w.re) :
    DifferentiableAt ℂ (lemma171ResiduePrefactor D) w := by
  have hre : 1/2 < (1+w).re := by simp only [Complex.add_re,Complex.one_re]; linarith
  have had : DifferentiableAt ℂ (fun w : ℂ => 1+w) w := by fun_prop
  have hc := ((lemma171_correction_analyticOnNhd D) (1+w) hre).differentiableAt.comp w had
  have hz := (lemma32_zeta_pole_removed_differentiableAt (by linarith : 0 < (1+w).re)).comp w had
  exact (hc.mul (hz.pow 2)).mul (lemma171_gaussian_factor_differentiable D w)

lemma lemma171_prefactor_diffContOnCl {D : ℕ} (hL : 2 ≤ lemma23PaperL D) :
    DiffContOnCl ℂ (lemma171ResiduePrefactor D) (ball 0 (lemma171ResidueRadius D)) := by
  have hd : DifferentiableOn ℂ (lemma171ResiduePrefactor D) (closedBall 0 (lemma171ResidueRadius D)) := by
    intro w hw
    have hn : ‖w‖ ≤ lemma171ResidueRadius D := by simpa [mem_closedBall,dist_eq_norm] using hw
    have hb := (abs_le.mp ((Complex.abs_re_le_norm w).trans
      (hn.trans (lemma171_residue_radius_properties hL).2.1))).1
    exact (lemma171_prefactor_differentiableAt D w (by linarith)).differentiableWithinAt
  exact hd.diffContOnCl_ball subset_rfl

lemma lemma171_prefactor_first_derivative_bound {D : ℕ} (hL : 2 ≤ lemma23PaperL D) :
    ‖deriv (lemma171ResiduePrefactor D) 0‖ ≤ 4*lemma171PrefactorBound*lemma23PaperL D^2 := by
  have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (lemma171_residue_radius_properties hL).1 (lemma171_prefactor_diffContOnCl hL)
    (fun w hw => lemma171_prefactor_local_bound hL w (by
      exact le_of_eq (by simpa [mem_sphere,dist_eq_norm] using hw)))
  calc
    _ ≤ lemma171PrefactorBound/lemma171ResidueRadius D := hc
    _ = _ := by unfold lemma171ResidueRadius; field_simp

lemma lemma171_prefactor_second_derivative_bound {D : ℕ} (hL : 2 ≤ lemma23PaperL D) :
    ‖iteratedDeriv 2 (lemma171ResiduePrefactor D) 0‖ ≤ 32*lemma171PrefactorBound*lemma23PaperL D^4 := by
  have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    2 (lemma171_residue_radius_properties hL).1 (lemma171_prefactor_diffContOnCl hL)
    (fun w hw => lemma171_prefactor_local_bound hL w (by
      exact le_of_eq (by simpa [mem_sphere,dist_eq_norm] using hw)))
  calc
    _ ≤ 2*lemma171PrefactorBound/lemma171ResidueRadius D^2 := by
      simpa [Nat.factorial] using hc
    _ = _ := by unfold lemma171ResidueRadius; field_simp; ring


noncomputable def lemma171ResidueErrorConstant : ℝ :=
  128*Real.exp 1*lemma32RegularProductBound (3/4) +
    128*Real.exp 1*lemma171PrefactorBound + 16*lemma171PrefactorBound

lemma lemma171_residue_error_constant_pos : 0 < lemma171ResidueErrorConstant := by
  have hK := lemma32_regular_product_bound_pos (3/4)
  have hB := lemma171_prefactor_bound_pos
  unfold lemma171ResidueErrorConstant
  positivity

/-- The actual residue is a+O((log D)^(-2018)), with one absolute explicit constant. -/
lemma lemma171_actual_residue_error_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 2 ≤ lemma23PaperL D) (hA : NormalizedAssumptionA χ) :
    ‖lemma171ActualResidue χ - (lemma171MainTerm χ : ℂ)‖ ≤
      lemma171ResidueErrorConstant*lemma23PaperL D^(-2018 : ℤ) := by
  let L := lemma23PaperL D
  let K := lemma32RegularProductBound (3/4)
  let B := lemma171PrefactorBound
  have hL0 : 0 < L := by dsimp [L]; linarith
  have hL1 : 1 ≤ L := by dsimp [L]; linarith
  have hK : 0 < K := lemma32_regular_product_bound_pos _
  have hB : 0 < B := lemma171_prefactor_bound_pos
  have hv := lemma32_actual_value_at_one_small χ hD hA
  have hv1 : ‖LAtOne χ‖ ≤ 1 := hv.trans (zpow_le_one_of_nonpos₀ hL1 (by norm_num))
  have hC : ‖lemma171AnalyticCorrection D 1‖ ≤ K :=
    lemma171_correction_sector_bound D (3/4) (by norm_num) 1 (by norm_num) (by simp)
  have hd1 : ‖LDerivAtOne χ‖ ≤ 16*Real.exp 1*L^2 := by
    exact lemma32_actual_first_derivative_bound χ hD hL (by simp; positivity)
  have hd2 : ‖iteratedDeriv 2 (dirichletLFunction χ) 1‖ ≤ 128*Real.exp 1*L^3 := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero,L,lemma23PaperL] using
      lemma55_actual_second_derivative_bound χ hD hL (s := 1) (by simp; positivity)
  have h34 : L^3 ≤ L^4 := pow_le_pow_right₀ hL1 (by norm_num)
  have hp1 := lemma171_prefactor_first_derivative_bound hL
  have hp2 := lemma171_prefactor_second_derivative_bound hL
  have ht1 : ‖lemma171AnalyticCorrection D 1*iteratedDeriv 2 (dirichletLFunction χ) 1‖ ≤
      (128*Real.exp 1*K)*L^4 := by
    rw [norm_mul]
    calc
      _ ≤ K*(128*Real.exp 1*L^3) := mul_le_mul hC hd2 (norm_nonneg _) hK.le
      _ ≤ K*(128*Real.exp 1*L^4) := by gcongr
      _ = _ := by ring
  have ht2 : ‖2*deriv (lemma171ResiduePrefactor D) 0*LDerivAtOne χ‖ ≤
      (128*Real.exp 1*B)*L^4 := by
    rw [norm_mul,norm_mul]
    norm_num only [norm_ofNat]
    calc
      _ ≤ 2*(4*B*L^2)*(16*Real.exp 1*L^2) := by gcongr
      _ = _ := by ring
  have ht3 : ‖iteratedDeriv 2 (lemma171ResiduePrefactor D) 0*LAtOne χ/2‖ ≤
      (16*B)*L^4 := by
    rw [norm_div,norm_mul]
    norm_num only [norm_ofNat]
    calc
      _ ≤ (32*B*L^4)*1/2 := by gcongr
      _ = _ := by ring
  have ht : ‖lemma171AnalyticCorrection D 1*iteratedDeriv 2 (dirichletLFunction χ) 1 +
      2*deriv (lemma171ResiduePrefactor D) 0*LDerivAtOne χ +
      iteratedDeriv 2 (lemma171ResiduePrefactor D) 0*LAtOne χ/2‖ ≤
        lemma171ResidueErrorConstant*L^4 := by
    calc
      _ ≤ ‖lemma171AnalyticCorrection D 1*iteratedDeriv 2 (dirichletLFunction χ) 1‖ +
          ‖2*deriv (lemma171ResiduePrefactor D) 0*LDerivAtOne χ‖ +
          ‖iteratedDeriv 2 (lemma171ResiduePrefactor D) 0*LAtOne χ/2‖ := norm_add₃_le
      _ ≤ (128*Real.exp 1*K)*L^4+(128*Real.exp 1*B)*L^4+(16*B)*L^4 :=
        add_le_add (add_le_add ht1 ht2) ht3
      _ = _ := by unfold lemma171ResidueErrorConstant; dsimp [K,B]; ring
  rw [lemma171_actual_residue_decomposition χ hD]
  rw [show (lemma171MainTerm χ : ℂ)+LAtOne χ*(lemma171AnalyticCorrection D 1*
      iteratedDeriv 2 (dirichletLFunction χ) 1 +
      2*deriv (lemma171ResiduePrefactor D) 0*LDerivAtOne χ +
      iteratedDeriv 2 (lemma171ResiduePrefactor D) 0*LAtOne χ/2) - (lemma171MainTerm χ : ℂ) =
      LAtOne χ*(lemma171AnalyticCorrection D 1*iteratedDeriv 2 (dirichletLFunction χ) 1 +
      2*deriv (lemma171ResiduePrefactor D) 0*LDerivAtOne χ +
      iteratedDeriv 2 (lemma171ResiduePrefactor D) 0*LAtOne χ/2) by ring]
  rw [norm_mul]
  calc
    _ ≤ L^(-2022 : ℤ)*(lemma171ResidueErrorConstant*L^4) :=
      mul_le_mul hv ht (norm_nonneg _) (zpow_pos hL0 _).le
    _ = lemma171ResidueErrorConstant*(L^(-2022 : ℤ)*L^4) := by ring
    _ = _ := by
      congr 1
      simpa only [Int.reduceAdd,zpow_ofNat] using
        (zpow_add₀ hL0.ne' (-2022 : ℤ) 4).symm

end ZhangLS.Spec
