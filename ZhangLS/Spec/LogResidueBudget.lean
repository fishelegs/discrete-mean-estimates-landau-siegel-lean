import ZhangLS.Spec.FourthResidue

/-! Uniform bound for every L(1,χ)-containing term in the actual fourth residue. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex Metric Set

lemma lemma171_L_third_derivative_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 2 ≤ lemma23PaperL D) :
    ‖iteratedDeriv 3 (dirichletLFunction χ) 1‖ ≤
      1536 * Real.exp 1 * lemma23PaperL D ^ 4 := by
  let L := lemma23PaperL D
  let R := 1 / (4 * L)
  have hL0 : 0 < L := by dsimp [L]; linarith
  have hR : 0 < R := by dsimp [R]; positivity
  have hRle : R ≤ 1 / L := by
    dsimp [R]
    apply one_div_le_one_div_of_le hL0
    linarith
  have hLi : 1 / L ≤ (1 : ℝ) / 2 := one_div_le_one_div_of_le (by norm_num) hL
  have hb (z : ℂ) (hz : z ∈ sphere (1 : ℂ) R) :
      ‖dirichletLFunction χ z‖ ≤ 4 * Real.exp 1 * L := by
    have hn : ‖z - 1‖ ≤ 1 / L := (mem_sphere_iff_norm.mp hz).le.trans hRle
    have hre := (Complex.abs_re_le_norm (z - 1)).trans hn
    have hnorm : ‖z‖ ≤ 2 := by
      have hh : ‖z‖ ≤ ‖z - 1‖ + 1 := by simpa using norm_add_le (z - 1) (1 : ℂ)
      linarith
    apply lemma55_actual_L_near_one_bound χ hD hL _ hnorm
    have hh := (abs_le.mp hre).1
    simp only [Complex.sub_re, Complex.one_re] at hh
    change 1 - 1 / L ≤ z.re
    linarith
  have hh := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    3 hR (differentiable_dirichletLFunction_of_one_lt_modulus χ hD).diffContOnCl hb
  calc
    _ ≤ 6 * (4 * Real.exp 1 * L) / R ^ 3 := by simpa [Nat.factorial] using hh
    _ = _ := by dsimp [R, L]; field_simp; ring

noncomputable def lemma171LogResidueMain {D : ℕ} (χ : RealPrimitiveCharacter D) : ℂ :=
  lemma171AnalyticCorrection D 1 * LDerivAtOne χ *
      iteratedDeriv 2 (dirichletLFunction χ) 1 +
    deriv (lemma171ResiduePrefactor D) 0 * (LDerivAtOne χ) ^ 2

noncomputable def lemma171LogResidueErrorConstant : ℝ :=
  512 * Real.exp 1 * lemma32RegularProductBound (3/4) +
    1024 * Real.exp 1 * lemma171PrefactorBound + 64 * lemma171PrefactorBound

lemma lemma171_log_residue_error_constant_pos : 0 < lemma171LogResidueErrorConstant := by
  have hK := lemma32_regular_product_bound_pos (3/4)
  have hB := lemma171_prefactor_bound_pos
  unfold lemma171LogResidueErrorConstant
  positivity

lemma lemma171_actual_log_residue_error_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 2 ≤ lemma23PaperL D) (hA : NormalizedAssumptionA χ) :
    ‖lemma171ActualLogResidue χ - lemma171LogResidueMain χ‖ ≤
      lemma171LogResidueErrorConstant * lemma23PaperL D ^ (-2016 : ℤ) := by
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
  have hd1 : ‖LDerivAtOne χ‖ ≤ 16 * Real.exp 1 * L ^ 2 :=
    lemma32_actual_first_derivative_bound χ hD hL (by simp; positivity)
  have hd2 : ‖iteratedDeriv 2 (dirichletLFunction χ) 1‖ ≤ 128 * Real.exp 1 * L ^ 3 := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero, L, lemma23PaperL] using
      lemma55_actual_second_derivative_bound χ hD hL (s := 1) (by simp; positivity)
  have hd3 := lemma171_L_third_derivative_bound χ hD hL
  have hp1 := lemma171_prefactor_first_derivative_bound hL
  have hp2 := lemma171_prefactor_second_derivative_bound hL
  have hp3 := lemma171_prefactor_third_derivative_bound hL
  have h46 : L ^ 4 ≤ L ^ 6 := pow_le_pow_right₀ hL1 (by norm_num)
  have h56 : L ^ 5 ≤ L ^ 6 := pow_le_pow_right₀ hL1 (by norm_num)
  have ht1 : ‖lemma171AnalyticCorrection D 1 * iteratedDeriv 3 (dirichletLFunction χ) 1 / 3‖ ≤
      (512 * Real.exp 1 * K) * L ^ 6 := by
    rw [norm_div, norm_mul]
    norm_num only [norm_ofNat]
    calc
      _ ≤ K * (1536 * Real.exp 1 * L ^ 4) / 3 := by gcongr
      _ = (512 * Real.exp 1 * K) * L ^ 4 := by ring
      _ ≤ _ := by gcongr
  have ht2 : ‖deriv (lemma171ResiduePrefactor D) 0 *
      iteratedDeriv 2 (dirichletLFunction χ) 1‖ ≤ (512 * Real.exp 1 * B) * L ^ 6 := by
    rw [norm_mul]
    calc
      _ ≤ (4 * B * L ^ 2) * (128 * Real.exp 1 * L ^ 3) := by gcongr
      _ = (512 * Real.exp 1 * B) * L ^ 5 := by ring
      _ ≤ _ := by gcongr
  have ht3 : ‖iteratedDeriv 2 (lemma171ResiduePrefactor D) 0 * LDerivAtOne χ‖ ≤
      (512 * Real.exp 1 * B) * L ^ 6 := by
    rw [norm_mul]
    calc
      _ ≤ (32 * B * L ^ 4) * (16 * Real.exp 1 * L ^ 2) := by gcongr
      _ = _ := by ring
  have ht4 : ‖iteratedDeriv 3 (lemma171ResiduePrefactor D) 0 * LAtOne χ / 6‖ ≤
      (64 * B) * L ^ 6 := by
    rw [norm_div, norm_mul]
    norm_num only [norm_ofNat]
    calc
      _ ≤ (384 * B * L ^ 6) * 1 / 6 := by gcongr
      _ = _ := by ring
  have ht : ‖lemma171AnalyticCorrection D 1 * iteratedDeriv 3 (dirichletLFunction χ) 1 / 3 +
      deriv (lemma171ResiduePrefactor D) 0 * iteratedDeriv 2 (dirichletLFunction χ) 1 +
      iteratedDeriv 2 (lemma171ResiduePrefactor D) 0 * LDerivAtOne χ +
      iteratedDeriv 3 (lemma171ResiduePrefactor D) 0 * LAtOne χ / 6‖ ≤
      lemma171LogResidueErrorConstant * L ^ 6 := by
    calc
      _ ≤ (‖lemma171AnalyticCorrection D 1 * iteratedDeriv 3 (dirichletLFunction χ) 1 / 3‖ +
        ‖deriv (lemma171ResiduePrefactor D) 0 * iteratedDeriv 2 (dirichletLFunction χ) 1‖ +
        ‖iteratedDeriv 2 (lemma171ResiduePrefactor D) 0 * LDerivAtOne χ‖) +
        ‖iteratedDeriv 3 (lemma171ResiduePrefactor D) 0 * LAtOne χ / 6‖ :=
          (norm_add_le _ _).trans (add_le_add norm_add₃_le le_rfl)
      _ ≤ (512 * Real.exp 1 * K) * L ^ 6 + (512 * Real.exp 1 * B) * L ^ 6 +
          (512 * Real.exp 1 * B) * L ^ 6 + (64 * B) * L ^ 6 := by gcongr
      _ = _ := by unfold lemma171LogResidueErrorConstant; dsimp [K, B]; ring
  rw [lemma171_actual_log_residue_decomposition χ hD]
  unfold lemma171LogResidueMain
  rw [add_sub_cancel_left, norm_mul]
  calc
    _ ≤ L ^ (-2022 : ℤ) * (lemma171LogResidueErrorConstant * L ^ 6) :=
      mul_le_mul hv ht (norm_nonneg _) (zpow_pos hL0 _).le
    _ = lemma171LogResidueErrorConstant * (L ^ (-2022 : ℤ) * L ^ 6) := by ring
    _ = _ := by
      congr 1
      simpa only [Int.reduceAdd, zpow_ofNat] using
        (zpow_add₀ hL0.ne' (-2022 : ℤ) 6).symm

end ZhangLS.Spec
