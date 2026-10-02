import ZhangLS.Spec.Lemma55ActualZeroDetection

/-!
# Normalization cost for a zero in the complete original region

At a candidate zero's own height, the original Re s>1−2/log D condition
places it in the actual Jensen disk. Every maximal inverse square from
a subset containing that zero has radius at least (1+2/log D)^−2.
Normalizing its first J powers therefore costs at most exp(4J/log D).
-/

namespace ZhangLS.Spec

open Complex Metric Set Finset

lemma lemma55_jensen_center_at_zero_height (ρ : ℂ) :
    lemma55JensenCenter ρ.im - ρ = ((2 - ρ.re : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [lemma55JensenCenter]

theorem lemma55_original_zero_in_own_local_disk
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) {ρ : ℂ}
    (hregion : Lemma55InZeroRegion D ρ) (hzero : dirichletLFunction χ ρ = 0) :
    ρ ∈ lemma55LocalZeroFinset χ ρ.im := by
  have hr := lemma55_actual_zero_re_lt_one χ hD hzero
  have hLp : 0 < Real.log (D : ℝ) := by linarith only [hL]
  have hinv : 2 / Real.log (D : ℝ) ≤ (1 : ℝ) / 1000 := by
    apply (div_le_iff₀ hLp).mpr
    linarith only [hL]
  apply (lemma55_mem_actual_local_zero_finset χ hD ρ.im ρ).mpr
  refine ⟨?_, hzero⟩
  rw [mem_closedBall_iff_norm, norm_sub_rev, lemma55_jensen_center_at_zero_height,
    norm_real, Real.norm_eq_abs, abs_of_pos (by linarith only [hr] : 0 < 2 - ρ.re)]
  have hre := hregion.1
  linarith only [hre, hinv]

theorem lemma55_original_zero_inverse_square_lower_bound
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) {ρ : ℂ}
    (hregion : Lemma55InZeroRegion D ρ) (hzero : dirichletLFunction χ ρ = 0) :
    ((1 + 2 / Real.log (D : ℝ))⁻¹) ^ 2 ≤ ‖lemma55ZeroInverseSquare ρ.im ρ‖ := by
  have hr := lemma55_actual_zero_re_lt_one χ hD hzero
  have hLp : 0 < Real.log (D : ℝ) := by linarith only [hL]
  have hd : 0 < 2 - ρ.re := by linarith only [hr]
  have ha : 2 - ρ.re ≤ 1 + 2 / Real.log (D : ℝ) := by
    linarith only [hregion.1]
  have hi : (1 + 2 / Real.log (D : ℝ))⁻¹ ≤ (2 - ρ.re)⁻¹ :=
    (inv_le_inv₀ (by positivity : 0 < 1 + 2 / Real.log (D : ℝ)) hd).mpr ha
  unfold lemma55ZeroInverseSquare
  rw [norm_pow, norm_inv, lemma55_jensen_center_at_zero_height,
    norm_real, Real.norm_eq_abs, abs_of_pos hd]
  exact pow_le_pow_left₀ (by positivity) hi 2

theorem lemma55_original_candidate_subset_normalization
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) {ρ : ℂ}
    (hregion : Lemma55InZeroRegion D ρ) (hzero : dirichletLFunction χ ρ = 0)
    (S : Finset ℂ) (hS : S ⊆ lemma55LocalZeroFinset χ ρ.im) (hρ : ρ ∈ S) :
    ∃ ρ₀ ∈ S, 0 < ‖lemma55ZeroInverseSquare ρ.im ρ₀‖ ∧
      ‖lemma55ZeroInverseSquare ρ.im ρ₀‖ < 1 ∧
      ((1 + 2 / Real.log (D : ℝ))⁻¹) ^ 2 ≤ ‖lemma55ZeroInverseSquare ρ.im ρ₀‖ ∧
      ∀ σ ∈ S, ‖lemma55ZeroInverseSquare ρ.im σ‖ ≤ ‖lemma55ZeroInverseSquare ρ.im ρ₀‖ := by
  obtain ⟨ρ₀, hρ₀, hrp, hr1, hmax⟩ :=
    lemma55_actual_subset_max_inverse_square χ hD ρ.im S hS ⟨ρ, hρ⟩
  exact ⟨ρ₀, hρ₀, hrp, hr1,
    (lemma55_original_zero_inverse_square_lower_bound χ hD hL hregion hzero).trans
      (hmax ρ hρ), hmax⟩

lemma lemma55_normalization_power_exp_bound {L r : ℝ}
    (hL : 0 < L) (hr : 0 < r) (hlower : ((1 + 2 / L)⁻¹) ^ 2 ≤ r) (k : ℕ) :
    r⁻¹ ^ k ≤ Real.exp (4 * (k : ℝ) / L) := by
  have ha : 0 < 1 + 2 / L := by positivity
  have hi : r⁻¹ ≤ (1 + 2 / L) ^ 2 := by
    have h := (inv_le_inv₀ hr (by positivity : 0 < ((1 + 2 / L)⁻¹) ^ 2)).mpr hlower
    simpa only [← inv_pow, inv_inv] using h
  have he : 1 + 2 / L ≤ Real.exp (2 / L) := by
    simpa only [add_comm] using Real.add_one_le_exp (2 / L)
  calc
    _ ≤ ((1 + 2 / L) ^ 2) ^ k := pow_le_pow_left₀ (inv_nonneg.mpr hr.le) hi k
    _ = (1 + 2 / L) ^ (2 * k) := by rw [pow_mul]
    _ ≤ (Real.exp (2 / L)) ^ (2 * k) := pow_le_pow_left₀ ha.le he (2 * k)
    _ = Real.exp (4 * (k : ℝ) / L) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring

lemma lemma55_normalization_first_powers_exp_bound {L r : ℝ}
    (hL : 0 < L) (hr : 0 < r) (hlower : ((1 + 2 / L)⁻¹) ^ 2 ≤ r)
    (J j : ℕ) (hj : j ∈ range J) :
    r⁻¹ ^ (j + 1) ≤ Real.exp (4 * (J : ℝ) / L) := by
  have hle : (j + 1 : ℕ) ≤ J := by have h := mem_range.mp hj; omega
  have hcast : ((j + 1 : ℕ) : ℝ) ≤ (J : ℝ) := by exact_mod_cast hle
  apply (lemma55_normalization_power_exp_bound hL hr hlower (j + 1)).trans
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_right (by linarith only [hcast]) hL.le

end ZhangLS.Spec
