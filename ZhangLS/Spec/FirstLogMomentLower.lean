import ZhangLS.Spec.FirstLogMoment
import ZhangLS.Spec.Lemma171EulerFactors
import ZhangLS.Spec.Lemma171ResidueBound
import ZhangLS.Spec.Lemma171MainLowerBound

/-! A strict actual arithmetic mass from the n=4 term. No jet-sign inference is used. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace ZhangLS.Spec
open Complex Finset Filter
open scoped Topology

lemma lemma171_coefficient_four_ge_one {D : ℕ} (χ : RealPrimitiveCharacter D) :
    1 ≤ lemma171Coefficient χ 4 := by
  have hp : Nat.Prime 2 := by decide
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr χ.quadratic (2 : ZMod D) with h | h | h
  · have hh : χ.evalNat 2 = 0 := by simpa only [RealPrimitiveCharacter.evalNat] using h
    have hv : lemma171Coefficient χ 4 = 1 := by
      simpa only [show (2 : ℕ)^2 = 4 by norm_num] using
        lemma171_coefficient_prime_power_of_zero χ hp hh 2
    exact le_of_eq hv.symm
  · have hh : χ.evalNat 2 = 1 := by simpa only [RealPrimitiveCharacter.evalNat] using h
    calc
      1 ≤ (2+1 : ℝ)^2 := by norm_num
      _ = lemma171Coefficient χ 4 := by
        simpa only [show (2 : ℕ)^2 = 4 by norm_num, Nat.cast_ofNat] using
          (lemma171_coefficient_prime_power_of_one χ hp hh 2).symm
  · have hh : χ.evalNat 2 = -1 := by simpa only [RealPrimitiveCharacter.evalNat] using h
    have hodd : ¬ Even (2+1 : ℕ) := by decide
    have hv : lemma171Coefficient χ 4 = 1 := by
      simpa only [show (2 : ℕ)^2 = 4 by norm_num, hodd, if_false] using
        lemma171_coefficient_prime_power_of_neg_one χ hp hh 2
    exact le_of_eq hv.symm

lemma lemma171_nu_four_real_ge_one {D : ℕ} (χ : RealPrimitiveCharacter D) :
    1 ≤ (lemma23NuArithmeticFunction χ 4).re := by
  have h := lemma171_coefficient_four_ge_one χ
  unfold lemma171Coefficient at h
  have hn := (one_le_sq_iff₀ (norm_nonneg (lemma23NuArithmeticFunction χ 4))).mp h
  exact hn.trans_eq (Complex.re_eq_norm.mpr (lemma31_actual_nu_nonneg χ 4)).symm

lemma lemma171_four_mem_short_range {D : ℕ} (hD : 2 ≤ D) :
    4 ∈ Finset.Ico 1 (D^4) := by
  have hpow := Nat.pow_le_pow_left hD 4
  norm_num at hpow
  exact Finset.mem_Ico.mpr ⟨by norm_num, by omega⟩

/-- The actual n=4 coefficient supplies a strictly positive, fixed mass. -/
theorem lemma171_first_log_moment_ge_log_four {D : ℕ}
    (χ : RealPrimitiveCharacter D) (hD : 2 ≤ D) :
    Real.log 4 / 4 ≤ lemma171FirstLogMoment χ := by
  have hh := Finset.single_le_sum
    (f := fun n : ℕ => lemma171Coefficient χ n * Real.log (n : ℝ) / (n : ℝ))
    (s := Finset.Ico 1 (D^4)) (a := 4)
    (fun n hn => by
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ico.mp hn).1
      exact div_nonneg (mul_nonneg (lemma171_coefficient_nonneg χ n)
        (Real.log_nonneg hn1)) (Nat.cast_nonneg n)) (lemma171_four_mem_short_range hD)
  have hlog : 0 ≤ Real.log 4 := (Real.log_pos (by norm_num : (1 : ℝ) < 4)).le
  calc
    _ ≤ lemma171Coefficient χ 4 * Real.log 4 / 4 := by
      have hc := mul_le_mul_of_nonneg_right (lemma171_coefficient_four_ge_one χ) hlog
      nlinarith only [hc]
    _ ≤ _ := by simpa only [Nat.cast_ofNat, lemma171FirstLogMoment] using hh

noncomputable def lemma171MainUpperConstant : ℝ :=
  256 * (Real.exp 1)^2 * lemma32RegularProductBound (3/4)

lemma lemma171_main_upper_constant_pos : 0 < lemma171MainUpperConstant := by
  have hK := lemma32_regular_product_bound_pos (3/4)
  unfold lemma171MainUpperConstant
  positivity

/-- An actual uniform a≤C L^4 estimate from the source Cauchy bound for L′(1). -/
lemma lemma171_actual_main_upper {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 2 ≤ lemma23PaperL D) :
    lemma171MainTerm χ ≤ lemma171MainUpperConstant * lemma23PaperL D^4 := by
  have hK := lemma32_regular_product_bound_pos (3/4)
  have hL0 : 0 < lemma23PaperL D := by linarith
  have hC : ‖lemma171AnalyticCorrection D 1‖ ≤ lemma32RegularProductBound (3/4) :=
    lemma171_correction_sector_bound D (3/4) (by norm_num) 1 (by norm_num) (by simp)
  have hd : ‖LDerivAtOne χ‖ ≤ 16 * Real.exp 1 * lemma23PaperL D^2 :=
    lemma32_actual_first_derivative_bound χ hD hL (by simp; positivity)
  calc
    _ ≤ |lemma171MainTerm χ| := le_abs_self _
    _ = ‖(lemma171MainTerm χ : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs]
    _ = ‖lemma171AnalyticCorrection D 1‖ * ‖LDerivAtOne χ‖^2 := by
      rw [lemma171_main_term_complex χ hD, norm_mul, norm_pow]
    _ ≤ lemma32RegularProductBound (3/4) * (16 * Real.exp 1 * lemma23PaperL D^2)^2 := by
      gcongr
    _ = _ := by unfold lemma171MainUpperConstant; ring

noncomputable def lemma171FirstLogRelativeLowerConstant : ℝ :=
  Real.log 4 / (4 * lemma171MainUpperConstant)

lemma lemma171_first_log_relative_lower_constant_pos :
    0 < lemma171FirstLogRelativeLowerConstant := by
  have hc := lemma171_main_upper_constant_pos
  unfold lemma171FirstLogRelativeLowerConstant
  exact div_pos (Real.log_pos (by norm_num)) (by positivity)

lemma lemma171_actual_first_log_relative_lower {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 2 ≤ D) (hL : 2 ≤ lemma23PaperL D) (ha : 0 < lemma171MainTerm χ) :
    lemma171FirstLogRelativeLowerConstant * lemma23PaperL D^(-4 : ℤ) ≤
      lemma171FirstLogMoment χ / lemma171MainTerm χ := by
  have hu := lemma171_actual_main_upper χ (by omega) hL
  have hm := lemma171_first_log_moment_ge_log_four χ hD
  have hL0 : 0 < lemma23PaperL D := by linarith
  have hc := lemma171_main_upper_constant_pos
  have hn : 0 ≤ Real.log 4 / 4 := div_nonneg (Real.log_nonneg (by norm_num)) (by norm_num)
  calc
    _ = (Real.log 4 / 4) / (lemma171MainUpperConstant * lemma23PaperL D^4) := by
      unfold lemma171FirstLogRelativeLowerConstant
      rw [zpow_neg, zpow_ofNat]
      field_simp [hc.ne', hL0.ne']
      <;> ring
    _ ≤ (Real.log 4 / 4) / lemma171MainTerm χ := div_le_div_of_nonneg_left hn ha hu
    _ ≤ _ := div_le_div_of_nonneg_right hm ha.le

/-- The strict relative mass is uniform under original (A), with the constant
and threshold chosen before conductor and character. -/
theorem lemma171_actual_first_log_relative_lower_uniform :
    ∃ D₀ : ℕ, 2 ≤ D₀ ∧ ∀ D : ℕ, D₀ ≤ D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ →
        lemma171FirstLogRelativeLowerConstant * lemma23PaperL D^(-4 : ℤ) ≤
          lemma171FirstLogMoment χ / lemma171MainTerm χ := by
  obtain ⟨D₁, hD₁, hmain⟩ := lemma171_actual_main_gt_half
  obtain ⟨D₂, hlog⟩ := eventually_atTop.mp
    (lemma171_log_tendsto_atTop.eventually (eventually_ge_atTop 2))
  refine ⟨max D₁ D₂, hD₁.trans (le_max_left _ _), ?_⟩
  intro D hD χ hA
  have h1 : D₁ ≤ D := (le_max_left _ _).trans hD
  have h2 : D₂ ≤ D := (le_max_right _ _).trans hD
  have ha := hmain D h1 χ hA
  exact lemma171_actual_first_log_relative_lower χ (hD₁.trans h1) (hlog D h2) (by linarith)

/-- The same arithmetic mass after division by the actual log P=L^9.
This is a mass bound only; it does not assert a matrix or projected gain. -/
theorem lemma171_actual_first_log_normalized_mass_lower_uniform :
    ∃ D₀ : ℕ, 2 ≤ D₀ ∧ ∀ D : ℕ, D₀ ≤ D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ →
        lemma171FirstLogRelativeLowerConstant * lemma23PaperL D^(-13 : ℤ) ≤
          lemma171FirstLogMoment χ /
            (lemma171MainTerm χ * Real.log (lemma23PaperP D)) := by
  obtain ⟨D₀, hD₀, hmass⟩ := lemma171_actual_first_log_relative_lower_uniform
  refine ⟨D₀, hD₀, ?_⟩
  intro D hD χ hA
  have hD1 : (1 : ℝ) < D := by exact_mod_cast (show 1 < D by omega)
  have hL : 0 < lemma23PaperL D := Real.log_pos hD1
  have hh := hmass D hD χ hA
  rw [lemma23PaperP, Real.log_exp, ← div_div]
  calc
    _ = (lemma171FirstLogRelativeLowerConstant * lemma23PaperL D^(-4 : ℤ)) /
        lemma23PaperL D^9 := by
      rw [zpow_neg, zpow_ofNat, zpow_neg, zpow_ofNat]
      field_simp [hL.ne']
      <;> ring
    _ ≤ _ := div_le_div_of_nonneg_right hh (pow_nonneg hL.le _)

end ZhangLS.Spec
