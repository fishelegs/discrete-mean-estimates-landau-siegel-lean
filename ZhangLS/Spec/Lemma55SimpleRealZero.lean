import ZhangLS.Spec.Lemma55LocalDerivatives
import ZhangLS.Spec.RealAxisContinuation
import ZhangLS.Spec.Lemma57LeftQuadraticGrowth
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The simple real zero in the first conclusion of Lemma 5.5

Under (A) and the proved Lemma 5.7 threshold, the actual derivative stays
at least 1/32 on [1-64(log D)^(-2022),1]. The left endpoint has negative
L-value, and the value at one is positive. The intermediate value theorem
therefore constructs an actual simple real zero with the claimed distance.
The full height-2D exclusion of other zeros is a separate open obligation.
-/

namespace ZhangLS.Spec

open Complex Set
open scoped Real

set_option maxRecDepth 4096
set_option maxHeartbeats 600000

noncomputable def lemma55RealZeroWidth (D : ℕ) : ℝ :=
  64 * Real.log (D : ℝ) ^ (-2022 : ℤ)

theorem lemma55_local_zero_budget {D : ℕ}
    (hDN : lemma57ExplicitModulusThreshold ≤ D) :
    0 < lemma55RealZeroWidth D ∧
      lemma55RealZeroWidth D ≤ 1 / (4 * Real.log (D : ℝ)) ∧
      (128 * Real.exp 1 * Real.log (D : ℝ) ^ 3) * lemma55RealZeroWidth D ≤ 1 / 32 := by
  let L := Real.log (D : ℝ)
  have hL : 10000000 ≤ L := lemma57_log_ge_ten_million hDN
  clear hDN
  have hLp : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hwidth : 0 < lemma55RealZeroWidth D := by
    unfold lemma55RealZeroWidth
    positivity
  have hp2021 : L ^ (-2021 : ℤ) ≤ L⁻¹ := by
    simpa using zpow_le_zpow_right₀ hL1 (show (-2021 : ℤ) ≤ -1 by norm_num)
  have hp2019 : L ^ (-2019 : ℤ) ≤ L⁻¹ := by
    simpa using zpow_le_zpow_right₀ hL1 (show (-2019 : ℤ) ≤ -1 by norm_num)
  have hcancel1 : L * L ^ (-2022 : ℤ) = L ^ (-2021 : ℤ) := by
    simpa using (zpow_add₀ hLp.ne' 1 (-2022)).symm
  have hcancel3 : L ^ 3 * L ^ (-2022 : ℤ) = L ^ (-2019 : ℤ) := by
    simpa using (zpow_add₀ hLp.ne' 3 (-2022)).symm
  refine ⟨hwidth, ?_, ?_⟩
  · apply (le_div_iff₀ (by positivity : 0 < 4 * L)).mpr
    change (64 * L ^ (-2022 : ℤ)) * (4 * L) ≤ 1
    calc
      _ = 256 * (L * L ^ (-2022 : ℤ)) := by ring
      _ = 256 * L ^ (-2021 : ℤ) := by rw [hcancel1]
      _ ≤ 256 * L⁻¹ := mul_le_mul_of_nonneg_left hp2021 (by norm_num)
      _ ≤ 1 := by
        rw [← div_eq_mul_inv]
        exact (div_le_one hLp).mpr (by linarith)
  · change (128 * Real.exp 1 * L ^ 3) * (64 * L ^ (-2022 : ℤ)) ≤ 1 / 32
    calc
      _ = 8192 * Real.exp 1 * (L ^ 3 * L ^ (-2022 : ℤ)) := by ring
      _ = 8192 * Real.exp 1 * L ^ (-2019 : ℤ) := by rw [hcancel3]
      _ ≤ 8192 * Real.exp 1 * L⁻¹ :=
        mul_le_mul_of_nonneg_left hp2019 (by positivity)
      _ ≤ 8192 * 3 * L⁻¹ := by
        gcongr
        exact Real.exp_one_lt_three.le
      _ ≤ 1 / 32 := by
        rw [← div_eq_mul_inv]
        apply (div_le_iff₀ hLp).mpr
        linarith

theorem lemma55_actual_real_derivative_lower_bound
    {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hDN : lemma57ExplicitModulusThreshold ≤ D) (hA : NormalizedAssumptionA χ)
    {x : ℝ} (hx : |x - 1| ≤ lemma55RealZeroWidth D) :
    (1 : ℝ) / 32 ≤ deriv (realLValue χ) x := by
  have hD := lemma57_one_lt_of_explicit_threshold hDN
  have hL : 2 ≤ Real.log (D : ℝ) := by
    linarith [lemma57_log_ge_ten_million hDN]
  have hb := lemma55_local_zero_budget hDN
  have hdist : ‖(x : ℂ) - 1‖ = |x - 1| := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hvar := lemma55_actual_first_derivative_variation χ hD hL
    (s := (x : ℂ)) (by rw [hdist]; exact hx.trans hb.2.1)
  have hnorm : ‖deriv (dirichletLFunction χ) (x : ℂ) - LDerivAtOne χ‖ ≤ 1 / 32 := by
    apply hvar.trans
    rw [hdist]
    exact (mul_le_mul_of_nonneg_left hx (by positivity)).trans hb.2.2
  have hre := (Complex.abs_re_le_norm
    (deriv (dirichletLFunction χ) (x : ℂ) - LDerivAtOne χ)).trans hnorm
  rw [Complex.sub_re, ← realLDerivAtOne_eq_re χ hD,
    ← realLValue_deriv_eq_re χ hD x] at hre
  have hlower := lemma57_one_sixteenth_at_explicit_threshold χ hDN hA
  have hscale := lemma57Scale_ge_one hD
  have hleft := (abs_le.mp hre).1
  nlinarith only [hscale, hlower, hleft]

/-- The first original conclusion, with an explicit absolute distance constant
64 and the same closed modulus threshold as the proved Lemma 5.7. -/
theorem lemma55_actual_simple_real_zero
    {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hDN : lemma57ExplicitModulusThreshold ≤ D) (hA : NormalizedAssumptionA χ) :
    ∃ ρ : ℝ, 0 < 1 - ρ ∧
      1 - ρ ≤ 64 * Real.log (D : ℝ) ^ (-2022 : ℤ) ∧
      dirichletLFunction χ (ρ : ℂ) = 0 ∧
      deriv (dirichletLFunction χ) (ρ : ℂ) ≠ 0 := by
  have hD := lemma57_one_lt_of_explicit_threshold hDN
  let w := lemma55RealZeroWidth D
  have hwp : 0 < w := (lemma55_local_zero_budget hDN).1
  have hdiff : Differentiable ℝ (realLValue χ) :=
    fun x => (realLValue_hasDerivAt χ hD x).differentiableAt
  have hder (x : ℝ) (hx : x ∈ Icc (1 - w) 1) :
      (1 : ℝ) / 32 ≤ deriv (realLValue χ) x := by
    apply lemma55_actual_real_derivative_lower_bound χ hDN hA
    rw [abs_of_nonpos (by linarith [hx.2] : x - 1 ≤ 0)]
    linarith [hx.1]
  have hmean := (convex_Icc (1 - w) 1).mul_sub_le_image_sub_of_le_deriv
    hdiff.continuous.continuousOn hdiff.differentiableOn
    (fun x hx => hder x (interior_subset hx))
    (1 - w) (left_mem_Icc.mpr (by linarith)) 1
    (right_mem_Icc.mpr (by linarith)) (by linarith)
  have hA' : realLValue χ 1 < Real.log (D : ℝ) ^ (-2022 : ℤ) := by
    simpa [NormalizedAssumptionA, AssumptionAWithConstant, realLAtOne] using hA
  have hleft : realLValue χ (1 - w) < 0 := by
    have hwpow : w = 64 * Real.log (D : ℝ) ^ (-2022 : ℤ) := rfl
    nlinarith only [hmean, hA', hwp, hwpow]
  have hright : 0 < realLValue χ 1 := realLAtOne_pos χ hD
  obtain ⟨ρ, hρ, hzero⟩ :=
    (intermediate_value_Icc (by linarith : 1 - w ≤ 1) hdiff.continuous.continuousOn)
      (show (0 : ℝ) ∈ Icc (realLValue χ (1 - w)) (realLValue χ 1) from
        ⟨hleft.le, hright.le⟩)
  have hρlt : ρ < 1 := by
    have hρne : ρ ≠ 1 := by intro heq; subst ρ; linarith
    exact lt_of_le_of_ne hρ.2 hρne
  have hderρ := hder ρ hρ
  refine ⟨ρ, by linarith, by change 1 - ρ ≤ w; linarith [hρ.1], ?_, ?_⟩
  · rw [dirichletLFunction_real_eq_realLValue χ hD ρ, hzero]
    simp
  · intro hdzero
    rw [realLValue_deriv_eq_re χ hD ρ, hdzero] at hderρ
    norm_num at hderρ

end ZhangLS.Spec
