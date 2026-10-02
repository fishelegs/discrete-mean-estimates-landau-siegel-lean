import ZhangLS.Spec.Lemma56PerronContour
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Logarithmic finite-height cost of the actual cumulative Perron kernel -/

namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Real
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

lemma lemma56_perron_kernel_norm {B x : ℝ} (hx : 0 < x) (σ t : ℝ) :
    ‖lemma56PerronKernel B σ x t‖ =
      x ^ σ * Real.exp ((σ ^ 2 - t ^ 2) / (4 * B ^ 2)) /
        ‖(σ : ℂ) + (t : ℂ) * I‖ := by
  rw [lemma56PerronKernel, norm_div, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.norm_exp]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
    mul_zero, zero_mul, sub_zero, add_zero]
  congr 2
  have hcast : 4 * (B : ℂ) ^ 2 = ((4 * B ^ 2 : ℝ) : ℂ) := by push_cast; ring
  have hsq : (((σ : ℂ) + (t : ℂ) * I) ^ 2).re = σ ^ 2 - t ^ 2 := by
    rw [pow_two, Complex.mul_re]
    simp
    ring
  have hinv : (((4 * B ^ 2 : ℝ) : ℂ))⁻¹ = (((4 * B ^ 2)⁻¹ : ℝ) : ℂ) := by norm_cast
  rw [hcast, div_eq_mul_inv, hinv, Complex.mul_re, hsq]
  simp only [ofReal_re, ofReal_im, mul_zero, sub_zero]
  ring

lemma lemma56_perron_kernel_log_majorant {B x σ : ℝ} (hB : 0 < B) (hx : 0 < x)
    (hσ : (1 / 2 : ℝ) ≤ σ) (t : ℝ) :
    ‖lemma56PerronKernel B σ x t‖ ≤
      (3 * x ^ σ * Real.exp (σ ^ 2 / (4 * B ^ 2))) * (1 / (1 + |t|)) := by
  let z : ℂ := (σ : ℂ) + (t : ℂ) * I
  have hre : σ ≤ ‖z‖ := by simpa [z] using Complex.re_le_norm z
  have him : |t| ≤ ‖z‖ := by simpa [z] using Complex.abs_im_le_norm z
  have hn : 0 < ‖z‖ := by linarith only [hσ, hre]
  have hden : 0 < 1 + |t| := by positivity
  have hrec : 1 / ‖z‖ ≤ 3 / (1 + |t|) := by
    apply (div_le_div_iff₀ hn hden).mpr
    linarith only [hσ, hre, him]
  have hex : Real.exp ((σ ^ 2 - t ^ 2) / (4 * B ^ 2)) ≤
      Real.exp (σ ^ 2 / (4 * B ^ 2)) := by
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith only [sq_nonneg t]
  rw [lemma56_perron_kernel_norm hx σ t, div_eq_mul_inv]
  calc
    _ ≤ (x ^ σ * Real.exp (σ ^ 2 / (4 * B ^ 2))) * (3 / (1 + |t|)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hex (Real.rpow_nonneg hx.le _)
      · simpa only [one_div, z] using hrec
      · positivity
      · positivity
    _ = _ := by ring

lemma lemma56_perron_log_majorant_integral {H : ℝ} (hH : 0 ≤ H) :
    (∫ t : ℝ in -H..H, 1 / (1 + |t|)) = 2 * Real.log (1 + H) := by
  let g : ℝ → ℝ := fun t => 1 / (1 + |t|)
  have hc : Continuous g := by
    dsimp [g]
    exact continuous_const.div (continuous_const.add continuous_abs) (fun t => by positivity)
  have hpos : (∫ t : ℝ in 0..H, g t) = Real.log (1 + H) := by
    calc
      _ = ∫ t : ℝ in 0..H, 1 / (t + 1) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have ht0 : 0 ≤ t := (show t ∈ Set.Icc 0 H by simpa [Set.uIcc_of_le hH] using ht).1
        simp [g, abs_of_nonneg ht0, add_comm]
      _ = ∫ u : ℝ in 1..H + 1, 1 / u := by
        simpa only [zero_add] using intervalIntegral.integral_comp_add_right (fun u : ℝ => 1 / u)
          (a := 0) (b := H) 1
      _ = Real.log (1 + H) := by
        rw [integral_one_div_of_pos (by norm_num) (by linarith only [hH])]
        simp [add_comm]
  have hneg : (∫ t : ℝ in -H..0, g t) = ∫ t : ℝ in 0..H, g t := by
    have he := intervalIntegral.integral_comp_neg g (a := -H) (b := 0)
    simpa [g] using he
  have hsum := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) (-H) 0) (hc.intervalIntegrable (μ := volume) 0 H)
  change (∫ t : ℝ in -H..H, g t) = _
  rw [← hsum, hneg, hpos]
  ring

lemma lemma56_perron_vertical_integral_bound {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) {B x H M σ : ℝ} (hB : 0 < B) (hx : 0 < x)
    (hH : 0 ≤ H) (hM : 0 ≤ M) (hσ : (1 / 2 : ℝ) ≤ σ) (τ : ℝ)
    (hLD : ∀ t : ℝ, |t| ≤ H → ‖logDeriv (DirichletCharacter.LFunction θ)
      ((σ : ℂ) + (t : ℂ) * I - (τ : ℂ) * I)‖ ≤ M) :
    ‖∫ t : ℝ in -H..H, lemma56PerronArithmeticIntegrand θ B x τ
      ((σ : ℂ) + (t : ℂ) * I)‖ ≤
        6 * M * x ^ σ * Real.exp (σ ^ 2 / (4 * B ^ 2)) * Real.log (1 + H) := by
  let C := 3 * M * x ^ σ * Real.exp (σ ^ 2 / (4 * B ^ 2))
  let g : ℝ → ℝ := fun t => C * (1 / (1 + |t|))
  have hc : Continuous g := by
    dsimp [g]
    exact continuous_const.mul (continuous_const.div
      (continuous_const.add continuous_abs) (fun t => by positivity))
  calc
    _ ≤ ∫ t : ℝ in -H..H, g t := by
      apply intervalIntegral.norm_integral_le_of_norm_le (by linarith only [hH])
      · filter_upwards [] with t ht
        have htH : |t| ≤ H := abs_le.mpr ⟨ht.1.le, ht.2⟩
        change ‖-(logDeriv (DirichletCharacter.LFunction θ)
          ((σ : ℂ) + (t : ℂ) * I - (τ : ℂ) * I)) * lemma56PerronKernel B σ x t‖ ≤ g t
        rw [norm_mul, norm_neg]
        calc
          _ ≤ M * ‖lemma56PerronKernel B σ x t‖ :=
            mul_le_mul_of_nonneg_right (hLD t htH) (norm_nonneg _)
          _ ≤ M * ((3 * x ^ σ * Real.exp (σ ^ 2 / (4 * B ^ 2))) * (1 / (1 + |t|))) :=
            mul_le_mul_of_nonneg_left (lemma56_perron_kernel_log_majorant hB hx hσ t) hM
          _ = g t := by dsimp [g, C]; ring
      · exact hc.intervalIntegrable _ _
    _ = _ := by
      rw [show (∫ t : ℝ in -H..H, g t) = C * (∫ t : ℝ in -H..H, 1 / (1 + |t|)) by
        exact intervalIntegral.integral_const_mul _ _, lemma56_perron_log_majorant_integral hH]
      dsimp [C]
      ring

end ZhangLS.Spec
