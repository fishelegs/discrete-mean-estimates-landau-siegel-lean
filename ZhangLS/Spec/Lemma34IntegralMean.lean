import ZhangLS.Spec.Lemma34PartialIntegrability
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
set_option autoImplicit false
namespace ZhangLS.Spec
open MeasureTheory Set
set_option maxHeartbeats 2000000

lemma lemma34_D_positive {D : ℕ} (hL : 3 ≤ lemma23PaperL D) : 0 < D := by
  by_cases h : D = 0
  · simp [h,lemma23PaperL] at hL
    linarith
  · exact Nat.pos_of_ne_zero h

lemma lemma34_inverse_integral {D : ℕ} (hL : 3 ≤ lemma23PaperL D) :
    (∫ t in Set.Ioc (1 : ℝ) ((D : ℝ)^80), 1/t) = 80*lemma23PaperL D := by
  have hD1 : 1 ≤ (D : ℝ) := by exact_mod_cast lemma34_D_positive hL
  have hR : 1 ≤ (D : ℝ)^80 := one_le_pow₀ hD1
  rw [← intervalIntegral.integral_of_le hR,
    integral_one_div_of_pos zero_lt_one (lt_of_lt_of_le zero_lt_one hR)]
  simp only [div_one,Real.log_pow,lemma23PaperL]
  norm_num

lemma lemma34_actual_sum_norms_square_mean {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hL : 3 ≤ lemma23PaperL D) (x : ℝ) (hx : 1 ≤ x) (hxD : x ≤ (D : ℝ)^80) :
    (∑ ψ ∈ lemma33ActualFamily D,
      (‖lemma23ActualX1 χ ψ.2 (lemma23PaperCenter D) x‖ +
        ‖lemma23ActualX2 χ ψ.2 (lemma23PaperCenter D) x‖)^2) ≤
      4 * lemma33ActualPrimeMass D * (81^1600 * lemma23PaperL D^1600) := by
  have h1 := lemma34_actual_x1_mean_square χ hL x hx hxD
  have h2 := lemma34_actual_x2_mean_square χ hL x hx hxD
  have hh : (∑ ψ ∈ lemma33ActualFamily D,
      (‖lemma23ActualX1 χ ψ.2 (lemma23PaperCenter D) x‖ +
        ‖lemma23ActualX2 χ ψ.2 (lemma23PaperCenter D) x‖)^2) ≤
      2*((∑ ψ ∈ lemma33ActualFamily D, ‖lemma23ActualX1 χ ψ.2 (lemma23PaperCenter D) x‖^2) +
        (∑ ψ ∈ lemma33ActualFamily D, ‖lemma23ActualX2 χ ψ.2 (lemma23PaperCenter D) x‖^2)) := by
    rw [← Finset.sum_add_distrib,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ψ hψ
    nlinarith [sq_nonneg (‖lemma23ActualX1 χ ψ.2 (lemma23PaperCenter D) x‖ -
      ‖lemma23ActualX2 χ ψ.2 (lemma23PaperCenter D) x‖)]
  linarith

lemma lemma34_actual_weighted_integral_cauchy {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N) (hL : 3 ≤ lemma23PaperL D) :
    (∫ t in Set.Ioc (1 : ℝ) ((D : ℝ)^80),
      (‖lemma23ActualX1 χ ψ (lemma23PaperCenter D) t‖ +
        ‖lemma23ActualX2 χ ψ (lemma23PaperCenter D) t‖)/t)^2 ≤
      (80*lemma23PaperL D) * (∫ t in Set.Ioc (1 : ℝ) ((D : ℝ)^80),
        (‖lemma23ActualX1 χ ψ (lemma23PaperCenter D) t‖ +
          ‖lemma23ActualX2 χ ψ (lemma23PaperCenter D) t‖)^2/t) := by
  let μ := volume.restrict (Set.Ioc (1 : ℝ) ((D : ℝ)^80))
  let f := fun t : ℝ => ‖lemma23ActualX1 χ ψ (lemma23PaperCenter D) t‖ +
    ‖lemma23ActualX2 χ ψ (lemma23PaperCenter D) t‖
  have hw : Integrable (fun t : ℝ => 1/t) μ := by
    simpa only [pow_zero] using lemma34_actual_partial_sums_weighted_integrable χ ψ 0
  have hfw : Integrable (fun t : ℝ => f t*(1/t)) μ := by
    simpa only [pow_one,mul_one_div] using lemma34_actual_partial_sums_weighted_integrable χ ψ 1
  have hf2w : Integrable (fun t : ℝ => f t^2*(1/t)) μ := by
    simpa only [mul_one_div] using lemma34_actual_partial_sums_weighted_integrable χ ψ 2
  have hn : 0 ≤ᵐ[μ] (fun t : ℝ => 1/t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact one_div_nonneg.mpr (le_of_lt (lt_trans zero_lt_one ht.1))
  have hW : 0 < ∫ t, 1/t ∂μ := by
    change 0 < ∫ t in Set.Ioc (1 : ℝ) ((D : ℝ)^80), 1/t
    rw [lemma34_inverse_integral hL]
    nlinarith
  have h := lemma34_weighted_integral_cauchy μ f (fun t => 1/t) hw hfw hf2w hn hW
  simpa only [μ,f,mul_one_div,lemma34_inverse_integral hL] using h

lemma lemma34_actual_weighted_square_integral_mean {D : ℕ}
    (χ : RealPrimitiveCharacter D) (hL : 3 ≤ lemma23PaperL D) :
    (∑ ψ ∈ lemma33ActualFamily D,
      ∫ t in Set.Ioc (1 : ℝ) ((D : ℝ)^80),
        (‖lemma23ActualX1 χ ψ.2 (lemma23PaperCenter D) t‖ +
          ‖lemma23ActualX2 χ ψ.2 (lemma23PaperCenter D) t‖)^2/t) ≤
      (4*lemma33ActualPrimeMass D*(81^1600*lemma23PaperL D^1600)) *
        (80*lemma23PaperL D) := by
  let μ := volume.restrict (Set.Ioc (1 : ℝ) ((D : ℝ)^80))
  let f : lemma33CharacterIndex D → ℝ → ℝ := fun ψ t =>
    (‖lemma23ActualX1 χ ψ.2 (lemma23PaperCenter D) t‖ +
      ‖lemma23ActualX2 χ ψ.2 (lemma23PaperCenter D) t‖)^2/t
  let K := 4*lemma33ActualPrimeMass D*(81^1600*lemma23PaperL D^1600)
  have hf (ψ : lemma33CharacterIndex D) : Integrable (f ψ) μ :=
    lemma34_actual_partial_sums_weighted_integrable χ ψ.2 2
  have hs : Integrable (fun t => ∑ ψ ∈ lemma33ActualFamily D, f ψ t) μ :=
    integrable_finsetSum _ (fun ψ _ => hf ψ)
  have hw : Integrable (fun t : ℝ => 1/t) μ := by
    simpa only [pow_zero] using
      lemma34_actual_partial_sums_weighted_integrable χ (1 : DirichletCharacter ℂ 1) 0
  have hK : Integrable (fun t : ℝ => K/t) μ := by
    simpa only [mul_one_div] using hw.const_mul K
  have hmono : (fun t => ∑ ψ ∈ lemma33ActualFamily D, f ψ t) ≤ᵐ[μ] (fun t => K/t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    dsimp only [f,K]
    rw [← Finset.sum_div]
    exact div_le_div_of_nonneg_right
      (lemma34_actual_sum_norms_square_mean χ hL t ht.1.le ht.2) (by linarith [ht.1])
  calc
    _ = ∫ t, ∑ ψ ∈ lemma33ActualFamily D, f ψ t ∂μ :=
      (integral_finsetSum _ (fun ψ _ => hf ψ)).symm
    _ ≤ ∫ t, K/t ∂μ := integral_mono_ae hs hK hmono
    _ = K * (80*lemma23PaperL D) := by
      simp_rw [div_eq_mul_inv]
      rw [integral_const_mul]
      congr 1
      simpa only [one_div] using lemma34_inverse_integral hL

lemma lemma34_actual_integral_mean_square {D : ℕ}
    (χ : RealPrimitiveCharacter D) (hL : 3 ≤ lemma23PaperL D) :
    (∑ ψ ∈ lemma33ActualFamily D,
      (∫ t in Set.Ioc (1 : ℝ) ((D : ℝ)^80),
        (‖lemma23ActualX1 χ ψ.2 (lemma23PaperCenter D) t‖ +
          ‖lemma23ActualX2 χ ψ.2 (lemma23PaperCenter D) t‖)/t)^2) ≤
      (80*lemma23PaperL D)^2 *
        (4*lemma33ActualPrimeMass D*(81^1600*lemma23PaperL D^1600)) := by
  calc
    _ ≤ ∑ ψ ∈ lemma33ActualFamily D, (80*lemma23PaperL D) *
      (∫ t in Set.Ioc (1 : ℝ) ((D : ℝ)^80),
        (‖lemma23ActualX1 χ ψ.2 (lemma23PaperCenter D) t‖ +
          ‖lemma23ActualX2 χ ψ.2 (lemma23PaperCenter D) t‖)^2/t) := by
      apply Finset.sum_le_sum
      intro ψ hψ
      exact lemma34_actual_weighted_integral_cauchy χ ψ.2 hL
    _ = (80*lemma23PaperL D) * ∑ ψ ∈ lemma33ActualFamily D,
      (∫ t in Set.Ioc (1 : ℝ) ((D : ℝ)^80),
        (‖lemma23ActualX1 χ ψ.2 (lemma23PaperCenter D) t‖ +
          ‖lemma23ActualX2 χ ψ.2 (lemma23PaperCenter D) t‖)^2/t) := by rw [Finset.mul_sum]
    _ ≤ (80*lemma23PaperL D) *
      ((4*lemma33ActualPrimeMass D*(81^1600*lemma23PaperL D^1600)) *
        (80*lemma23PaperL D)) := mul_le_mul_of_nonneg_left
          (lemma34_actual_weighted_square_integral_mean χ hL) (by linarith)
    _ = _ := by ring

end ZhangLS.Spec
