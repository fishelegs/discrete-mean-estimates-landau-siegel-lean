import ZhangLS.Spec.Lemma36Integrability
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex MeasureTheory Set
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma36_actual_weighted_integral_cauchy {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N) (hL : 3 ≤ lemma23PaperL D) :
    (∫ t in Set.Ioc ((D : ℝ)^4) ((D : ℝ)^8),
      (‖lemma23ActualX4 χ ψ t‖)/t)^2 ≤
      (4*lemma23PaperL D) * (∫ t in Set.Ioc ((D : ℝ)^4) ((D : ℝ)^8),
        (‖lemma23ActualX4 χ ψ t‖)^2/t) := by
  have hp := lemma36_interval_parameters hL
  have hD1 : 1 ≤ D := hp.1
  have hDr : (0 : ℝ) < D := by exact_mod_cast hp.1
  let μ := volume.restrict (Set.Ioc ((D : ℝ)^4) ((D : ℝ)^8))
  let f := fun t : ℝ => ‖lemma23ActualX4 χ ψ t‖
  have hw : Integrable (fun t : ℝ => 1/t) μ := by
    simpa only [pow_zero] using lemma36_actual_X4_power_weighted_integrable χ ψ hD1 0
  have hfw : Integrable (fun t : ℝ => f t*(1/t)) μ := by
    simpa only [pow_one,mul_one_div] using lemma36_actual_X4_power_weighted_integrable χ ψ hD1 1
  have hf2w : Integrable (fun t : ℝ => f t^2*(1/t)) μ := by
    simpa only [mul_one_div] using lemma36_actual_X4_power_weighted_integrable χ ψ hD1 2
  have hn : 0 ≤ᵐ[μ] (fun t : ℝ => 1/t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact one_div_nonneg.mpr (le_of_lt ((pow_pos hDr 4).trans ht.1))
  have hW : 0 < ∫ t, 1/t ∂μ := by
    change 0 < ∫ t in Set.Ioc ((D : ℝ)^4) ((D : ℝ)^8), 1/t
    rw [lemma36_inverse_integral hL]
    exact hp.2.2
  have h := lemma34_weighted_integral_cauchy μ f (fun t => 1/t) hw hfw hf2w hn hW
  simpa only [μ,f,mul_one_div,lemma36_inverse_integral hL] using h

lemma lemma36_actual_weighted_square_integral_mean_le {D : ℕ}
    (χ : RealPrimitiveCharacter D) (hL : 3 ≤ lemma23PaperL D) (K : ℝ)
    (hmean : ∀ t : ℝ, t ≤ ((D : ℝ)^8) →
      (∑ ψ ∈ lemma33ActualFamily D, ‖lemma23ActualX4 χ ψ.2 t‖^2) ≤ K) :
    (∑ ψ ∈ lemma33ActualFamily D,
      ∫ t in Set.Ioc ((D : ℝ)^4) ((D : ℝ)^8), ‖lemma23ActualX4 χ ψ.2 t‖^2/t) ≤
        K*(4*lemma23PaperL D) := by
  have hp := lemma36_interval_parameters hL
  have hD1 : 1 ≤ D := hp.1
  have hDr : (0 : ℝ) < D := by exact_mod_cast hp.1
  let μ := volume.restrict (Set.Ioc ((D : ℝ)^4) ((D : ℝ)^8))
  let f : lemma33CharacterIndex D → ℝ → ℝ := fun ψ t =>
    (‖lemma23ActualX4 χ ψ.2 t‖)^2/t
  have hf (ψ : lemma33CharacterIndex D) : Integrable (f ψ) μ :=
    lemma36_actual_X4_power_weighted_integrable χ ψ.2 hD1 2
  have hs : Integrable (fun t => ∑ ψ ∈ lemma33ActualFamily D, f ψ t) μ :=
    integrable_finsetSum _ (fun ψ _ => hf ψ)
  have hw : Integrable (fun t : ℝ => 1/t) μ := lemma36_inverse_integrable hL
  have hK : Integrable (fun t : ℝ => K/t) μ := by
    simpa only [mul_one_div] using hw.const_mul K
  have hmono : (fun t => ∑ ψ ∈ lemma33ActualFamily D, f ψ t) ≤ᵐ[μ] (fun t => K/t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    dsimp only [f]
    rw [← Finset.sum_div]
    exact div_le_div_of_nonneg_right
      (hmean t ht.2) ((pow_pos hDr 4).trans ht.1).le
  calc
    _ = ∫ t, ∑ ψ ∈ lemma33ActualFamily D, f ψ t ∂μ :=
      (integral_finsetSum _ (fun ψ _ => hf ψ)).symm
    _ ≤ ∫ t, K/t ∂μ := integral_mono_ae hs hK hmono
    _ = K * (4*lemma23PaperL D) := by
      simp_rw [div_eq_mul_inv]
      rw [integral_const_mul]
      congr 1
      simpa only [one_div] using lemma36_inverse_integral hL

lemma lemma36_actual_integral_mean_square_le {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hL : 3 ≤ lemma23PaperL D) (K : ℝ)
    (hmean : ∀ t : ℝ, t ≤ ((D : ℝ)^8) →
      (∑ ψ ∈ lemma33ActualFamily D, ‖lemma23ActualX4 χ ψ.2 t‖^2) ≤ K) :
    (∑ ψ ∈ lemma33ActualFamily D,
      (∫ t in Set.Ioc ((D : ℝ)^4) ((D : ℝ)^8), ‖lemma23ActualX4 χ ψ.2 t‖/t)^2) ≤
        K*(4*lemma23PaperL D)^2 := by
  have hw : 0 ≤ (4*lemma23PaperL D) := (lemma36_interval_parameters hL).2.2.le
  calc
    _ ≤ ∑ ψ ∈ lemma33ActualFamily D,
        (4*lemma23PaperL D)*(∫ t in Set.Ioc ((D : ℝ)^4) ((D : ℝ)^8),
          ‖lemma23ActualX4 χ ψ.2 t‖^2/t) :=
      Finset.sum_le_sum (fun ψ _ => lemma36_actual_weighted_integral_cauchy χ ψ.2 hL)
    _ = (4*lemma23PaperL D)*(∑ ψ ∈ lemma33ActualFamily D,
        ∫ t in Set.Ioc ((D : ℝ)^4) ((D : ℝ)^8), ‖lemma23ActualX4 χ ψ.2 t‖^2/t) := by
      rw [Finset.mul_sum]
    _ ≤ (4*lemma23PaperL D)*(K*(4*lemma23PaperL D)) := mul_le_mul_of_nonneg_left
      (lemma36_actual_weighted_square_integral_mean_le χ hL K hmean) hw
    _ = _ := by ring

/-- Exactly the left-hand side of `Lemma23GoodPartialSums.condition36`. -/
noncomputable def lemma36ActualB {D q : ℕ} (χ : RealPrimitiveCharacter D)
    (ψ : DirichletCharacter ℂ q) : ℝ :=
  ‖lemma23ActualX4 χ ψ ((D : ℝ)^8)‖ +
    ∫ t : ℝ in Set.Ioc ((D : ℝ)^4) ((D : ℝ)^8), ‖lemma23ActualX4 χ ψ t‖/t

lemma lemma36_actual_B_nonneg {D q : ℕ} (χ : RealPrimitiveCharacter D)
    (ψ : DirichletCharacter ℂ q) : 0 ≤ lemma36ActualB χ ψ := by
  unfold lemma36ActualB
  apply add_nonneg (norm_nonneg _)
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have hp : 0 < t := lt_of_le_of_lt (pow_nonneg (Nat.cast_nonneg D) 4) ht.1
  exact div_nonneg (norm_nonneg _) hp.le

/-- A uniform second-moment estimate for `X₄` gives the endpoint-plus-integral
second moment with the explicit loss `34 L²`. -/
lemma lemma36_actual_B_mean_square_le {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hL : 3 ≤ lemma23PaperL D) (K : ℝ) (hK : 0 ≤ K)
    (hmean : ∀ t : ℝ, t ≤ (D : ℝ)^8 →
      (∑ ψ ∈ lemma33ActualFamily D, ‖lemma23ActualX4 χ ψ.2 t‖^2) ≤ K) :
    (∑ ψ ∈ lemma33ActualFamily D, (lemma36ActualB χ ψ.2)^2) ≤
      34*K*lemma23PaperL D^2 := by
  have he := hmean ((D : ℝ)^8) le_rfl
  have hi := lemma36_actual_integral_mean_square_le χ hL K hmean
  have hl2 : 1 ≤ lemma23PaperL D^2 := one_le_pow₀ (show 1 ≤ lemma23PaperL D by linarith)
  have hpoint (ψ : lemma33CharacterIndex D) : (lemma36ActualB χ ψ.2)^2 ≤
      2*‖lemma23ActualX4 χ ψ.2 ((D : ℝ)^8)‖^2 +
        2*(∫ t in Set.Ioc ((D : ℝ)^4) ((D : ℝ)^8), ‖lemma23ActualX4 χ ψ.2 t‖/t)^2 := by
    unfold lemma36ActualB
    nlinarith [sq_nonneg (‖lemma23ActualX4 χ ψ.2 ((D : ℝ)^8)‖ -
      (∫ t in Set.Ioc ((D : ℝ)^4) ((D : ℝ)^8), ‖lemma23ActualX4 χ ψ.2 t‖/t))]
  have hlow : 2*K ≤ 2*K*lemma23PaperL D^2 :=
    le_mul_of_one_le_right (mul_nonneg (by norm_num) hK) hl2
  calc
    _ ≤ ∑ ψ ∈ lemma33ActualFamily D,
        (2*‖lemma23ActualX4 χ ψ.2 ((D : ℝ)^8)‖^2 +
          2*(∫ t in Set.Ioc ((D : ℝ)^4) ((D : ℝ)^8), ‖lemma23ActualX4 χ ψ.2 t‖/t)^2) :=
      Finset.sum_le_sum (fun ψ _ => hpoint ψ)
    _ = 2*(∑ ψ ∈ lemma33ActualFamily D, ‖lemma23ActualX4 χ ψ.2 ((D : ℝ)^8)‖^2) +
        2*(∑ ψ ∈ lemma33ActualFamily D,
          (∫ t in Set.Ioc ((D : ℝ)^4) ((D : ℝ)^8), ‖lemma23ActualX4 χ ψ.2 t‖/t)^2) := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
    _ ≤ 2*K + 2*(K*(4*lemma23PaperL D)^2) := add_le_add
      (mul_le_mul_of_nonneg_left he (by norm_num)) (mul_le_mul_of_nonneg_left hi (by norm_num))
    _ ≤ _ := by nlinarith

end ZhangLS.Spec
