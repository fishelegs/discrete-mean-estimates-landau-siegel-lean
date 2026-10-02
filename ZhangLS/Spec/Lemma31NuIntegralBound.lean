import ZhangLS.Spec.Lemma31WeightedKernel
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset MeasureTheory Set
set_option maxHeartbeats 2000000

lemma lemma31_nu_weighted_integral_le {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (M N : ℕ) (hDM : D ≤ M) (hMN : M ≤ N) :
    (∫ t : ℝ in Set.Ioc (M : ℝ) N, (t^2)⁻¹*lemma31NuCumulative χ t) ≤
      realLAtOne χ*Real.log (N : ℝ) + 12*Real.sqrt (D : ℝ)*(Real.sqrt (M : ℝ))⁻¹ := by
  have hm : (1 : ℝ) ≤ M := by exact_mod_cast (hD.le.trans hDM)
  have hm0 : (0 : ℝ) < M := by linarith
  have hmn : (M : ℝ) ≤ N := by exact_mod_cast hMN
  have hdc : (D : ℝ) ≤ M := by exact_mod_cast hDM
  have hM : 1 ≤ M := hD.le.trans hDM
  have hL : 0 ≤ realLAtOne χ := (realLAtOne_pos χ hD).le
  have hK : 0 ≤ 6*Real.sqrt (D : ℝ) := by positivity
  have hc : ContinuousOn (fun t : ℝ => t⁻¹) (Set.Icc (M : ℝ) N) := by
    apply ContinuousOn.inv₀ continuous_id.continuousOn
    intro t ht
    change t ≠ 0
    linarith [ht.1]
  have hi : IntegrableOn (fun t : ℝ => t⁻¹) (Set.Ioc (M : ℝ) N) :=
    hc.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hp : IntegrableOn (fun t : ℝ => t^(-3/2 : ℝ)) (Set.Ioc (M : ℝ) N) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3/2 : ℝ) < -1) hm0).mono_set
      Set.Ioc_subset_Ioi_self
  have hiL := hi.const_mul (realLAtOne χ)
  have hpK := hp.const_mul (6*Real.sqrt (D : ℝ))
  have hlog : Real.log (M : ℝ) ≥ 0 := Real.log_nonneg hm
  calc
    _ ≤ ∫ t : ℝ in Set.Ioc (M : ℝ) N,
        realLAtOne χ*t⁻¹ + 6*Real.sqrt (D : ℝ)*t^(-3/2 : ℝ) := by
      apply integral_mono_ae (lemma31_nu_weighted_kernel_integrable χ M N hM) (hiL.add hpK)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact lemma31_nu_weighted_kernel_bound χ hD t (hdc.trans ht.1.le)
    _ = realLAtOne χ*(Real.log (N : ℝ)-Real.log (M : ℝ)) +
        6*Real.sqrt (D : ℝ)*(∫ t : ℝ in Set.Ioc (M : ℝ) N, t^(-3/2 : ℝ)) := by
      rw [integral_add hiL hpK,integral_const_mul,integral_const_mul,
        lemma31_inverse_partial_integral (M : ℝ) (N : ℝ) hm0 hmn]
    _ ≤ realLAtOne χ*Real.log (N : ℝ) +
        6*Real.sqrt (D : ℝ)*(2*(Real.sqrt (M : ℝ))⁻¹) := add_le_add
      (mul_le_mul_of_nonneg_left (sub_le_self _ hlog) hL)
      (mul_le_mul_of_nonneg_left
        (lemma31_three_halves_partial_integral_le (M : ℝ) (N : ℝ) hm0) hK)
    _ = _ := by ring

end ZhangLS.Spec
