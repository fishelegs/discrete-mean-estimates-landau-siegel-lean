import ZhangLS.Spec.Lemma31PowerIntegrals
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset MeasureTheory Set
set_option maxHeartbeats 2000000

lemma lemma31_nu_weighted_kernel_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (t : ℝ) (ht : (D : ℝ) ≤ t) :
    (t^2)⁻¹*lemma31NuCumulative χ t ≤
      realLAtOne χ*t⁻¹ + 6*Real.sqrt (D : ℝ)*t^(-3/2 : ℝ) := by
  have hp : 0 < t := lt_of_lt_of_le (by exact_mod_cast (show 0 < D by omega)) ht
  have he := mul_le_mul_of_nonneg_left (lemma31_nu_cumulative_real_bound χ hD t ht)
    (inv_nonneg.mpr (sq_nonneg t))
  have hi : (t^2)⁻¹*t = t⁻¹ := by field_simp
  calc
    _ ≤ (t^2)⁻¹*(t*realLAtOne χ + 6*Real.sqrt (D : ℝ)*Real.sqrt t) := he
    _ = realLAtOne χ*((t^2)⁻¹*t) +
        6*Real.sqrt (D : ℝ)*((t^2)⁻¹*Real.sqrt t) := by ring
    _ = _ := by rw [hi,lemma31_sqrt_inverse_square t hp]

lemma lemma31_nu_weighted_kernel_integrable {D : ℕ} (χ : RealPrimitiveCharacter D)
    (M N : ℕ) (hM : 1 ≤ M) :
    IntegrableOn (fun t : ℝ => (t^2)⁻¹*lemma31NuCumulative χ t) (Set.Ioc (M : ℝ) N) := by
  have hm : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hc : ContinuousOn (fun t : ℝ => (t^2)⁻¹) (Set.Icc (M : ℝ) N) := by
    apply ContinuousOn.inv₀
    · exact continuous_id.continuousOn.pow 2
    · intro t ht
      exact pow_ne_zero 2 (by linarith [ht.1])
  have he := integrableOn_mul_sum_Icc (m := 0) (lemma31NuReal χ)
    (show (0 : ℝ) ≤ M by linarith) hc.integrableOn_Icc
  have hi : IntegrableOn (fun t : ℝ => (t^2)⁻¹*lemma31NuCumulative χ t)
      (Set.Icc (M : ℝ) N) := by
    apply he.congr_fun _ measurableSet_Icc
    intro t ht
    dsimp only [lemma31NuCumulative]
    rw [lemma31_nu_real_sum_zero_to_one]
  exact hi.mono_set Set.Ioc_subset_Icc_self

end ZhangLS.Spec
