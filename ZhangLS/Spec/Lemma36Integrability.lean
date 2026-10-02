import ZhangLS.Spec.Lemma34WeightedCauchy
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex MeasureTheory Set
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def lemma36ActualTailCoefficient {D q : ℕ} (χ : RealPrimitiveCharacter D)
    (ψ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  if D^4 < n then lemma23ActualVarsigma χ n * ψ (n : ZMod q) *
    Complex.exp (-lemma23PaperCenter D * (Real.log (n : ℝ) : ℂ)) else 0

lemma lemma36_actual_X4_eq_partial_sum {D q : ℕ} (χ : RealPrimitiveCharacter D)
    (ψ : DirichletCharacter ℂ q) (x : ℝ) :
    lemma23ActualX4 χ ψ x =
      ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, lemma36ActualTailCoefficient χ ψ n := by
  have hs : {n ∈ Finset.Icc 0 ⌊x⌋₊ | D^4 < n} = Finset.Ioc (D^4) ⌊x⌋₊ := by
    ext n
    simp only [Finset.mem_filter,Finset.mem_Icc,Finset.mem_Ioc]
    omega
  unfold lemma23ActualX4 lemma36ActualTailCoefficient
  rw [← Finset.sum_filter,hs]

lemma lemma36_actual_X4_measurable {D q : ℕ} (χ : RealPrimitiveCharacter D)
    (ψ : DirichletCharacter ℂ q) : Measurable (fun t : ℝ => lemma23ActualX4 χ ψ t) := by
  have he : (fun t : ℝ => lemma23ActualX4 χ ψ t) =
      (fun t : ℝ => ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, lemma36ActualTailCoefficient χ ψ n) := by
    funext t
    exact lemma36_actual_X4_eq_partial_sum χ ψ t
  rw [he]
  exact (measurable_of_countable
    (fun N : ℕ => ∑ n ∈ Finset.Icc 0 N, lemma36ActualTailCoefficient χ ψ n)).comp Nat.measurable_floor

lemma lemma36_actual_X4_partial_norm_bound {D q : ℕ} (χ : RealPrimitiveCharacter D)
    (ψ : DirichletCharacter ℂ q) (t : ℝ) (ht : t ≤ ((D : ℝ)^8)) :
    ‖lemma23ActualX4 χ ψ t‖ ≤
      ∑ n ∈ Finset.Icc 0 ⌊((D : ℝ)^8)⌋₊, ‖lemma36ActualTailCoefficient χ ψ n‖ := by
  rw [lemma36_actual_X4_eq_partial_sum]
  apply (norm_sum_le _ _).trans
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Icc_subset_Icc_right (Nat.floor_le_floor ht)) (by intros; positivity)

lemma lemma36_actual_X4_integrable {D q : ℕ} (χ : RealPrimitiveCharacter D)
    (ψ : DirichletCharacter ℂ q) :
    IntegrableOn (fun t : ℝ => lemma23ActualX4 χ ψ t)
      (Set.Ioc ((D : ℝ)^4) ((D : ℝ)^8)) := by
  let B : ℝ := ∑ n ∈ Finset.Icc 0 ⌊((D : ℝ)^8)⌋₊, ‖lemma36ActualTailCoefficient χ ψ n‖
  have hb : IntegrableOn (fun _ : ℝ => B)
      (Set.Ioc ((D : ℝ)^4) ((D : ℝ)^8)) := continuous_const.integrableOn_Ioc
  apply hb.mono' (lemma36_actual_X4_measurable χ ψ).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact lemma36_actual_X4_partial_norm_bound χ ψ t ht.2

lemma lemma36_actual_X4_power_weighted_integrable {D q : ℕ} (χ : RealPrimitiveCharacter D)
    (ψ : DirichletCharacter ℂ q) (hD : 1 ≤ D) (m : ℕ) :
    IntegrableOn (fun t : ℝ => ‖lemma23ActualX4 χ ψ t‖^m/t)
      (Set.Ioc ((D : ℝ)^4) ((D : ℝ)^8)) := by
  let B : ℝ := ∑ n ∈ Finset.Icc 0 ⌊((D : ℝ)^8)⌋₊, ‖lemma36ActualTailCoefficient χ ψ n‖
  have hm : Measurable (fun t : ℝ => ‖lemma23ActualX4 χ ψ t‖^m/t) :=
    ((lemma36_actual_X4_measurable χ ψ).norm.pow_const m).div measurable_id
  have hb : IntegrableOn (fun _ : ℝ => B^m)
      (Set.Ioc ((D : ℝ)^4) ((D : ℝ)^8)) := continuous_const.integrableOn_Ioc
  have hd : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hd4 : (1 : ℝ) ≤ (D : ℝ)^4 := one_le_pow₀ hd
  apply hb.mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have ht1 : 1 ≤ t := hd4.trans ht.1.le
  have ht0 : 0 < t := by linarith
  have hn := lemma36_actual_X4_partial_norm_bound χ ψ t ht.2
  have hp := pow_le_pow_left₀ (norm_nonneg _) hn m
  rw [Real.norm_of_nonneg (div_nonneg (pow_nonneg (norm_nonneg _) _) ht0.le)]
  exact (div_le_self (pow_nonneg (norm_nonneg _) _) ht1).trans hp

/-- The interval in condition (3.6) has positive logarithmic length. -/
lemma lemma36_interval_parameters {D : ℕ} (hL : 3 ≤ lemma23PaperL D) :
    0 < D ∧ (D : ℝ)^4 < (D : ℝ)^8 ∧ 0 < 4*lemma23PaperL D := by
  have hd : 0 < D := by
    by_contra h
    have hz : D = 0 := by omega
    simp [hz,lemma23PaperL] at hL
    linarith
  have hdR : (0 : ℝ) < D := by exact_mod_cast hd
  have he4 : (D : ℝ)^4 = Real.exp (4*lemma23PaperL D) := by
    have he := Real.exp_nat_mul (lemma23PaperL D) 4
    norm_num at he
    rw [lemma23PaperL,Real.exp_log hdR] at he
    exact he.symm
  have he8 : (D : ℝ)^8 = Real.exp (8*lemma23PaperL D) := by
    have he := Real.exp_nat_mul (lemma23PaperL D) 8
    norm_num at he
    rw [lemma23PaperL,Real.exp_log hdR] at he
    exact he.symm
  refine ⟨hd,?_,by linarith⟩
  rw [he4,he8]
  exact Real.exp_lt_exp.mpr (by linarith)

/-- The reciprocal weight on the condition-(3.6) interval integrates to `4 L`. -/
lemma lemma36_inverse_integral {D : ℕ} (hL : 3 ≤ lemma23PaperL D) :
    (∫ t : ℝ in Set.Ioc ((D : ℝ)^4) ((D : ℝ)^8), 1/t) = 4*lemma23PaperL D := by
  have hp := lemma36_interval_parameters hL
  have hd : (0 : ℝ) < D := by exact_mod_cast hp.1
  rw [← intervalIntegral.integral_of_le hp.2.1.le,
    integral_one_div_of_pos (pow_pos hd 4) (pow_pos hd 8)]
  rw [Real.log_div (pow_ne_zero 8 (ne_of_gt hd)) (pow_ne_zero 4 (ne_of_gt hd))]
  simp only [Real.log_pow,lemma23PaperL,Nat.cast_ofNat]
  ring

lemma lemma36_inverse_integrable {D : ℕ} (hL : 3 ≤ lemma23PaperL D) :
    IntegrableOn (fun t : ℝ => 1/t) (Set.Ioc ((D : ℝ)^4) ((D : ℝ)^8)) := by
  have hp := lemma36_interval_parameters hL
  have hd : (0 : ℝ) < D := by exact_mod_cast hp.1
  have hc : ContinuousOn (fun t : ℝ => t⁻¹) (Set.Icc ((D : ℝ)^4) ((D : ℝ)^8)) := by
    apply ContinuousOn.inv₀ continuous_id.continuousOn
    intro t ht
    change t ≠ 0
    exact ne_of_gt ((pow_pos hd 4).trans_le ht.1)
  simpa only [one_div] using hc.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self

end ZhangLS.Spec
