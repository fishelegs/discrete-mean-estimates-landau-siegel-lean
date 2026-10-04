import ZhangLS.Spec.CoprimeProfileAbelBound
import Mathlib.NumberTheory.AbelSummation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

set_option autoImplicit false
namespace ZhangLS.Spec.CoprimeProfileAbel
open Finset MeasureTheory Set
open scoped Classical
set_option maxHeartbeats 2000000

lemma summatory_zero_start (D : ℕ) (x : ℝ) :
    (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, coefficient D n) = summatory D x := by
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons, coefficient_zero, zero_add]
  rw [← Finset.Icc_add_one_left_eq_Ioc]
  simp [summatory]

/-- Actual Abel identity with strict lower and inclusive upper integer endpoints. -/
theorem finite_abel (D : ℕ) {L R : ℝ} (hL : 0 ≤ L) (hLR : L ≤ R)
    (f f' : ℝ → ℝ) (hf : ∀ t ∈ Set.Icc L R, HasDerivAt f (f' t) t)
    (hf' : ContinuousOn f' (Set.Icc L R)) :
    (∑ n ∈ Finset.Ioc ⌊L⌋₊ ⌊R⌋₊, f n * coefficient D n) =
      f R * summatory D R - f L * summatory D L -
        ∫ t in L..R, f' t * summatory D t := by
  have hd : ∀ t ∈ Set.Icc L R, DifferentiableAt ℝ f t := fun t ht => (hf t ht).differentiableAt
  have hint : IntegrableOn (deriv f) (Set.Icc L R) :=
    hf'.integrableOn_Icc.congr_fun (fun t ht => (hf t ht).deriv.symm) measurableSet_Icc
  have h := sum_mul_eq_sub_sub_integral_mul (coefficient D) hL hLR hd hint
  simp_rw [summatory_zero_start] at h
  rw [← intervalIntegral.integral_of_le hLR] at h
  convert h using 1
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [(hf t ((Set.uIcc_of_le hLR) ▸ ht)).deriv]

lemma summatory_product_integrable (D : ℕ) {L R : ℝ} (hL : 0 ≤ L) (hLR : L ≤ R)
    {g : ℝ → ℝ} (hg : ContinuousOn g (Set.Icc L R)) :
    IntervalIntegrable (fun t => g t * summatory D t) volume L R := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hLR).mpr
  have h := integrableOn_mul_sum_Icc (coefficient D) hL (m := 0) hg.integrableOn_Icc
  simpa only [summatory_zero_start] using h

/-- Remainder identity after the actual arithmetic main term is removed. -/
theorem abel_remainder_identity (D : ℕ) {L R : ℝ} (hL : 0 ≤ L) (hLR : L ≤ R)
    (f f' : ℝ → ℝ) (hf : ∀ t ∈ Set.Icc L R, HasDerivAt f (f' t) t)
    (hf' : ContinuousOn f' (Set.Icc L R)) (hfL : f L = 0) (hfR : f R = 0) :
    (∑ n ∈ Finset.Ioc ⌊L⌋₊ ⌊R⌋₊, f n * coefficient D n) -
      mainConstant D * (∫ t in L..R, f t) =
      -(∫ t in L..R, f' t * (summatory D t - mainConstant D * t)) := by
  have hS := summatory_product_integrable D hL hLR hf'
  have hC : IntervalIntegrable (fun t => f' t * (mainConstant D * t)) volume L R :=
    (hf'.mul (continuous_const.mul continuous_id).continuousOn).intervalIntegrable_of_Icc hLR
  have he : (∫ t in L..R, f' t * (summatory D t - mainConstant D * t)) =
      (∫ t in L..R, f' t * summatory D t) -
        (∫ t in L..R, f' t * (mainConstant D * t)) := by
    simp_rw [mul_sub]
    exact intervalIntegral.integral_sub hS hC
  have hb := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := f) (u' := f') (v := fun t : ℝ => t) (v' := fun _ => (1 : ℝ))
    (fun t ht => hf t ((Set.uIcc_of_le hLR) ▸ ht)) (fun t _ => hasDerivAt_id t)
    (hf'.intervalIntegrable_of_Icc hLR) (intervalIntegrable_const)
  simp only [mul_one, hfL, hfR, zero_mul, sub_zero, zero_sub] at hb
  have hmain : (∫ t in L..R, f' t * (mainConstant D * t)) =
      -(mainConstant D * (∫ t in L..R, f t)) := by
    have hc : (fun t => f' t * (mainConstant D * t)) =
        (fun t => mainConstant D * (f' t * t)) := by funext t; ring
    rw [hc, intervalIntegral.integral_const_mul, hb]
    ring
  rw [finite_abel D hL hLR f f' hf hf', hfL, hfR, zero_mul, zero_mul,
    sub_zero, zero_sub, he, hmain]
  ring

/-- Explicit outer-sum error for a differentiable weight with an actual
reciprocal-square derivative envelope; the summatory input is proved above. -/
theorem abel_remainder_bound {D : ℕ} (hD : 0 < D) {L R W : ℝ}
    (hL : 1 ≤ L) (hLR : L ≤ R) (hW : 0 ≤ W)
    (f f' : ℝ → ℝ) (hf : ∀ t ∈ Set.Icc L R, HasDerivAt f (f' t) t)
    (hf' : ContinuousOn f' (Set.Icc L R)) (hfL : f L = 0) (hfR : f R = 0)
    (hbound : ∀ t ∈ Set.Icc L R, |f' t| ≤ W / t ^ 2) :
    |(∑ n ∈ Finset.Ioc ⌊L⌋₊ ⌊R⌋₊, f n * coefficient D n) -
      mainConstant D * (∫ t in L..R, f t)| ≤
      ((D.divisors.card : ℝ) * (1 + Real.log R) + 2) * W / L := by
  let Q : ℝ := (D.divisors.card : ℝ) * (1 + Real.log R) + 2
  have hLp : 0 < L := by linarith
  have hRp : 0 < R := hLp.trans_le hLR
  have hQ : 0 ≤ Q := by
    have hlog := Real.log_nonneg (hL.trans hLR)
    dsimp [Q]
    positivity
  have hg : ContinuousOn (fun t : ℝ => Q * W * (t ^ 2)⁻¹) (Set.Icc L R) := by
    apply ContinuousOn.mul continuous_const.continuousOn
    apply ContinuousOn.inv₀ (continuous_id.pow 2).continuousOn
    intro t ht
    exact pow_ne_zero 2 (by dsimp at *; linarith [ht.1])
  have hint := intervalIntegral.norm_integral_le_of_norm_le hLR
    (f := fun t => f' t * (summatory D t - mainConstant D * t))
    (g := fun t => Q * W * (t ^ 2)⁻¹) (μ := volume)
    (Filter.Eventually.of_forall (fun t ht => by
      have htc : t ∈ Set.Icc L R := ⟨ht.1.le, ht.2⟩
      have ht1 : 1 ≤ t := hL.trans htc.1
      have htpos : 0 < t := by linarith
      have he := summatory_error hD ht1
      have hlog : Real.log t ≤ Real.log R := Real.log_le_log htpos htc.2
      have heQ : |summatory D t - mainConstant D * t| ≤ Q := by
        apply he.trans
        dsimp [Q]
        gcongr
      rw [Real.norm_eq_abs, abs_mul]
      calc
        _ ≤ (W / t ^ 2) * Q := mul_le_mul (hbound t htc) heQ (abs_nonneg _) (by positivity)
        _ = _ := by simp only [div_eq_mul_inv]; ring))
    (hg.intervalIntegrable_of_Icc hLR)
  have hi : (∫ t in L..R, (t ^ 2)⁻¹) = L⁻¹ - R⁻¹ := by
    have hd : ∀ t ∈ Set.uIcc L R, HasDerivAt (fun u : ℝ => -u⁻¹) ((t ^ 2)⁻¹) t := by
      intro t ht
      have htne : t ≠ 0 := by rw [Set.uIcc_of_le hLR] at ht; linarith [ht.1]
      simpa using (hasDerivAt_inv htne).neg
    have hc : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.Icc L R) := by
      apply ContinuousOn.inv₀ (continuous_id.pow 2).continuousOn
      intro t ht
      exact pow_ne_zero 2 (by dsimp at *; linarith [ht.1])
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable_of_Icc hLR)
    simpa only [neg_sub_neg] using he
  rw [intervalIntegral.integral_const_mul, hi] at hint
  rw [abel_remainder_identity D (by linarith) hLR f f' hf hf' hfL hfR, abs_neg]
  have hb : Q * W * (L⁻¹ - R⁻¹) ≤ Q * W / L := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (sub_le_self _ (by positivity)) (mul_nonneg hQ hW)
  have hfinal : |∫ t in L..R, f' t * (summatory D t - mainConstant D * t)| ≤
      Q * W * (L⁻¹ - R⁻¹) := by simpa only [Real.norm_eq_abs] using hint
  exact hfinal.trans hb

end ZhangLS.Spec.CoprimeProfileAbel
