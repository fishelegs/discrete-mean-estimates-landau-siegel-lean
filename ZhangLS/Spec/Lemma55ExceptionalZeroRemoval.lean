import ZhangLS.Spec.Lemma55ExceptionalPoleComparison

/-!
# Removing the proved simple actual zero from local power sums

The actual nonzero derivative proves multiplicity one. Erasing this zero
subtracts exactly its inverse-power contribution when it is in the local
disk, and subtracts nothing otherwise. The actual remainder budget is
unchanged. Any other original-region zero supplies a nonempty remaining
local set and a maximal normalization radius for the detection theorem.
-/

namespace ZhangLS.Spec

open Complex Finset

theorem lemma55_actual_simple_zero_order_nat
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) {β : ℂ}
    (hzero : dirichletLFunction χ β = 0) (hderiv : deriv (dirichletLFunction χ) β ≠ 0) :
    analyticOrderNatAt (dirichletLFunction χ) β = 1 := by
  have ha := lemma55_actual_L_analyticOnNhd χ hD β (Set.mem_univ β)
  have ho := ha.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hzero hderiv
  unfold analyticOrderNatAt
  rw [ho]
  rfl

noncomputable def lemma55ExceptionalRemovedLocalZeros {D : ℕ}
    (χ : RealPrimitiveCharacter D) (t : ℝ) (β : ℂ) : Finset ℂ := by
  classical
  exact (lemma55LocalZeroFinset χ t).erase β

theorem lemma55_actual_simple_zero_removed_power_sum
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) (t : ℝ) {β : ℂ}
    (hzero : dirichletLFunction χ β = 0) (hderiv : deriv (dirichletLFunction χ) β ≠ 0) (k : ℕ) :
    lemma55SubsetZeroPowerSum χ t (lemma55ExceptionalRemovedLocalZeros χ t β) k =
      lemma55LocalZeroPowerSum χ t k -
        (if β ∈ lemma55LocalZeroFinset χ t then 1 / (lemma55JensenCenter t - β) ^ k else 0) := by
  classical
  have ho := lemma55_actual_simple_zero_order_nat χ hD hzero hderiv
  unfold lemma55SubsetZeroPowerSum lemma55ExceptionalRemovedLocalZeros lemma55LocalZeroPowerSum
  by_cases hβ : β ∈ lemma55LocalZeroFinset χ t
  · rw [if_pos hβ, sum_erase_eq_sub hβ, ho, Nat.cast_one]
  · rw [if_neg hβ, erase_eq_of_notMem hβ, sub_zero]

noncomputable def lemma55RemovedNormalizedLogDerivative {D : ℕ}
    (χ : RealPrimitiveCharacter D) (t : ℝ) (β : ℂ) (n : ℕ) : ℂ :=
  lemma55NormalizedLogDerivative χ t n -
    (if β ∈ lemma55LocalZeroFinset χ t then
      1 / (lemma55JensenCenter t - β) ^ (n + 1) else 0)

theorem lemma55_actual_removed_power_remainder_eq
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) (t : ℝ) {β : ℂ}
    (hzero : dirichletLFunction χ β = 0) (hderiv : deriv (dirichletLFunction χ) β ≠ 0) (n : ℕ) :
    lemma55RemovedNormalizedLogDerivative χ t β n -
      lemma55SubsetZeroPowerSum χ t (lemma55ExceptionalRemovedLocalZeros χ t β) (n + 1) =
        lemma55NormalizedLogDerivative χ t n - lemma55LocalZeroPowerSum χ t (n + 1) := by
  rw [lemma55_actual_simple_zero_removed_power_sum χ hD t hzero hderiv]
  unfold lemma55RemovedNormalizedLogDerivative
  ring

theorem lemma55_actual_removed_power_remainder_sum_bound
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ)) {β : ℂ}
    (hzero : dirichletLFunction χ β = 0) (hderiv : deriv (dirichletLFunction χ) β ≠ 0)
    (I : Finset ℕ) :
    (∑ n ∈ I, ‖lemma55RemovedNormalizedLogDerivative χ t β n -
      lemma55SubsetZeroPowerSum χ t (lemma55ExceptionalRemovedLocalZeros χ t β) (n + 1)‖) ≤
        71280 * Real.log (D : ℝ) := by
  simp_rw [lemma55_actual_removed_power_remainder_eq χ hD t hzero hderiv]
  exact lemma55_actual_power_sum_remainder_sum_bound χ hD hL ht I

theorem lemma55_original_other_zero_remaining_normalization
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) {ρ β : ℂ}
    (hregion : Lemma55InZeroRegion D ρ) (hzero : dirichletLFunction χ ρ = 0) (hne : ρ ≠ β) :
    ∃ ρ₀ ∈ lemma55ExceptionalRemovedLocalZeros χ ρ.im β,
      0 < ‖lemma55ZeroInverseSquare ρ.im ρ₀‖ ∧
      ‖lemma55ZeroInverseSquare ρ.im ρ₀‖ < 1 ∧
      ((1 + 2 / Real.log (D : ℝ))⁻¹) ^ 2 ≤ ‖lemma55ZeroInverseSquare ρ.im ρ₀‖ ∧
      ∀ σ ∈ lemma55ExceptionalRemovedLocalZeros χ ρ.im β,
        ‖lemma55ZeroInverseSquare ρ.im σ‖ ≤ ‖lemma55ZeroInverseSquare ρ.im ρ₀‖ := by
  classical
  apply lemma55_original_candidate_subset_normalization χ hD hL hregion hzero
  · exact erase_subset _ _
  · apply mem_erase.mpr
    exact ⟨hne, lemma55_original_zero_in_own_local_disk χ hD hL hregion hzero⟩

noncomputable def lemma55WeightedRemainingZeroPowerSum {D : ℕ}
    (χ : RealPrimitiveCharacter D) (t r : ℝ) (β v : ℂ) (J : ℕ) : ℂ :=
  ∑ j ∈ range J, (lemma55FejerDetectionWeight v J j : ℂ) *
    lemma55SubsetZeroPowerSum χ t (lemma55ExceptionalRemovedLocalZeros χ t β) (2 * (j + 1)) /
      (r : ℂ) ^ (j + 1)

noncomputable def lemma55WeightedRemovedLogDerivative {D : ℕ}
    (χ : RealPrimitiveCharacter D) (t r : ℝ) (β v : ℂ) (J : ℕ) : ℂ :=
  ∑ j ∈ range J, (lemma55FejerDetectionWeight v J j : ℂ) *
    lemma55RemovedNormalizedLogDerivative χ t β (2 * j + 1) / (r : ℂ) ^ (j + 1)

theorem lemma55_actual_weighted_remaining_remainder_eq
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) (t r : ℝ) {β : ℂ}
    (hzero : dirichletLFunction χ β = 0) (hderiv : deriv (dirichletLFunction χ) β ≠ 0)
    (v : ℂ) (J : ℕ) :
    lemma55WeightedRemovedLogDerivative χ t r β v J -
      lemma55WeightedRemainingZeroPowerSum χ t r β v J =
        lemma55WeightedLogDerivative χ t r v J - lemma55WeightedZeroPowerSum χ t r v J := by
  unfold lemma55WeightedRemovedLogDerivative lemma55WeightedRemainingZeroPowerSum
    lemma55WeightedLogDerivative lemma55WeightedZeroPowerSum
  rw [← sum_sub_distrib, ← sum_sub_distrib]
  apply sum_congr rfl
  intro j _
  have hp := lemma55_actual_removed_power_remainder_eq χ hD t hzero hderiv (2 * j + 1)
  have hn : 2 * j + 1 + 1 = 2 * (j + 1) := by omega
  rw [hn] at hp
  rw [← sub_div, ← mul_sub, ← sub_div, ← mul_sub, hp]

theorem lemma55_actual_weighted_remaining_error_uniform_bound
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ))
    {r : ℝ} (hr : 0 < r) (hlower : ((1 + 2 / Real.log (D : ℝ))⁻¹) ^ 2 ≤ r)
    {β v : ℂ} (hzero : dirichletLFunction χ β = 0)
    (hderiv : deriv (dirichletLFunction χ) β ≠ 0) (hv : ‖v‖ ≤ 1) (J : ℕ) :
    ‖lemma55WeightedRemovedLogDerivative χ t r β v J -
      lemma55WeightedRemainingZeroPowerSum χ t r β v J‖ ≤ 79200 * Real.log (D : ℝ) := by
  rw [lemma55_actual_weighted_remaining_remainder_eq χ hD t r hzero hderiv v J]
  exact lemma55_actual_weighted_power_error_uniform_bound χ hD hL ht hr hlower hv J

theorem lemma55_actual_weighted_remaining_detection
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ)) {β ρ₀ : ℂ}
    (hρ₀ : ρ₀ ∈ lemma55ExceptionalRemovedLocalZeros χ t β)
    (hmax : ∀ σ ∈ lemma55ExceptionalRemovedLocalZeros χ t β,
      ‖lemma55ZeroInverseSquare t σ‖ ≤ ‖lemma55ZeroInverseSquare t ρ₀‖) (J : ℕ) :
    (J : ℝ) / 4 - 13 * Real.log (D : ℝ) ≤
      (lemma55WeightedRemainingZeroPowerSum χ t ‖lemma55ZeroInverseSquare t ρ₀‖ β
        (lemma55ZeroInverseSquare t ρ₀ / (‖lemma55ZeroInverseSquare t ρ₀‖ : ℂ))⁻¹ J).re := by
  classical
  have hd := lemma55_actual_subset_weighted_detection_log_bound χ hD hL ht
    (lemma55ExceptionalRemovedLocalZeros χ t β) (erase_subset _ _) hρ₀ hmax J
  apply hd.trans_eq
  unfold lemma55WeightedRemainingZeroPowerSum
  rw [Complex.re_sum]
  apply sum_congr rfl
  intro j _
  have he (w : ℝ) (a b : ℂ) : (w : ℂ) * a / b = (w : ℂ) * (a / b) := by ring
  rw [he]
  simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]

theorem lemma55_original_other_zero_detected
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) {ρ β : ℂ}
    (hregion : Lemma55InZeroRegion D ρ) (hzero : dirichletLFunction χ ρ = 0) (hne : ρ ≠ β) :
    ∃ ρ₀ ∈ lemma55ExceptionalRemovedLocalZeros χ ρ.im β,
      0 < ‖lemma55ZeroInverseSquare ρ.im ρ₀‖ ∧
      ‖lemma55ZeroInverseSquare ρ.im ρ₀‖ < 1 ∧
      ((1 + 2 / Real.log (D : ℝ))⁻¹) ^ 2 ≤ ‖lemma55ZeroInverseSquare ρ.im ρ₀‖ ∧
      ∀ J : ℕ, (J : ℝ) / 4 - 13 * Real.log (D : ℝ) ≤
        (lemma55WeightedRemainingZeroPowerSum χ ρ.im ‖lemma55ZeroInverseSquare ρ.im ρ₀‖ β
          (lemma55ZeroInverseSquare ρ.im ρ₀ / (‖lemma55ZeroInverseSquare ρ.im ρ₀‖ : ℂ))⁻¹ J).re := by
  obtain ⟨ρ₀, hρ₀, hrp, hr1, hrlo, hmax⟩ :=
    lemma55_original_other_zero_remaining_normalization χ hD hL hregion hzero hne
  exact ⟨ρ₀, hρ₀, hrp, hr1, hrlo, fun J =>
    lemma55_actual_weighted_remaining_detection χ hD hL hregion.2.le hρ₀ hmax J⟩

end ZhangLS.Spec
