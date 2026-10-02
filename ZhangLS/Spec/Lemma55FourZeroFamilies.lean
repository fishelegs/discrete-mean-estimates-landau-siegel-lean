import ZhangLS.Spec.Lemma55CombinedPowerUpperBound
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Fin

/-! # Four tagged actual zero families

Tags retain both functions at both heights, including coincident heights.
The actual orders and inverse squares use the appropriate actual function
and center. The total multiplicity is at most 62 log D.
-/

namespace ZhangLS.Spec
open Complex Finset Metric Set

abbrev Lemma55TaggedZero := Σ _ : Fin 4, ℂ

noncomputable def lemma55ZeroFamily {D : ℕ} (χ : RealPrimitiveCharacter D)
    (t : ℝ) (β : ℂ) (i : Fin 4) : Finset ℂ :=
  ![lemma55ExceptionalRemovedLocalZeros χ 0 β, lemma55ZetaLocalZeroFinset 0,
    lemma55ExceptionalRemovedLocalZeros χ t β, lemma55ZetaLocalZeroFinset t] i

noncomputable def lemma55FamilyHeight (t : ℝ) (i : Fin 4) : ℝ := ![0, 0, t, t] i

noncomputable def lemma55FamilyOrder {D : ℕ} (χ : RealPrimitiveCharacter D)
    (i : Fin 4) (ρ : ℂ) : ℕ :=
  if i = 0 ∨ i = 2 then analyticOrderNatAt (dirichletLFunction χ) ρ
    else analyticOrderNatAt zetaPoleRemoved ρ

noncomputable def lemma55FourZeroFinset {D : ℕ} (χ : RealPrimitiveCharacter D)
    (t : ℝ) (β : ℂ) : Finset Lemma55TaggedZero :=
  univ.sigma (lemma55ZeroFamily χ t β)

noncomputable def lemma55TaggedInverseSquare (t : ℝ) (a : Lemma55TaggedZero) : ℂ :=
  lemma55ZeroInverseSquare (lemma55FamilyHeight t a.1) a.2

lemma lemma55_mem_four_zero_finset {D : ℕ} (χ : RealPrimitiveCharacter D)
    (t : ℝ) (β : ℂ) (a : Lemma55TaggedZero) :
    a ∈ lemma55FourZeroFinset χ t β ↔ a.2 ∈ lemma55ZeroFamily χ t β a.1 := by
  classical
  simp [lemma55FourZeroFinset]

lemma lemma55_actual_zeta_inverse_square_norm_bounds {t : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ lemma55ZetaLocalZeroFinset t) :
    0 < ‖lemma55ZeroInverseSquare t ρ‖ ∧ ‖lemma55ZeroInverseSquare t ρ‖ < 1 := by
  have hm := (lemma55_mem_actual_zeta_local_zero_finset t ρ).mp hρ
  have hR := (lemma55_actual_zeta_pole_removed_zero_iff
    (lemma55_zeta_disk_re_pos (by norm_num) hm.1)).mpr hm.2
  have hre := lemma55_actual_zeta_pole_removed_zero_re_lt_one hR
  have hn := re_le_norm (lemma55JensenCenter t - ρ)
  rw [sub_re, lemma55_jensen_center_re] at hn
  have hd : 1 < ‖lemma55JensenCenter t - ρ‖ := by linarith only [hre, hn]
  have hdp : 0 < ‖lemma55JensenCenter t - ρ‖ := by linarith only [hd]
  have hi : 0 < ‖lemma55JensenCenter t - ρ‖⁻¹ := inv_pos.mpr hdp
  have hi1 : ‖lemma55JensenCenter t - ρ‖⁻¹ < 1 := (inv_lt_one₀ hdp).mpr hd
  unfold lemma55ZeroInverseSquare
  rw [norm_pow, norm_inv]
  exact ⟨by positivity, by nlinarith only [hi, hi1]⟩

lemma lemma55_actual_tagged_zero_order_pos {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) {t : ℝ} {β : ℂ} {a : Lemma55TaggedZero}
    (ha : a ∈ lemma55FourZeroFinset χ t β) :
    1 ≤ lemma55FamilyOrder χ a.1 a.2 := by
  obtain ⟨i, ρ⟩ := a
  have hρ := (lemma55_mem_four_zero_finset χ t β ⟨i, ρ⟩).mp ha
  fin_cases i <;> simp [lemma55ZeroFamily] at hρ
  · change 1 ≤ analyticOrderNatAt (dirichletLFunction χ) ρ
    exact lemma55_actual_local_zero_order_pos χ hD (erase_subset _ _ hρ)
  · change 1 ≤ analyticOrderNatAt zetaPoleRemoved ρ
    exact lemma55_actual_zeta_local_zero_order_pos hρ
  · change 1 ≤ analyticOrderNatAt (dirichletLFunction χ) ρ
    exact lemma55_actual_local_zero_order_pos χ hD (erase_subset _ _ hρ)
  · change 1 ≤ analyticOrderNatAt zetaPoleRemoved ρ
    exact lemma55_actual_zeta_local_zero_order_pos hρ

lemma lemma55_actual_tagged_inverse_square_bounds {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) {t : ℝ} {β : ℂ} {a : Lemma55TaggedZero}
    (ha : a ∈ lemma55FourZeroFinset χ t β) :
    0 < ‖lemma55TaggedInverseSquare t a‖ ∧ ‖lemma55TaggedInverseSquare t a‖ < 1 := by
  obtain ⟨i, ρ⟩ := a
  have hρ := (lemma55_mem_four_zero_finset χ t β ⟨i, ρ⟩).mp ha
  fin_cases i <;> simp [lemma55ZeroFamily] at hρ
  · change 0 < ‖lemma55ZeroInverseSquare 0 ρ‖ ∧ ‖lemma55ZeroInverseSquare 0 ρ‖ < 1
    exact lemma55_actual_inverse_square_norm_bounds χ hD (erase_subset _ _ hρ)
  · change 0 < ‖lemma55ZeroInverseSquare 0 ρ‖ ∧ ‖lemma55ZeroInverseSquare 0 ρ‖ < 1
    exact lemma55_actual_zeta_inverse_square_norm_bounds hρ
  · change 0 < ‖lemma55ZeroInverseSquare t ρ‖ ∧ ‖lemma55ZeroInverseSquare t ρ‖ < 1
    exact lemma55_actual_inverse_square_norm_bounds χ hD (erase_subset _ _ hρ)
  · change 0 < ‖lemma55ZeroInverseSquare t ρ‖ ∧ ‖lemma55ZeroInverseSquare t ρ‖ < 1
    exact lemma55_actual_zeta_inverse_square_norm_bounds hρ

lemma lemma55_removed_zero_order_sum_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 2000 ≤ Real.log (D : ℝ)) {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ)) (β : ℂ) :
    (∑ ρ ∈ lemma55ExceptionalRemovedLocalZeros χ t β,
      (analyticOrderNatAt (dirichletLFunction χ) ρ : ℝ)) ≤ 13 * Real.log (D : ℝ) := by
  calc
    _ ≤ ∑ ρ ∈ lemma55LocalZeroFinset χ t,
        (analyticOrderNatAt (dirichletLFunction χ) ρ : ℝ) :=
      sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (fun _ _ _ => Nat.cast_nonneg _)
    _ = (lemma55LocalMultiplicity χ t : ℝ) := by simp [lemma55LocalMultiplicity]
    _ ≤ _ := lemma55_actual_local_multiplicity_bound χ hD hL ht

lemma lemma55_actual_four_zero_order_sum_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 2000 ≤ Real.log (D : ℝ)) {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ)) (β : ℂ) :
    (∑ a ∈ lemma55FourZeroFinset χ t β, (lemma55FamilyOrder χ a.1 a.2 : ℝ)) ≤
      62 * Real.log (D : ℝ) := by
  classical
  have hχ0 := lemma55_removed_zero_order_sum_bound χ hD hL (by simp : |(0 : ℝ)| ≤ 2 * D) β
  have hχt := lemma55_removed_zero_order_sum_bound χ hD hL ht β
  have hζ0 := lemma55_actual_zeta_local_multiplicity_bound hD hL (by simp : |(0 : ℝ)| ≤ 2 * D)
  have hζt := lemma55_actual_zeta_local_multiplicity_bound hD hL ht
  unfold lemma55FourZeroFinset
  rw [sum_sigma, Fin.sum_univ_four]
  simp [lemma55ZeroFamily, lemma55FamilyOrder]
  unfold lemma55ZetaLocalMultiplicity at hζ0 hζt
  push_cast at hζ0 hζt
  linarith only [hχ0, hχt, hζ0, hζt]

noncomputable def lemma55TaggedZeroPowerSum {D : ℕ} (χ : RealPrimitiveCharacter D)
    (t : ℝ) (β : ℂ) (k : ℕ) : ℂ :=
  ∑ a ∈ lemma55FourZeroFinset χ t β, (lemma55FamilyOrder χ a.1 a.2 : ℂ) /
    (lemma55JensenCenter (lemma55FamilyHeight t a.1) - a.2) ^ k

lemma lemma55_actual_tagged_power_sum_eq {D : ℕ} (χ : RealPrimitiveCharacter D)
    (t : ℝ) (β : ℂ) (k : ℕ) :
    lemma55TaggedZeroPowerSum χ t β k =
      (lemma55SubsetZeroPowerSum χ 0 (lemma55ExceptionalRemovedLocalZeros χ 0 β) k +
        lemma55ZetaLocalZeroPowerSum 0 k) +
      (lemma55SubsetZeroPowerSum χ t (lemma55ExceptionalRemovedLocalZeros χ t β) k +
        lemma55ZetaLocalZeroPowerSum t k) := by
  classical
  unfold lemma55TaggedZeroPowerSum lemma55FourZeroFinset
  rw [sum_sigma, Fin.sum_univ_four]
  simp [lemma55ZeroFamily, lemma55FamilyOrder, lemma55FamilyHeight,
    lemma55SubsetZeroPowerSum, lemma55ZetaLocalZeroPowerSum, add_assoc]

end ZhangLS.Spec
