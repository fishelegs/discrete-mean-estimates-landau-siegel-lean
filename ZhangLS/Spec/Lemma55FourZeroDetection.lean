import ZhangLS.Spec.Lemma55FourZeroFamilies

/-! # Common-maximum detection across the four actual zero families

Every proposed other zero in the entire original region gives a member
of the tagged family. A maximum over all four families normalizes every
term to the closed unit disk. Actual multiplicities and the Fejér kernel
then give J/4−62 log D for every detection degree.
-/

namespace ZhangLS.Spec
open Complex Finset

lemma lemma55_tagged_normalized_power_sum {D : ℕ} (χ : RealPrimitiveCharacter D)
    (t r : ℝ) (β : ℂ) (k : ℕ) :
    (∑ a ∈ lemma55FourZeroFinset χ t β, (lemma55FamilyOrder χ a.1 a.2 : ℝ) *
      ((lemma55TaggedInverseSquare t a / (r : ℂ)) ^ k).re) =
        (lemma55TaggedZeroPowerSum χ t β (2 * k) / (r : ℂ) ^ k).re := by
  unfold lemma55TaggedZeroPowerSum lemma55TaggedInverseSquare lemma55ZeroInverseSquare
  rw [sum_div, Complex.re_sum]
  apply sum_congr rfl
  intro a _
  rw [div_pow, ← pow_mul, inv_pow]
  have he : ((lemma55FamilyOrder χ a.1 a.2 : ℂ) /
      (lemma55JensenCenter (lemma55FamilyHeight t a.1) - a.2) ^ (2 * k)) / (r : ℂ) ^ k =
        (lemma55FamilyOrder χ a.1 a.2 : ℂ) *
          (((lemma55JensenCenter (lemma55FamilyHeight t a.1) - a.2) ^ (2 * k))⁻¹ / (r : ℂ) ^ k) := by ring
  rw [he]
  simp only [mul_re, natCast_re, natCast_im, zero_mul, sub_zero]

lemma lemma55_actual_weighted_tagged_power_sum_eq {D : ℕ} (χ : RealPrimitiveCharacter D)
    (t r : ℝ) (β v : ℂ) (J : ℕ) :
    (∑ j ∈ range J, (lemma55FejerDetectionWeight v J j : ℂ) *
      lemma55TaggedZeroPowerSum χ t β (2 * (j + 1)) / (r : ℂ) ^ (j + 1)) =
        lemma55CombinedRemainingPower χ t r β v J := by
  simp_rw [lemma55_actual_tagged_power_sum_eq]
  unfold lemma55CombinedRemainingPower lemma55WeightedRemainingZeroPowerSum lemma55ZetaWeightedZeroPowerSum
  simp only [mul_add, add_div, sum_add_distrib]

lemma lemma55_actual_weighted_tagged_real_sum_eq {D : ℕ} (χ : RealPrimitiveCharacter D)
    (t r : ℝ) (β v : ℂ) (J : ℕ) :
    (∑ j ∈ range J, lemma55FejerDetectionWeight v J j *
      (lemma55TaggedZeroPowerSum χ t β (2 * (j + 1)) / (r : ℂ) ^ (j + 1)).re) =
        (lemma55CombinedRemainingPower χ t r β v J).re := by
  rw [← lemma55_actual_weighted_tagged_power_sum_eq, Complex.re_sum]
  apply sum_congr rfl
  intro j _
  have he : (lemma55FejerDetectionWeight v J j : ℂ) *
      lemma55TaggedZeroPowerSum χ t β (2 * (j + 1)) / (r : ℂ) ^ (j + 1) =
        (lemma55FejerDetectionWeight v J j : ℂ) *
          (lemma55TaggedZeroPowerSum χ t β (2 * (j + 1)) / (r : ℂ) ^ (j + 1)) := by ring
  rw [he]
  simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]

lemma lemma55_original_other_zero_in_four_families {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 2000 ≤ Real.log (D : ℝ)) {ρ β : ℂ}
    (hregion : Lemma55InZeroRegion D ρ) (hzero : dirichletLFunction χ ρ = 0) (hne : ρ ≠ β) :
    (⟨2, ρ⟩ : Lemma55TaggedZero) ∈ lemma55FourZeroFinset χ ρ.im β := by
  classical
  have hρ := lemma55_original_zero_in_own_local_disk χ hD hL hregion hzero
  apply (lemma55_mem_four_zero_finset χ ρ.im β ⟨2, ρ⟩).mpr
  simpa [lemma55ZeroFamily, lemma55ExceptionalRemovedLocalZeros, hne] using hρ

lemma lemma55_actual_common_maximum_weighted_detection {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 2000 ≤ Real.log (D : ℝ)) {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ))
    {β : ℂ} {a₀ : Lemma55TaggedZero} (ha₀ : a₀ ∈ lemma55FourZeroFinset χ t β)
    (hmax : ∀ a ∈ lemma55FourZeroFinset χ t β,
      ‖lemma55TaggedInverseSquare t a‖ ≤ ‖lemma55TaggedInverseSquare t a₀‖) (J : ℕ) :
    (J : ℝ) / 4 - 62 * Real.log (D : ℝ) ≤
      (lemma55CombinedRemainingPower χ t ‖lemma55TaggedInverseSquare t a₀‖ β
        (lemma55TaggedInverseSquare t a₀ / (‖lemma55TaggedInverseSquare t a₀‖ : ℂ))⁻¹ J).re := by
  have hr := (lemma55_actual_tagged_inverse_square_bounds χ hD ha₀).1
  have hnorm : ∀ a ∈ lemma55FourZeroFinset χ t β,
      ‖lemma55TaggedInverseSquare t a / (‖lemma55TaggedInverseSquare t a₀‖ : ℂ)‖ ≤ 1 := by
    intro a ha
    rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hr]
    exact (div_le_iff₀ hr).mpr (by simpa only [one_mul] using hmax a ha)
  have hunit : ‖lemma55TaggedInverseSquare t a₀ / (‖lemma55TaggedInverseSquare t a₀‖ : ℂ)‖ = 1 := by
    rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hr, div_self hr.ne']
  have hm : 1 ≤ (lemma55FamilyOrder χ a₀.1 a₀.2 : ℝ) := by
    exact_mod_cast lemma55_actual_tagged_zero_order_pos χ hD ha₀
  have hd := lemma55_fejer_finite_weighted_power_detection (lemma55FourZeroFinset χ t β)
    (fun a => (lemma55FamilyOrder χ a.1 a.2 : ℝ))
    (fun a => lemma55TaggedInverseSquare t a / (‖lemma55TaggedInverseSquare t a₀‖ : ℂ))
    ha₀ (fun _ _ => Nat.cast_nonneg _) hm hnorm hunit J
  simp only [lemma55_tagged_normalized_power_sum] at hd
  rw [lemma55_actual_weighted_tagged_real_sum_eq] at hd
  have hN := lemma55_actual_four_zero_order_sum_bound χ hD hL ht β
  linarith only [hd, hN]

lemma lemma55_original_other_zero_four_detected {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 2000 ≤ Real.log (D : ℝ)) {ρ β : ℂ}
    (hregion : Lemma55InZeroRegion D ρ) (hzero : dirichletLFunction χ ρ = 0) (hne : ρ ≠ β) :
    ∃ a₀ ∈ lemma55FourZeroFinset χ ρ.im β,
      0 < ‖lemma55TaggedInverseSquare ρ.im a₀‖ ∧ ‖lemma55TaggedInverseSquare ρ.im a₀‖ < 1 ∧
      ((1 + 2 / Real.log (D : ℝ))⁻¹) ^ 2 ≤ ‖lemma55TaggedInverseSquare ρ.im a₀‖ ∧
      ∀ J : ℕ, (J : ℝ) / 4 - 62 * Real.log (D : ℝ) ≤
        (lemma55CombinedRemainingPower χ ρ.im ‖lemma55TaggedInverseSquare ρ.im a₀‖ β
          (lemma55TaggedInverseSquare ρ.im a₀ / (‖lemma55TaggedInverseSquare ρ.im a₀‖ : ℂ))⁻¹ J).re := by
  have hρ := lemma55_original_other_zero_in_four_families χ hD hL hregion hzero hne
  obtain ⟨a₀, ha₀, hmax⟩ := (lemma55FourZeroFinset χ ρ.im β).exists_max_image
    (fun a => ‖lemma55TaggedInverseSquare ρ.im a‖) ⟨⟨2, ρ⟩, hρ⟩
  have hb := lemma55_actual_tagged_inverse_square_bounds χ hD ha₀
  have hlower := (lemma55_original_zero_inverse_square_lower_bound χ hD hL hregion hzero).trans
    (by simpa [lemma55TaggedInverseSquare, lemma55FamilyHeight] using hmax ⟨2, ρ⟩ hρ)
  exact ⟨a₀, ha₀, hb.1, hb.2, hlower, fun J =>
    lemma55_actual_common_maximum_weighted_detection χ hD hL hregion.2.le ha₀ hmax J⟩

end ZhangLS.Spec
