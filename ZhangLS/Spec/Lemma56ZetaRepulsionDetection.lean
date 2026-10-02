import ZhangLS.Spec.Lemma55FullZeroExclusion


set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Metric Set MeasureTheory Finset
open scoped Real
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

lemma lemma56_actual_zeta_zero_own_disk {L : ℝ} (hL : 2000 ≤ L) {ρ : ℂ}
    (hre : 1 - 2 / L < ρ.re) (hzero : zetaPoleRemoved ρ = 0) :
    ρ ∈ lemma55ZetaLocalZeroFinset ρ.im := by
  have hr := lemma55_actual_zeta_pole_removed_zero_re_lt_one hzero
  have hLp : 0 < L := by linarith only [hL]
  have hinv : 2 / L ≤ (1 : ℝ) / 1000 := by
    apply (div_le_iff₀ hLp).mpr
    linarith only [hL]
  have hp : 0 < ρ.re := by linarith only [hre, hinv]
  apply (lemma55_mem_actual_zeta_local_zero_finset ρ.im ρ).mpr
  refine ⟨?_, (lemma55_actual_zeta_pole_removed_zero_iff hp).mp hzero⟩
  rw [mem_closedBall_iff_norm, norm_sub_rev, lemma55_jensen_center_at_zero_height,
    norm_real, Real.norm_eq_abs, abs_of_pos (by linarith only [hr] : 0 < 2 - ρ.re)]
  linarith only [hre, hinv]

lemma lemma56_actual_zeta_inverse_square_lower {L : ℝ} (hL : 2000 ≤ L) {ρ : ℂ}
    (hre : 1 - 2 / L < ρ.re) (hzero : zetaPoleRemoved ρ = 0) :
    ((1 + 2 / L)⁻¹) ^ 2 ≤ ‖lemma55ZeroInverseSquare ρ.im ρ‖ := by
  have hr := lemma55_actual_zeta_pole_removed_zero_re_lt_one hzero
  have hLp : 0 < L := by linarith only [hL]
  have hd : 0 < 2 - ρ.re := by linarith only [hr]
  have ha : 2 - ρ.re ≤ 1 + 2 / L := by linarith only [hre]
  have hi : (1 + 2 / L)⁻¹ ≤ (2 - ρ.re)⁻¹ :=
    (inv_le_inv₀ (by positivity : 0 < 1 + 2 / L) hd).mpr ha
  unfold lemma55ZeroInverseSquare
  rw [norm_pow, norm_inv, lemma55_jensen_center_at_zero_height,
    norm_real, Real.norm_eq_abs, abs_of_pos hd]
  exact pow_le_pow_left₀ (by positivity) hi 2

lemma lemma56_actual_zeta_zero_four_detected {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 2000 ≤ Real.log (D : ℝ)) {ρ β : ℂ}
    (hre : 1 - 2 / Real.log (D : ℝ) < ρ.re) (ht : |ρ.im| ≤ 2 * (D : ℝ))
    (hzero : zetaPoleRemoved ρ = 0) :
    ∃ a₀ ∈ lemma55FourZeroFinset χ ρ.im β,
      0 < ‖lemma55TaggedInverseSquare ρ.im a₀‖ ∧ ‖lemma55TaggedInverseSquare ρ.im a₀‖ < 1 ∧
      ((1 + 2 / Real.log (D : ℝ))⁻¹) ^ 2 ≤ ‖lemma55TaggedInverseSquare ρ.im a₀‖ ∧
      ∀ J : ℕ, (J : ℝ) / 4 - 62 * Real.log (D : ℝ) ≤
        (lemma55CombinedRemainingPower χ ρ.im ‖lemma55TaggedInverseSquare ρ.im a₀‖ β
          (lemma55TaggedInverseSquare ρ.im a₀ / (‖lemma55TaggedInverseSquare ρ.im a₀‖ : ℂ))⁻¹ J).re := by
  have hlocal := lemma56_actual_zeta_zero_own_disk hL hre hzero
  have hρ : (⟨3, ρ⟩ : Lemma55TaggedZero) ∈ lemma55FourZeroFinset χ ρ.im β := by
    apply (lemma55_mem_four_zero_finset χ ρ.im β ⟨3, ρ⟩).mpr
    simpa [lemma55ZeroFamily] using hlocal
  obtain ⟨a₀, ha₀, hmax⟩ := (lemma55FourZeroFinset χ ρ.im β).exists_max_image
    (fun a => ‖lemma55TaggedInverseSquare ρ.im a‖) ⟨⟨3, ρ⟩, hρ⟩
  have hb := lemma55_actual_tagged_inverse_square_bounds χ hD ha₀
  have hlower := (lemma56_actual_zeta_inverse_square_lower hL hre hzero).trans
    (by simpa [lemma55TaggedInverseSquare, lemma55FamilyHeight] using hmax ⟨3, ρ⟩ hρ)
  exact ⟨a₀, ha₀, hb.1, hb.2, hlower, fun J =>
    lemma55_actual_common_maximum_weighted_detection χ hD hL ht ha₀ hmax J⟩

end ZhangLS.Spec
