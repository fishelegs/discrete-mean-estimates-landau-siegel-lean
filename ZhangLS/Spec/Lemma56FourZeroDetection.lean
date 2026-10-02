import ZhangLS.Spec.Lemma56FourZeroFamilies

/-! # Common-maximum detection for the actual mixed zero families -/

namespace ZhangLS.Spec
open Complex Finset
open scoped Real
set_option maxHeartbeats 1000000

lemma lemma56_tagged_normalized_power_sum {D q : ℕ} [NeZero q]
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ q)
    (t R : ℝ) (β : ℂ) (k : ℕ) :
    (∑ a ∈ lemma56FourZeroFinset χ θ t β, (lemma56FamilyOrder χ θ a.1 a.2 : ℝ) *
      ((lemma56TaggedInverseSquare t a / (R : ℂ)) ^ k).re) =
        (lemma56TaggedZeroPowerSum χ θ t β (2 * k) / (R : ℂ) ^ k).re := by
  unfold lemma56TaggedZeroPowerSum lemma56TaggedInverseSquare lemma55ZeroInverseSquare
  rw [sum_div, Complex.re_sum]
  apply sum_congr rfl
  intro a _
  rw [div_pow, ← pow_mul, inv_pow]
  have he : ((lemma56FamilyOrder χ θ a.1 a.2 : ℂ) /
      (lemma55JensenCenter (lemma55FamilyHeight t a.1) - a.2) ^ (2 * k)) / (R : ℂ) ^ k =
        (lemma56FamilyOrder χ θ a.1 a.2 : ℂ) *
          (((lemma55JensenCenter (lemma55FamilyHeight t a.1) - a.2) ^ (2 * k))⁻¹ / (R : ℂ) ^ k) := by ring
  rw [he]
  simp only [mul_re, natCast_re, natCast_im, zero_mul, sub_zero]

lemma lemma56_actual_weighted_tagged_power_sum_eq {D q : ℕ} [NeZero q]
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ q)
    (t R : ℝ) (β v : ℂ) (J : ℕ) :
    (∑ j ∈ range J, (lemma55FejerDetectionWeight v J j : ℂ) *
      lemma56TaggedZeroPowerSum χ θ t β (2 * (j + 1)) / (R : ℂ) ^ (j + 1)) =
        lemma56MixedRemainingPower χ θ t R β v J := by
  letI : NeZero (D * q) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne q)⟩
  simp_rw [lemma56_actual_tagged_power_sum_eq]
  unfold lemma56MixedRemainingPower lemma55WeightedRemainingZeroPowerSum
    lemma55ZetaWeightedZeroPowerSum lemma56WeightedZeroPowerSum
  simp only [mul_add, add_div, sum_add_distrib]

lemma lemma56_actual_weighted_tagged_real_sum_eq {D q : ℕ} [NeZero q]
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ q)
    (t R : ℝ) (β v : ℂ) (J : ℕ) :
    (∑ j ∈ range J, lemma55FejerDetectionWeight v J j *
      (lemma56TaggedZeroPowerSum χ θ t β (2 * (j + 1)) / (R : ℂ) ^ (j + 1)).re) =
        (lemma56MixedRemainingPower χ θ t R β v J).re := by
  rw [← lemma56_actual_weighted_tagged_power_sum_eq, Complex.re_sum]
  apply sum_congr rfl
  intro j _
  have he : (lemma55FejerDetectionWeight v J j : ℂ) *
      lemma56TaggedZeroPowerSum χ θ t β (2 * (j + 1)) / (R : ℂ) ^ (j + 1) =
        (lemma55FejerDetectionWeight v J j : ℂ) *
          (lemma56TaggedZeroPowerSum χ θ t β (2 * (j + 1)) / (R : ℂ) ^ (j + 1)) := by ring
  rw [he]
  simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]

lemma lemma56_actual_common_maximum_weighted_detection {D q : ℕ} [NeZero q]
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ q)
    (hD : 1 < D) (hL : 2000 ≤ lemma23PaperL D) (hq : (q : ℝ) < lemma56PaperT D)
    (hθ : θ ≠ 1) (htwist : lemma44CharacterTwist χ θ ≠ 1)
    {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ)) {β : ℂ} {a₀ : Lemma56TaggedZero}
    (ha₀ : a₀ ∈ lemma56FourZeroFinset χ θ t β)
    (hmax : ∀ a ∈ lemma56FourZeroFinset χ θ t β,
      ‖lemma56TaggedInverseSquare t a‖ ≤ ‖lemma56TaggedInverseSquare t a₀‖) (J : ℕ) :
    (J : ℝ) / 4 - 79 * lemma23PaperL D ^ (11 / 10 : ℝ) ≤
      (lemma56MixedRemainingPower χ θ t ‖lemma56TaggedInverseSquare t a₀‖ β
        (lemma56TaggedInverseSquare t a₀ / (‖lemma56TaggedInverseSquare t a₀‖ : ℂ))⁻¹ J).re := by
  have hr := (lemma56_actual_tagged_inverse_square_bounds χ θ hD hθ htwist ha₀).1
  have hnorm : ∀ a ∈ lemma56FourZeroFinset χ θ t β,
      ‖lemma56TaggedInverseSquare t a / (‖lemma56TaggedInverseSquare t a₀‖ : ℂ)‖ ≤ 1 := by
    intro a ha
    rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hr]
    exact (div_le_iff₀ hr).mpr (by simpa only [one_mul] using hmax a ha)
  have hunit : ‖lemma56TaggedInverseSquare t a₀ / (‖lemma56TaggedInverseSquare t a₀‖ : ℂ)‖ = 1 := by
    rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hr, div_self hr.ne']
  have hm : 1 ≤ (lemma56FamilyOrder χ θ a₀.1 a₀.2 : ℝ) := by
    exact_mod_cast lemma56_actual_tagged_zero_order_pos χ θ hD hθ htwist ha₀
  have hd := lemma55_fejer_finite_weighted_power_detection (lemma56FourZeroFinset χ θ t β)
    (fun a => (lemma56FamilyOrder χ θ a.1 a.2 : ℝ))
    (fun a => lemma56TaggedInverseSquare t a / (‖lemma56TaggedInverseSquare t a₀‖ : ℂ))
    ha₀ (fun _ _ => Nat.cast_nonneg _) hm hnorm hunit J
  simp only [lemma56_tagged_normalized_power_sum] at hd
  rw [lemma56_actual_weighted_tagged_real_sum_eq] at hd
  have hN := lemma56_actual_four_zero_order_sum_bound χ θ hD hL hq hθ htwist ht β
  linarith only [hd, hN]

lemma lemma56_actual_near_one_zero_four_detected {D q : ℕ} [NeZero q]
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ q)
    (hD : 1 < D) (hL : 2000 ≤ lemma23PaperL D) (hq : (q : ℝ) < lemma56PaperT D)
    (hθ : θ ≠ 1) (htwist : lemma44CharacterTwist χ θ ≠ 1)
    {ρ β : ℂ} {ε : ℝ} (hε : 0 ≤ ε) (hεupper : ε ≤ 1 / 4)
    (hre : 1 - ε < ρ.re) (ht : |ρ.im| ≤ 2 * (D : ℝ))
    (hzero : DirichletCharacter.LFunction θ ρ = 0) :
    ∃ a₀ ∈ lemma56FourZeroFinset χ θ ρ.im β,
      0 < ‖lemma56TaggedInverseSquare ρ.im a₀‖ ∧ ‖lemma56TaggedInverseSquare ρ.im a₀‖ < 1 ∧
      ((1 + ε)⁻¹) ^ 2 ≤ ‖lemma56TaggedInverseSquare ρ.im a₀‖ ∧
      ∀ J : ℕ, (J : ℝ) / 4 - 79 * lemma23PaperL D ^ (11 / 10 : ℝ) ≤
        (lemma56MixedRemainingPower χ θ ρ.im ‖lemma56TaggedInverseSquare ρ.im a₀‖ β
          (lemma56TaggedInverseSquare ρ.im a₀ / (‖lemma56TaggedInverseSquare ρ.im a₀‖ : ℂ))⁻¹ J).re := by
  classical
  have hρ : (⟨2, ρ⟩ : Lemma56TaggedZero) ∈ lemma56FourZeroFinset χ θ ρ.im β := by
    apply (lemma56_mem_four_zero_finset χ θ ρ.im β ⟨2, ρ⟩).mpr
    simpa [lemma56ZeroFamily] using lemma56_near_one_zero_in_own_local_disk θ hθ hεupper hre hzero
  obtain ⟨a₀, ha₀, hmax⟩ := (lemma56FourZeroFinset χ θ ρ.im β).exists_max_image
    (fun a => ‖lemma56TaggedInverseSquare ρ.im a‖) ⟨⟨2, ρ⟩, hρ⟩
  have hb := lemma56_actual_tagged_inverse_square_bounds χ θ hD hθ htwist ha₀
  have hlower := (lemma56_near_one_zero_inverse_square_lower_bound θ hθ hε hre hzero).trans
    (by simpa [lemma56TaggedInverseSquare, lemma55FamilyHeight] using hmax ⟨2, ρ⟩ hρ)
  exact ⟨a₀, ha₀, hb.1, hb.2, hlower, fun J =>
    lemma56_actual_common_maximum_weighted_detection χ θ hD hL hq hθ htwist ht ha₀ hmax J⟩

end ZhangLS.Spec
