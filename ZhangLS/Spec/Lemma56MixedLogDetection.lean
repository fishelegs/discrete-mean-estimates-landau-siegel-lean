import ZhangLS.Spec.Lemma56WeakZeroExclusion

/-! # Actual mixed zero detection with unrestricted height

Actual L-functions and their actual zeros and analytic orders are retained.
The original finite prime-window target remains a separate unproved obligation.
-/

namespace ZhangLS.Spec
open Complex Metric Set Finset Filter
open scoped Real Topology
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

lemma lemma56_actual_four_zero_order_log_bound {D q : ℕ} [NeZero q]
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ q)
    (hD : 1 < D) (hL : 2000 ≤ lemma23PaperL D)
    (hθ : θ ≠ 1) (htwist : lemma44CharacterTwist χ θ ≠ 1) (t : ℝ) (β : ℂ) :
    letI : NeZero (D * q) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne q)⟩
    (∑ a ∈ lemma56FourZeroFinset χ θ t β, (lemma56FamilyOrder χ θ a.1 a.2 : ℝ)) ≤
      31 * lemma23PaperL D + 6 * lemma56JensenLogSize θ t +
        6 * lemma56JensenLogSize (lemma44CharacterTwist χ θ) t := by
  classical
  letI : NeZero (D * q) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne q)⟩
  have hχ0 := lemma55_removed_zero_order_sum_bound χ hD hL (by simp : |(0 : ℝ)| ≤ 2 * D) β
  have hζ0 := lemma55_actual_zeta_local_multiplicity_bound hD hL (by simp : |(0 : ℝ)| ≤ 2 * D)
  have hθt := lemma56_actual_local_multiplicity_bound θ hθ t
  have htw := lemma56_actual_local_multiplicity_bound (lemma44CharacterTwist χ θ) htwist t
  unfold lemma56FourZeroFinset
  rw [sum_sigma, Fin.sum_univ_four]
  simp [lemma56ZeroFamily, lemma56FamilyOrder, lemma56FamilyFunction]
  unfold lemma55ZetaLocalMultiplicity at hζ0
  unfold lemma56LocalMultiplicity at hθt htw
  push_cast at hζ0 hθt htw
  change _ ≤ 13 * lemma23PaperL D at hχ0
  change _ ≤ 18 * lemma23PaperL D at hζ0
  simp only [lemma56JensenLogSize, Nat.cast_mul]
  linarith only [hχ0, hζ0, hθt, htw]

lemma lemma56_actual_common_maximum_log_detection {D q : ℕ} [NeZero q]
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ q)
    (hD : 1 < D) (hL : 2000 ≤ lemma23PaperL D)
    (hθ : θ ≠ 1) (htwist : lemma44CharacterTwist χ θ ≠ 1)
    {t U : ℝ} (hLU : lemma23PaperL D ≤ U)
    (hBθ : lemma56JensenLogSize θ t ≤ 4 * U)
    (hBtw : letI : NeZero (D * q) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne q)⟩
      lemma56JensenLogSize (lemma44CharacterTwist χ θ) t ≤ 4 * U)
    {β : ℂ} {a₀ : Lemma56TaggedZero} (ha₀ : a₀ ∈ lemma56FourZeroFinset χ θ t β)
    (hmax : ∀ a ∈ lemma56FourZeroFinset χ θ t β,
      ‖lemma56TaggedInverseSquare t a‖ ≤ ‖lemma56TaggedInverseSquare t a₀‖) (J : ℕ) :
    (J : ℝ) / 4 - 79 * U ≤
      (lemma56MixedRemainingPower χ θ t ‖lemma56TaggedInverseSquare t a₀‖ β
        (lemma56TaggedInverseSquare t a₀ / (‖lemma56TaggedInverseSquare t a₀‖ : ℂ))⁻¹ J).re := by
  letI : NeZero (D * q) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne q)⟩
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
  have hN := lemma56_actual_four_zero_order_log_bound χ θ hD hL hθ htwist t β
  linarith only [hd, hN, hLU, hBθ, hBtw]

end ZhangLS.Spec
