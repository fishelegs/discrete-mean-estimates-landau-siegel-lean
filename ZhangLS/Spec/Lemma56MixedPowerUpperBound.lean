import ZhangLS.Spec.Lemma56ActualZeroDetection
import ZhangLS.Spec.Lemma55CombinedPowerUpperBound

/-! # Actual mixed arithmetic upper bound with independent normalization scale

Actual Dirichlet L-functions and their actual analytic orders are retained.
These auxiliary results do not assert the complete Lemma 5.6 prime-window estimate.
-/

namespace ZhangLS.Spec
open Complex Metric Set Filter MeromorphicOn Finset
open scoped Topology Real
set_option maxHeartbeats 1000000

noncomputable def lemma56MixedRemainingPower {D q : ℕ} [NeZero q]
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ q)
    (t R : ℝ) (β v : ℂ) (J : ℕ) : ℂ :=
  letI : NeZero (D * q) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne q)⟩
  (lemma55WeightedRemainingZeroPowerSum χ 0 R β v J + lemma55ZetaWeightedZeroPowerSum 0 R v J) +
    (lemma56WeightedZeroPowerSum θ t R v J + lemma56WeightedZeroPowerSum (lemma44CharacterTwist χ θ) t R v J)

noncomputable def lemma56MixedRemovedDerivative {D q : ℕ} [NeZero q]
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ q)
    (t R : ℝ) (β v : ℂ) (J : ℕ) : ℂ :=
  letI : NeZero (D * q) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne q)⟩
  (lemma55WeightedRemovedLogDerivative χ 0 R β v J + lemma55ZetaWeightedRemovedLogDerivative 0 R v J) +
    (lemma56WeightedLogDerivative θ t R v J + lemma56WeightedLogDerivative (lemma44CharacterTwist χ θ) t R v J)

lemma lemma56_actual_mixed_remaining_error_bound {D q : ℕ} [NeZero q]
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ q)
    (hθ : θ ≠ 1) (htwist : lemma44CharacterTwist χ θ ≠ 1)
    (hD : 1 < D) (hL : 2000 ≤ Real.log (D : ℝ)) (t : ℝ)
    {β : ℂ} (hzero : dirichletLFunction χ β = 0) (hderiv : deriv (dirichletLFunction χ) β ≠ 0)
    {R : ℝ} (hR : 0 < R) (hlower : ((1 + 2 / Real.log (D : ℝ))⁻¹) ^ 2 ≤ R)
    {v : ℂ} (hv : ‖v‖ ≤ 1) (J : ℕ) :
    letI : NeZero (D * q) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne q)⟩
    ‖lemma56MixedRemovedDerivative χ θ t R β v J - lemma56MixedRemainingPower χ θ t R β v J‖ ≤
      187200 * Real.log (D : ℝ) + 36000 * lemma56JensenLogSize θ t +
        36000 * lemma56JensenLogSize (lemma44CharacterTwist χ θ) t := by
  letI : NeZero (D * q) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne q)⟩
  have hχ0 := lemma55_actual_weighted_remaining_error_uniform_bound χ hD hL (by simp : |(0 : ℝ)| ≤ 2 * D)
    hR hlower hzero hderiv hv J
  have hζ0 := lemma55_actual_zeta_weighted_power_error_uniform_bound hD hL (by simp : |(0 : ℝ)| ≤ 2 * D)
    hR hlower hv J
  have hθt := lemma56_actual_weighted_power_error_uniform_bound θ hθ hL (t := t) hR hlower hv J
  have htw := lemma56_actual_weighted_power_error_uniform_bound (lemma44CharacterTwist χ θ) htwist hL
    (t := t) hR hlower hv J
  have heq : lemma56MixedRemovedDerivative χ θ t R β v J - lemma56MixedRemainingPower χ θ t R β v J =
      ((lemma55WeightedRemovedLogDerivative χ 0 R β v J - lemma55WeightedRemainingZeroPowerSum χ 0 R β v J) +
        (lemma55ZetaWeightedRemovedLogDerivative 0 R v J - lemma55ZetaWeightedZeroPowerSum 0 R v J)) +
      ((lemma56WeightedLogDerivative θ t R v J - lemma56WeightedZeroPowerSum θ t R v J) +
        (lemma56WeightedLogDerivative (lemma44CharacterTwist χ θ) t R v J -
          lemma56WeightedZeroPowerSum (lemma44CharacterTwist χ θ) t R v J)) := by
    unfold lemma56MixedRemovedDerivative lemma56MixedRemainingPower
    ring
  rw [heq]
  apply (norm_add_le _ _).trans
  have h0 := (norm_add_le _ _).trans (add_le_add hχ0 hζ0)
  have ht := (norm_add_le _ _).trans (add_le_add hθt htw)
  exact (add_le_add h0 ht).trans_eq (by ring)

lemma lemma56_actual_mixed_removed_derivative_nonpos {D q : ℕ} [NeZero q]
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ q) (t : ℝ)
    {R : ℝ} (hR : 0 < R) (β : ℂ) {v : ℂ} (hv : ‖v‖ ≤ 1) (J : ℕ) :
    (lemma56MixedRemovedDerivative χ θ t R β v J - lemma55WeightedLocalPoleDifference χ 0 R β v J).re ≤ 0 := by
  letI : NeZero (D * q) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne q)⟩
  have heq : lemma56MixedRemovedDerivative χ θ t R β v J - lemma55WeightedLocalPoleDifference χ 0 R β v J =
      ∑ j ∈ Finset.range J, (lemma55FejerDetectionWeight v J j : ℂ) *
        (lemma55NormalizedLogDerivative χ 0 (2 * j + 1) + lemma55ZetaNormalizedLogDerivative 0 (2 * j + 1) +
          (lemma56NormalizedDerivative θ t (2 * j + 1) +
            lemma56NormalizedDerivative (lemma44CharacterTwist χ θ) t (2 * j + 1))) /
              (R : ℂ) ^ (j + 1) := by
    unfold lemma56MixedRemovedDerivative
    rw [lemma55_actual_removed_pair_pole_identity]
    unfold lemma56WeightedLogDerivative
    rw [← sum_add_distrib]
    have hsum : (∑ j ∈ range J, (lemma55FejerDetectionWeight v J j : ℂ) *
      (lemma55NormalizedLogDerivative χ 0 (2 * j + 1) + lemma55ZetaNormalizedLogDerivative 0 (2 * j + 1)) /
        (R : ℂ) ^ (j + 1)) +
      (∑ j ∈ range J, ((lemma55FejerDetectionWeight v J j : ℂ) * lemma56NormalizedDerivative θ t (2 * j + 1) /
        (R : ℂ) ^ (j + 1) + (lemma55FejerDetectionWeight v J j : ℂ) *
        lemma56NormalizedDerivative (lemma44CharacterTwist χ θ) t (2 * j + 1) / (R : ℂ) ^ (j + 1))) =
      ∑ j ∈ range J, (lemma55FejerDetectionWeight v J j : ℂ) *
        (lemma55NormalizedLogDerivative χ 0 (2 * j + 1) + lemma55ZetaNormalizedLogDerivative 0 (2 * j + 1) +
          (lemma56NormalizedDerivative θ t (2 * j + 1) +
            lemma56NormalizedDerivative (lemma44CharacterTwist χ θ) t (2 * j + 1))) /
              (R : ℂ) ^ (j + 1) := by
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro j _
      ring
    linear_combination hsum
  rw [heq]
  exact lemma56_actual_weighted_four_function_nonpos χ θ t hR hv J

lemma lemma56_actual_mixed_remaining_real_upper_bound {D q : ℕ} [NeZero q]
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ q)
    (hθ : θ ≠ 1) (htwist : lemma44CharacterTwist χ θ ≠ 1)
    (hD : 1 < D) (hL : 2000 ≤ Real.log (D : ℝ)) (t : ℝ)
    {β R U : ℝ} (hβ : β ≤ 1) (hzero : dirichletLFunction χ (β : ℂ) = 0)
    (hderiv : deriv (dirichletLFunction χ) (β : ℂ) ≠ 0)
    (hmem : (β : ℂ) ∈ lemma55LocalZeroFinset χ 0) (hR : 0 < R)
    (hlower : ((1 + 2 / Real.log (D : ℝ))⁻¹) ^ 2 ≤ R)
    (hU : 0 < U) (hUlower : ((1 + 2 / U)⁻¹) ^ 2 ≤ R)
    {v : ℂ} (hv : ‖v‖ ≤ 1) (J : ℕ) :
    letI : NeZero (D * q) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne q)⟩
    (lemma56MixedRemainingPower χ θ t R (β : ℂ) v J).re ≤
      187200 * Real.log (D : ℝ) + 36000 * lemma56JensenLogSize θ t +
        36000 * lemma56JensenLogSize (lemma44CharacterTwist χ θ) t +
          2 * (1 - β) * (J : ℝ) * ((J : ℝ) + 1) * Real.exp (4 * (J : ℝ) / U) := by
  letI : NeZero (D * q) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne q)⟩
  have he := (abs_re_le_norm (lemma56MixedRemovedDerivative χ θ t R (β : ℂ) v J -
    lemma56MixedRemainingPower χ θ t R (β : ℂ) v J)).trans
      (lemma56_actual_mixed_remaining_error_bound χ θ hθ htwist hD hL t hzero hderiv hR hlower hv J)
  rw [sub_re] at he
  have hb := lemma56_actual_mixed_removed_derivative_nonpos χ θ t hR (β : ℂ) hv J
  rw [sub_re] at hb
  have hp := lemma55_weighted_exceptional_pole_difference_bound 0 β hβ hU hR hUlower hv J
  have hlocal : lemma55WeightedLocalPoleDifference χ 0 R (β : ℂ) v J =
      lemma55WeightedExceptionalPoleDifference 0 β R v J := by
    rw [lemma55_actual_local_pole_difference_eq, if_pos hmem, add_zero]
  rw [← hlocal] at hp
  have h0 := (re_le_norm (lemma55WeightedLocalPoleDifference χ 0 R (β : ℂ) v J)).trans hp
  linarith only [(abs_le.mp he).1, hb, h0]

end ZhangLS.Spec
