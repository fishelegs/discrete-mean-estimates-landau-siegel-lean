import ZhangLS.Spec.DivisorConductorBlockMomentsDefinitions

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec.DivisorConductorBlockMoments
open Complex Finset
open scoped Classical ComplexConjugate

/-- Norm of the literal negative complex power; positivity is explicit. -/
theorem longCoefficient_norm (d : ℕ) (b : ℕ → ℂ) (t : ℝ) {l : ℕ} (hl : 0 < l) :
    ‖longCoefficient d b t l‖ = ‖b (d * l)‖ / (l : ℝ) := by
  have hlR : 0 < (l : ℝ) := by exact_mod_cast hl
  unfold longCoefficient
  rw [norm_mul, ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hlR]
  norm_num [Complex.mul_re, Real.rpow_neg, div_eq_mul_inv]

theorem dilated_coefficient_bound {C_b : ℝ} (hC : 0 ≤ C_b) {b : ℕ → ℂ}
    (hb : CoefficientBound C_b b) (d l : ℕ) (hd : 0 < d) (hl : 0 < l) :
    ‖b (d * l)‖ ≤ (C_b * (lemma34Tau 5 d : ℝ)) * (lemma34Tau 5 l : ℝ) := by
  apply (hb (d * l) (Nat.mul_pos hd hl)).trans
  have ht : (lemma34Tau 5 (d * l) : ℝ) ≤
      (lemma34Tau 5 d : ℝ) * (lemma34Tau 5 l : ℝ) := by
    exact_mod_cast proposition71_tau_submultiplicative 5 d l
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left ht hC

/-- The arithmetic energy uses τ₅(dl)≤τ₅(d)τ₅(l), τ₅²≤τ₂₅,
and the proved harmonic convolution bound, with the mask retained. -/
theorem long_coefficient_energy {X C_b : ℝ} (hX : 1 ≤ X) (hC : 0 ≤ C_b)
    {b : ℕ → ℂ} (hb : CoefficientBound C_b b) (d h : ℕ) (hd : 0 < d) (t : ℝ) :
    (∑ l ∈ longIndices h X, ‖longCoefficient d b t l‖ ^ 2) ≤
      (2 / X) * longEnvelope C_b d X := by
  have hXp : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hN : 1 ≤ ⌊8 * X⌋₊ := by
    apply Nat.le_floor
    norm_num
    linarith
  have hY : 0 < X / 2 := by positivity
  have hYl : ∀ l ∈ longIndices h X, X / 2 ≤ (l : ℝ) :=
    fun l hl => (mem_filter.mp hl).2.1
  have he : (∑ l ∈ longIndices h X, ‖longCoefficient d b t l‖ ^ 2) =
      ∑ l ∈ longIndices h X, ‖b (d * l)‖ ^ 2 / (l : ℝ) ^ 2 := by
    apply sum_congr rfl
    intro l hl
    rw [longCoefficient_norm d b t (longIndices_positive hl), div_pow]
  rw [he]
  have henergy := proposition141_bounded_coefficient_interval_energy ⌊8 * X⌋₊ hN
    (C_b * (lemma34Tau 5 d : ℝ)) (by positivity) (fun l => b (d * l))
    (longIndices h X) (longIndices_subset h X)
    (fun l hl => dilated_coefficient_bound hC hb d l hd (by
      have := (mem_Icc.mp hl).1
      omega)) hY hYl
  apply henergy.trans
  have hfloor : (⌊8 * X⌋₊ : ℝ) ≤ 8 * X := Nat.floor_le (by positivity)
  have hNpos : 0 < (⌊8 * X⌋₊ : ℝ) := by exact_mod_cast hN
  have hloglo : 0 ≤ 1 + Real.log (⌊8 * X⌋₊ : ℝ) := by
    have hlog : 0 ≤ Real.log (⌊8 * X⌋₊ : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
    linarith
  have hlog : (1 + Real.log (⌊8 * X⌋₊ : ℝ)) ^ 25 ≤ logWeight X := by
    exact pow_le_pow_left₀ hloglo (by linarith [Real.log_le_log hNpos hfloor]) 25
  calc
    _ ≤ ((C_b * (lemma34Tau 5 d : ℝ)) ^ 2 / (X / 2)) * logWeight X := by
      exact mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = _ := by unfold longEnvelope; field_simp

/-- Elementary finite Cauchy, used for the genuine conductor-one polynomial. -/
theorem norm_sum_sq_le_card_energy (S : Finset ℕ) (a : ℕ → ℂ) :
    ‖∑ n ∈ S, a n‖ ^ 2 ≤ (S.card : ℝ) * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  have hnorm := norm_sum_le S a
  have hcs := sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun n => ‖a n‖)
  have hs : (∑ n ∈ S, ‖a n‖) ^ 2 ≤ (S.card : ℝ) * ∑ n ∈ S, ‖a n‖ ^ 2 := by
    simpa using hcs
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans hs

theorem longIndices_card_bound (h : ℕ) {X : ℝ} (hX : 1 ≤ X) :
    ((longIndices h X).card : ℝ) ≤ 8 * X := by
  have hcard : (longIndices h X).card ≤ ⌊8 * X⌋₊ := by
    have hc := card_le_card (longIndices_subset h X)
    simpa using hc
  exact (Nat.cast_le.mpr hcard).trans (Nat.floor_le (by linarith : 0 ≤ 8 * X))

theorem long_one_moment {X C_b : ℝ} (hX : 1 ≤ X) (hC : 0 ≤ C_b)
    {b : ℕ → ℂ} (hb : CoefficientBound C_b b) (d h : ℕ) (hd : 0 < d) (t : ℝ) :
    ‖longPolynomial d h X b 1 1 t‖ ^ 2 ≤ 16 * longEnvelope C_b d X := by
  have heq : longPolynomial d h X b 1 1 t =
      ∑ l ∈ longIndices h X, longCoefficient d b t l := by
    rw [longPolynomial_coefficient_sum]
    apply sum_congr rfl
    intro l hl
    have hθ : (1 : DirichletCharacter ℂ 1) (l : ZMod 1) = 1 := by
      rw [show (l : ZMod 1) = 1 by exact Subsingleton.elim _ _, map_one]
    rw [hθ, mul_one]
  rw [heq]
  apply (norm_sum_sq_le_card_energy _ _).trans
  calc
    _ ≤ (8 * X) * ((2 / X) * longEnvelope C_b d X) :=
      mul_le_mul (longIndices_card_bound h hX) (long_coefficient_energy hX hC hb d h hd t)
        (sum_nonneg (fun _ _ => sq_nonneg _)) (by linarith)
    _ = _ := by field_simp; ring

end ZhangLS.Spec.DivisorConductorBlockMoments
