import ZhangLS.Spec.Lemma55MangoldtPositivity
import ZhangLS.Spec.Lemma44ProductDirichletSeries

/-! # Actual arithmetic positivity for arbitrary complex characters

These are actual analytic or arithmetic facts. The full prime-window
decay assertion of Lemma 5.6 is not proved here.
-/

namespace ZhangLS.Spec
open Complex Filter Set LSeries
open scoped Topology ComplexOrder
set_option maxHeartbeats 1000000

noncomputable def lemma56Mangoldt {r : ℕ} (θ : DirichletCharacter ℂ r) : ℕ → ℂ :=
  fun n => θ (n : ZMod r) * (ArithmeticFunction.vonMangoldt n : ℂ)

noncomputable def lemma56NormalizedDerivative {r : ℕ} [NeZero r]
    (θ : DirichletCharacter ℂ r) (t : ℝ) (k : ℕ) : ℂ :=
  (-1 : ℂ) ^ k * iteratedDeriv k (logDeriv (DirichletCharacter.LFunction θ))
    (lemma55JensenCenter t) / (k.factorial : ℂ)

lemma lemma56_actual_mangoldt_abscissa {r : ℕ} [NeZero r]
    (θ : DirichletCharacter ℂ r) : abscissaOfAbsConv (lemma56Mangoldt θ) ≤ (1 : ℝ) := by
  apply abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
  intro y hy
  exact DirichletCharacter.LSeriesSummable_twist_vonMangoldt θ (by simpa using hy)

lemma lemma56_actual_logDeriv_mangoldt {r : ℕ} [NeZero r]
    (θ : DirichletCharacter ℂ r) {z : ℂ} (hz : 1 < z.re) :
    logDeriv (DirichletCharacter.LFunction θ) z = -LSeries (lemma56Mangoldt θ) z := by
  rw [logDeriv_apply, DirichletCharacter.deriv_LFunction_eq_deriv_LSeries θ hz,
    DirichletCharacter.LFunction_eq_LSeries θ hz]
  have hs := DirichletCharacter.LSeries_twist_vonMangoldt_eq θ hz
  change LSeries (lemma56Mangoldt θ) z =
    -deriv (LSeries (fun n => θ (n : ZMod r))) z /
      LSeries (fun n => θ (n : ZMod r)) z at hs
  simpa only [neg_div, neg_neg] using (congrArg Neg.neg hs).symm

lemma lemma56_actual_higher_logDeriv_mangoldt {r : ℕ} [NeZero r]
    (θ : DirichletCharacter ℂ r) {z : ℂ} (hz : 1 < z.re) (k : ℕ) :
    iteratedDeriv k (logDeriv (DirichletCharacter.LFunction θ)) z =
      -((-1 : ℂ) ^ k * LSeries (LSeries.logMul^[k] (lemma56Mangoldt θ)) z) := by
  have heq : logDeriv (DirichletCharacter.LFunction θ) =ᶠ[𝓝 z] -LSeries (lemma56Mangoldt θ) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hz] with w hw
    exact lemma56_actual_logDeriv_mangoldt θ hw
  rw [heq.iteratedDeriv_eq k, iteratedDeriv_neg]
  rw [LSeries_iteratedDeriv k (lt_of_le_of_lt (lemma56_actual_mangoldt_abscissa θ)
    (by exact_mod_cast hz))]

lemma lemma56_actual_normalized_logDeriv_mangoldt {r : ℕ} [NeZero r]
    (θ : DirichletCharacter ℂ r) (t : ℝ) (k : ℕ) :
    lemma56NormalizedDerivative θ t k =
      -LSeries (LSeries.logMul^[k] (lemma56Mangoldt θ)) (lemma55JensenCenter t) /
        (k.factorial : ℂ) := by
  have he : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by
    rw [← mul_pow]
    norm_num
  unfold lemma56NormalizedDerivative
  rw [lemma56_actual_higher_logDeriv_mangoldt θ (by simp) k]
  congr 1
  calc
    _ = -(((-1 : ℂ) ^ k * (-1 : ℂ) ^ k) *
        LSeries (LSeries.logMul^[k] (lemma56Mangoldt θ)) (lemma55JensenCenter t)) := by ring
    _ = _ := by rw [he, one_mul]

lemma lemma56_actual_log_power_summable {r : ℕ} [NeZero r]
    (θ : DirichletCharacter ℂ r) {z : ℂ} (hz : 1 < z.re) (k : ℕ) :
    LSeriesSummable (LSeries.logMul^[k] (lemma56Mangoldt θ)) z := by
  apply LSeriesSummable_of_abscissaOfAbsConv_lt_re
  rw [LSeries.absicssaOfAbsConv_logPowMul]
  exact lt_of_le_of_lt (lemma56_actual_mangoldt_abscissa θ) (by exact_mod_cast hz)

lemma lemma56_nonnegative_majorant_series_bound {f g : ℕ → ℂ}
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, ‖g n‖ ≤ (f n).re)
    (hs : LSeriesSummable f (2 : ℂ)) (t : ℝ)
    (hgs : LSeriesSummable g (lemma55JensenCenter t)) :
    ‖LSeries g (lemma55JensenCenter t)‖ ≤ (LSeries f 2).re := by
  have hst : LSeriesSummable f (lemma55JensenCenter t) := hs.of_re_le_re (by simp)
  change ‖∑' n, term g (lemma55JensenCenter t) n‖ ≤ (∑' n, term f 2 n).re
  calc
    _ ≤ ∑' n, ‖term g (lemma55JensenCenter t) n‖ := norm_tsum_le_tsum_norm hgs.norm
    _ ≤ ∑' n, ‖term f (2 : ℂ) n‖ := hgs.norm.tsum_le_tsum (fun n =>
      (norm_term_le (lemma55JensenCenter t) ((hg n).trans_eq (Complex.re_eq_norm.mpr (hf n)))).trans
        (norm_term_le_of_re_le_re f (by simp) n)) hs.norm
    _ = ∑' n, (term f 2 n).re := by
      apply tsum_congr
      intro n
      exact (Complex.re_eq_norm.mpr (term_nonneg (hf n) (2 : ℝ))).symm
    _ = _ := (re_tsum hs).symm


lemma lemma56_log_power_twist (f g : ℕ → ℂ) (k n : ℕ) :
    LSeries.logMul^[k] (fun m => f m * g m) n = (LSeries.logMul^[k] f n) * g n := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    simp only [LSeries.logMul]
    rw [ih]
    ring

noncomputable def lemma56TwistedPositiveCoeffs {D r : ℕ}
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ r) (k : ℕ) : ℕ → ℂ :=
  LSeries.logMul^[k] (lemma56Mangoldt θ + lemma56Mangoldt (lemma44CharacterTwist χ θ))

lemma lemma56_actual_twisted_positive_coeffs {D r : ℕ} [NeZero r]
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ r) (k n : ℕ) :
    lemma56TwistedPositiveCoeffs χ θ k n =
      lemma55PositiveMangoldtCoeffs χ k n * θ (n : ZMod r) := by
  have he : lemma56Mangoldt θ + lemma56Mangoldt (lemma44CharacterTwist χ θ) =
      (fun m => (lemma55MangoldtTwist χ m +
        lemma55MangoldtTwist lemma55ZetaTrivialCharacter m) * θ (m : ZMod r)) := by
    funext m
    rw [Pi.add_apply, lemma55_mangoldt_trivial]
    simp only [lemma56Mangoldt, lemma55MangoldtTwist, lemma44CharacterTwist_eval_nat]
    ring
  unfold lemma56TwistedPositiveCoeffs
  rw [he, lemma56_log_power_twist]
  rfl

lemma lemma56_actual_twisted_coeff_norm_bound {D r : ℕ} [NeZero r]
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ r) (k n : ℕ) :
    ‖lemma56TwistedPositiveCoeffs χ θ k n‖ ≤ (lemma55PositiveMangoldtCoeffs χ k n).re := by
  have hp : 0 ≤ lemma55PositiveMangoldtCoeffs χ k n :=
    lemma55_log_power_nonnegative (lemma55_actual_mangoldt_positive χ) k n
  rw [lemma56_actual_twisted_positive_coeffs, norm_mul]
  calc
    _ ≤ ‖lemma55PositiveMangoldtCoeffs χ k n‖ * 1 :=
      mul_le_mul_of_nonneg_left (θ.norm_le_one _) (norm_nonneg _)
    _ = _ := by rw [mul_one, (Complex.re_eq_norm.mpr hp).symm]

lemma lemma56_actual_twisted_coeffs_summable {D r : ℕ} [NeZero r]
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ r)
    {z : ℂ} (hz : 1 < z.re) (k : ℕ) :
    LSeriesSummable (lemma56TwistedPositiveCoeffs χ θ k) z := by
  letI : NeZero (D * r) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne r)⟩
  unfold lemma56TwistedPositiveCoeffs
  rw [lemma55_log_power_add]
  exact (lemma56_actual_log_power_summable θ hz k).add
    (lemma56_actual_log_power_summable (lemma44CharacterTwist χ θ) hz k)

lemma lemma56_actual_twisted_pair_mangoldt {D r : ℕ} [NeZero r]
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ r) (t : ℝ) (k : ℕ) :
    letI : NeZero (D * r) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne r)⟩
    lemma56NormalizedDerivative θ t k + lemma56NormalizedDerivative (lemma44CharacterTwist χ θ) t k =
      -LSeries (lemma56TwistedPositiveCoeffs χ θ k) (lemma55JensenCenter t) /
        (k.factorial : ℂ) := by
  letI : NeZero (D * r) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne r)⟩
  rw [lemma56_actual_normalized_logDeriv_mangoldt, lemma56_actual_normalized_logDeriv_mangoldt]
  unfold lemma56TwistedPositiveCoeffs
  rw [lemma55_log_power_add, LSeries_add
    (lemma56_actual_log_power_summable θ (by simp) k)
    (lemma56_actual_log_power_summable (lemma44CharacterTwist χ θ) (by simp) k)]
  ring

lemma lemma56_actual_four_function_logDeriv_nonpos {D r : ℕ} [NeZero r]
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ r) (t : ℝ) (k : ℕ) :
    letI : NeZero (D * r) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne r)⟩
    (lemma55NormalizedLogDerivative χ 0 k + lemma55ZetaNormalizedLogDerivative 0 k +
      (lemma56NormalizedDerivative θ t k + lemma56NormalizedDerivative (lemma44CharacterTwist χ θ) t k)).re ≤ 0 := by
  letI : NeZero (D * r) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne r)⟩
  have hf : ∀ n, 0 ≤ lemma55PositiveMangoldtCoeffs χ k n :=
    fun n => lemma55_log_power_nonnegative (lemma55_actual_mangoldt_positive χ) k n
  have hb := lemma56_nonnegative_majorant_series_bound hf
    (lemma56_actual_twisted_coeff_norm_bound χ θ k)
    (lemma55_actual_combined_mangoldt_summable χ (z := 2) (by norm_num) k) t
    (lemma56_actual_twisted_coeffs_summable χ θ (by simp) k)
  have hre := (neg_le_neg (abs_re_le_norm
    (LSeries (lemma56TwistedPositiveCoeffs χ θ k) (lemma55JensenCenter t)))).trans
      (neg_abs_le (LSeries (lemma56TwistedPositiveCoeffs χ θ k) (lemma55JensenCenter t)).re)
  rw [lemma55_actual_two_function_mangoldt, lemma56_actual_twisted_pair_mangoldt]
  rw [show lemma55JensenCenter 0 = (2 : ℂ) by simp [lemma55JensenCenter]]
  rw [← add_div, ← neg_add, div_natCast_re, neg_re, add_re]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith only [hb, hre]) (by positivity)

lemma lemma56_actual_weighted_four_function_nonpos {D r : ℕ} [NeZero r]
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ r) (t : ℝ)
    {R : ℝ} (hR : 0 < R) {v : ℂ} (hv : ‖v‖ ≤ 1) (J : ℕ) :
    letI : NeZero (D * r) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne r)⟩
    (∑ j ∈ Finset.range J, (lemma55FejerDetectionWeight v J j : ℂ) *
      (lemma55NormalizedLogDerivative χ 0 (2 * j + 1) +
        lemma55ZetaNormalizedLogDerivative 0 (2 * j + 1) +
        (lemma56NormalizedDerivative θ t (2 * j + 1) +
          lemma56NormalizedDerivative (lemma44CharacterTwist χ θ) t (2 * j + 1))) /
            (R : ℂ) ^ (j + 1)).re ≤ 0 := by
  letI : NeZero (D * r) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne r)⟩
  rw [Complex.re_sum]
  apply Finset.sum_nonpos
  intro j _
  rw [← Complex.ofReal_pow, div_ofReal_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (lemma55_fejer_detection_weight_bounds hv J j).1
      (lemma56_actual_four_function_logDeriv_nonpos χ θ t (2 * j + 1))) (pow_nonneg hR.le _)

end ZhangLS.Spec
