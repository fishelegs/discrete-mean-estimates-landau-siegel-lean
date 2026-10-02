import ZhangLS.Spec.CharacterAbelAnalyticContinuation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The actual character L-function near one

The Abel partial sum is bounded both by its length and by the conductor.
Splitting the actual integral at D gives an O(log D) bound on the original
analytic continuation, without any growth assumption on the L-function.
-/

namespace ZhangLS.Spec

open MeasureTheory Set Complex
open scoped Real

theorem RealPrimitiveCharacter.norm_sum_Icc_evalNat_le_length
    {D : ℕ} (χ : RealPrimitiveCharacter D) (N : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 N, χ.evalNat n‖ ≤ (N : ℝ) := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N, ‖χ.evalNat n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Icc 1 N, (1 : ℝ) :=
      Finset.sum_le_sum (fun n _ => χ.evalNat_norm_le_one n)
    _ = N := by simp

theorem lemma55_rpow_near_one_le_exp
    {D : ℕ} (hL : 2 ≤ Real.log (D : ℝ)) {σ t : ℝ}
    (hσ : 1 - 1 / Real.log (D : ℝ) ≤ σ)
    (ht : 1 ≤ t) (htD : t ≤ (D : ℝ)) :
    t ^ (1 - σ) ≤ Real.exp 1 := by
  have hLp : 0 < Real.log (D : ℝ) := by linarith
  have htp : 0 < t := by linarith
  calc
    _ ≤ t ^ (1 / Real.log (D : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le ht (by linarith)
    _ ≤ Real.exp 1 := by
      rw [Real.rpow_def_of_pos htp]
      apply Real.exp_le_exp.mpr
      have hlog : Real.log t ≤ Real.log (D : ℝ) := Real.log_le_log htp htD
      calc
        Real.log t * (1 / Real.log (D : ℝ)) =
            Real.log t / Real.log (D : ℝ) := by ring
        _ ≤ 1 := (div_le_one hLp).mpr hlog

theorem RealPrimitiveCharacter.norm_characterAbelIntegral_le_near_one
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2 ≤ Real.log (D : ℝ)) {s : ℂ}
    (hσ : 1 - 1 / Real.log (D : ℝ) ≤ s.re) :
    ‖characterAbelIntegral χ s‖ ≤ Real.exp 1 * (Real.log (D : ℝ) + 2) := by
  have hDp : (0 : ℝ) < D := by exact_mod_cast χ.modulus_pos
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD.le
  have hLp : 0 < Real.log (D : ℝ) := by linarith
  have hinv : 1 / Real.log (D : ℝ) ≤ (1 : ℝ) / 2 :=
    one_div_le_one_div_of_le (by norm_num) hL
  have hs : 0 < s.re := by linarith
  have hs2 : (1 : ℝ) / 2 ≤ s.re := by linarith
  let f : ℝ → ℂ := fun t =>
    (∑ n ∈ Finset.Icc 1 ⌊t⌋₊, χ.evalNat n) * (t : ℂ) ^ (-(s + 1))
  have hint : IntegrableOn f (Ioi 1) := χ.abelIntegrand_integrable hD hs
  have hfin : IntegrableOn f (Ioc 1 (D : ℝ)) :=
    hint.mono_set (fun _ ht => ht.1)
  have htail : IntegrableOn f (Ioi (D : ℝ)) :=
    hint.mono_set (fun _ ht => lt_of_le_of_lt hD1 ht)
  have hinvInt : IntegrableOn (fun t : ℝ => t⁻¹) (Ioc 1 (D : ℝ)) := by
    apply (intervalIntegral.intervalIntegrable_inv ?_ continuous_id.continuousOn).1
    intro t ht
    rw [uIcc_of_le hD1] at ht
    change t ≠ 0
    linarith [ht.1]
  have hsmall : ‖∫ t in Ioc 1 (D : ℝ), f t‖ ≤
      Real.exp 1 * Real.log (D : ℝ) := by
    calc
      _ ≤ ∫ t in Ioc 1 (D : ℝ), ‖f t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t in Ioc 1 (D : ℝ), Real.exp 1 * t⁻¹ := by
        apply integral_mono_ae hfin.norm (hinvInt.const_mul _)
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        have htp : 0 < t := by linarith [ht.1]
        have hpartial : ‖∑ n ∈ Finset.Icc 1 ⌊t⌋₊, χ.evalNat n‖ ≤ t :=
          (χ.norm_sum_Icc_evalNat_le_length ⌊t⌋₊).trans (Nat.floor_le htp.le)
        have hpow := lemma55_rpow_near_one_le_exp hL hσ ht.1.le ht.2
        dsimp [f]
        rw [norm_mul, norm_cpow_eq_rpow_re_of_pos htp]
        have hre : (-(s + 1)).re = -s.re - 1 := by simp; ring
        rw [hre]
        calc
          _ ≤ t * t ^ (-s.re - 1) :=
            mul_le_mul_of_nonneg_right hpartial (Real.rpow_nonneg htp.le _)
          _ = t ^ (1 - s.re) * t⁻¹ := by
            nth_rw 1 [← Real.rpow_one t]
            rw [← Real.rpow_neg_one t,
              ← Real.rpow_add htp, ← Real.rpow_add htp]
            congr 1
            ring
          _ ≤ Real.exp 1 * t⁻¹ :=
            mul_le_mul_of_nonneg_right hpow (inv_nonneg.mpr htp.le)
      _ = Real.exp 1 * Real.log (D : ℝ) := by
        rw [integral_const_mul, ← intervalIntegral.integral_of_le hD1,
          integral_inv_of_pos (by norm_num) hDp]
        simp
  have hmaj : IntegrableOn (fun t : ℝ => (D : ℝ) * t ^ (-s.re - 1))
      (Ioi (D : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hDp).const_mul _
  have hbig : ‖∫ t in Ioi (D : ℝ), f t‖ ≤ Real.exp 1 * 2 := by
    calc
      _ ≤ ∫ t in Ioi (D : ℝ), ‖f t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t in Ioi (D : ℝ), (D : ℝ) * t ^ (-s.re - 1) := by
        apply integral_mono_ae htail.norm hmaj
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have htp : 0 < t := hDp.trans ht
        dsimp [f]
        rw [norm_mul, norm_cpow_eq_rpow_re_of_pos htp]
        have hre : (-(s + 1)).re = -s.re - 1 := by simp; ring
        rw [hre]
        exact mul_le_mul_of_nonneg_right (χ.norm_sum_Icc_evalNat_le_modulus hD _)
          (Real.rpow_nonneg htp.le _)
      _ = (D : ℝ) ^ (1 - s.re) / s.re := by
        rw [integral_const_mul,
          integral_Ioi_rpow_of_lt (by linarith : -s.re - 1 < -1) hDp]
        have hden : -s.re - 1 + 1 = -s.re := by ring
        rw [hden]
        have hpow : (D : ℝ) * (D : ℝ) ^ (-s.re) = (D : ℝ) ^ (1 - s.re) := by
          nth_rw 1 [← Real.rpow_one (D : ℝ)]
          rw [← Real.rpow_add hDp]
          congr 1
        rw [neg_div_neg_eq, ← mul_div_assoc, hpow]
      _ ≤ Real.exp 1 / s.re :=
        div_le_div_of_nonneg_right
          (lemma55_rpow_near_one_le_exp hL hσ hD1 le_rfl) hs.le
      _ ≤ Real.exp 1 * 2 := by
        have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hs2
        have he := mul_le_mul_of_nonneg_left h (Real.exp_pos 1).le
        simpa [div_eq_mul_inv] using he
  have hunion : Ioc 1 (D : ℝ) ∪ Ioi (D : ℝ) = Ioi (1 : ℝ) := by
    ext t
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · intro ht
      rcases ht with ht | ht
      · exact ht.1
      · exact lt_of_le_of_lt hD1 ht
    · intro ht
      by_cases htD : t ≤ (D : ℝ)
      · exact Or.inl ⟨ht, htD⟩
      · exact Or.inr (lt_of_not_ge htD)
  have hdisj : Disjoint (Ioc 1 (D : ℝ)) (Ioi (D : ℝ)) := by
    apply disjoint_left.mpr
    intro t ht ht'
    exact (not_lt_of_ge ht.2) ht'
  change ‖∫ t in Ioi 1, f t‖ ≤ _
  rw [← hunion, setIntegral_union hdisj measurableSet_Ioi hfin htail]
  calc
    _ ≤ ‖∫ t in Ioc 1 (D : ℝ), f t‖ + ‖∫ t in Ioi (D : ℝ), f t‖ := norm_add_le _ _
    _ ≤ Real.exp 1 * Real.log (D : ℝ) + Real.exp 1 * 2 := add_le_add hsmall hbig
    _ = Real.exp 1 * (Real.log (D : ℝ) + 2) := by ring

/-- A logarithmic bound for the actual analytic continuation on a conductor-
dependent neighborhood of one. -/
theorem lemma55_actual_L_near_one_bound
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2 ≤ Real.log (D : ℝ)) {s : ℂ}
    (hσ : 1 - 1 / Real.log (D : ℝ) ≤ s.re) (hnorm : ‖s‖ ≤ 2) :
    ‖dirichletLFunction χ s‖ ≤ 4 * Real.exp 1 * Real.log (D : ℝ) := by
  have hLp : 0 < Real.log (D : ℝ) := by linarith
  have hinv : 1 / Real.log (D : ℝ) ≤ (1 : ℝ) / 2 :=
    one_div_le_one_div_of_le (by norm_num) hL
  have hs : 0 < s.re := by linarith
  rw [dirichletLFunction_eq_abelIntegral_of_pos_re χ hD hs, norm_mul]
  have hAbel := χ.norm_characterAbelIntegral_le_near_one hD hL hσ
  calc
    _ ≤ 2 * (Real.exp 1 * (Real.log (D : ℝ) + 2)) :=
      mul_le_mul hnorm hAbel (norm_nonneg _) (by positivity)
    _ ≤ 4 * Real.exp 1 * Real.log (D : ℝ) := by
      nlinarith [Real.exp_pos 1]

end ZhangLS.Spec
