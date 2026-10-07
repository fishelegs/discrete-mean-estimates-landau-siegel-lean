import Splice.ElementaryPrimeMass
import Splice.LValueNonnegative

open scoped BigOperators

/-! Public type and transitive-axiom receipt for the elementary analytic adapter. -/

#check @Splice.character_sum_Icc_norm_le
#check @Splice.nu_nonneg
#check @Splice.raw_LSeries_one_eq_zero
#check @Splice.LFunction_one_eq_abelIntegral
#check @Splice.norm_LFunction_one_sub_characterHarmonicSum_le
#check @Splice.tendsto_characterHarmonicSum
#check @Splice.LFunction_one_im_eq_zero
#check @Splice.LFunction_one_eq_ofReal_re
#check @Splice.nu_summatory_error_six_sqrt
#check @Splice.nu_harmonic_tail_eighteen_sqrt
#check @Splice.ExplicitMertens.prime_log_div_abs_error_le_four
#check @Splice.LOne_nonneg
#check @Splice.elementary_prime_mass

#print axioms Splice.character_sum_Icc_norm_le
#print axioms Splice.nu_nonneg
#print axioms Splice.raw_LSeries_one_eq_zero
#print axioms Splice.LFunction_one_eq_abelIntegral
#print axioms Splice.norm_LFunction_one_sub_characterHarmonicSum_le
#print axioms Splice.tendsto_characterHarmonicSum
#print axioms Splice.LFunction_one_im_eq_zero
#print axioms Splice.LFunction_one_eq_ofReal_re
#print axioms Splice.nu_summatory_error_six_sqrt
#print axioms Splice.nu_harmonic_tail_eighteen_sqrt
#print axioms Splice.ExplicitMertens.prime_log_div_abs_error_le_four
#print axioms Splice.LOne_nonneg
#print axioms Splice.elementary_prime_mass

example {D : ℕ} [NeZero D] (χ : DirichletCharacter ℂ D) (hne : χ ≠ 1)
    (hreal : ∀ x : ZMod D, (χ x).im = 0) : χ.LFunction 1 = (Splice.LOne χ : ℂ) :=
  Splice.LFunction_one_eq_ofReal_re χ hne (Splice.character_sum_Icc_norm_le χ hne) hreal

example {D : ℕ} [NeZero D] (hD : 97 ≤ D)
    (χ : DirichletCharacter ℂ D) (hne : χ ≠ 1)
    (hreal : ∀ x : ZMod D, (χ x).im = 0) :
    (∑ p ∈ (Nat.primesLE ⌊(D : ℝ) ^ 32⌋₊).filter
      (fun p => 86713344 < p ∧ ¬ p ∣ 2 * D ∧ χ p = -1),
        Real.log p / (p : ℝ)) / (32 * Real.log D) ≥
      7 / 8 - 1 / (4 * Real.log D) - 14 * Real.log D * (χ.LFunction 1).re -
        9 * (D : ℝ) ^ (-(3 / 2 : ℝ)) :=
  Splice.elementary_prime_mass hD χ hne hreal
