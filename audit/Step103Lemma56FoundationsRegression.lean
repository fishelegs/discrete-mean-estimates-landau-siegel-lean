import ZhangLS.Spec.Lemma56JensenBounds

open Complex ZhangLS.Spec MeasureTheory
set_option maxHeartbeats 1000000

example {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (t : ℝ) (k : ℕ) :
    ((-1 : ℂ) ^ k * iteratedDeriv k (logDeriv (DirichletCharacter.LFunction θ))
      (lemma55JensenCenter t)) / (k.factorial : ℂ) =
      -LSeries (LSeries.logMul^[k] (lemma56Mangoldt θ)) (lemma55JensenCenter t) /
        (k.factorial : ℂ) := lemma56_actual_normalized_logDeriv_mangoldt θ t k

example {D r : ℕ} [NeZero r] (χ : RealPrimitiveCharacter D)
    (θ : DirichletCharacter ℂ r) (k : ℕ) :
    letI : NeZero (D * r) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne r)⟩
    (lemma55NormalizedLogDerivative χ 0 k + lemma55ZetaNormalizedLogDerivative 0 k +
      (lemma56NormalizedDerivative θ (D : ℝ) k +
        lemma56NormalizedDerivative (lemma44CharacterTwist χ θ) (D : ℝ) k)).re ≤ 0 :=
  lemma56_actual_four_function_logDeriv_nonpos χ θ (D : ℝ) k

example {D r : ℕ} [NeZero r] (χ : RealPrimitiveCharacter D)
    (θ : DirichletCharacter ℂ r) {R : ℝ} (hR : 0 < R) {v : ℂ} (hv : ‖v‖ ≤ 1) (J : ℕ) :
    letI : NeZero (D * r) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne r)⟩
    (∑ j ∈ Finset.range J, (lemma55FejerDetectionWeight v J j : ℂ) *
      (lemma55NormalizedLogDerivative χ 0 (2 * j + 1) + lemma55ZetaNormalizedLogDerivative 0 (2 * j + 1) +
        (lemma56NormalizedDerivative θ (-(D : ℝ)) (2 * j + 1) +
          lemma56NormalizedDerivative (lemma44CharacterTwist χ θ) (-(D : ℝ)) (2 * j + 1))) /
      (R : ℂ) ^ (j + 1)).re ≤ 0 := lemma56_actual_weighted_four_function_nonpos χ θ _ hR hv J

example {D : ℕ} (χ : RealPrimitiveCharacter D) (k n : ℕ) :
    letI : NeZero D := ⟨χ.modulus_ne_zero⟩
    lemma56TwistedPositiveCoeffs χ χ.chi k n =
      lemma55PositiveMangoldtCoeffs χ k n * χ.chi (n : ZMod D) := by
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  exact lemma56_actual_twisted_positive_coeffs χ χ.chi k n

example {D : ℕ} (χ : RealPrimitiveCharacter D) (t : ℝ) (k : ℕ) :
    letI : NeZero (D * 1) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (by norm_num)⟩
    (lemma55NormalizedLogDerivative χ 0 k + lemma55ZetaNormalizedLogDerivative 0 k +
      (lemma56NormalizedDerivative (1 : DirichletCharacter ℂ 1) t k +
        lemma56NormalizedDerivative (lemma44CharacterTwist χ (1 : DirichletCharacter ℂ 1)) t k)).re ≤ 0 :=
  lemma56_actual_four_function_logDeriv_nonpos χ (1 : DirichletCharacter ℂ 1) t k



example {D r : ℕ} [NeZero r] (χ : RealPrimitiveCharacter D)
    (θ : DirichletCharacter ℂ r) (hθ : θ.IsPrimitive) (hne : r ≠ D) :
    lemma44CharacterTwist χ θ ≠ 1 :=
  fun h => hne (lemma56_principal_twist_conductors_equal χ θ hθ h)

example {D r : ℕ} [NeZero r] (χ : RealPrimitiveCharacter D)
    (θ : DirichletCharacter ℂ r) (hθ : θ.IsPrimitive)
    (hne : (fun n : ℕ => θ (n : ZMod r)) ≠ (fun n : ℕ => χ.chi (n : ZMod D))) :
    letI : NeZero (D * r) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne r)⟩
    Differentiable ℂ (@DirichletCharacter.LFunction (D * r)
      ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne r)⟩ (lemma44CharacterTwist χ θ)) :=
  lemma56_actual_distinct_twist_entire χ θ hθ hne

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    lemma44CharacterTwist χ (1 : DirichletCharacter ℂ 1) ≠ 1 :=
  fun h => (ne_of_lt hD) (lemma56_principal_twist_conductors_equal χ
    (1 : DirichletCharacter ℂ 1) DirichletCharacter.isPrimitive_one_level_one h)



-- Faithful target equivalence only: this does not prove the prime-sum target.
example : Lemma56Target ↔ ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℕ,
    ∀ {D r : ℕ} [NeZero r] (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ r),
      D₀ ≤ D → 1 < D → NormalizedAssumptionA χ → θ.IsPrimitive →
      (r : ℝ) < Real.exp ((Real.log (D : ℝ)) ^ (11 / 10 : ℝ)) →
      (fun n : ℕ => θ (n : ZMod r)) ≠ (fun n : ℕ => χ.chi (n : ZMod D)) →
      ∀ t : ℝ, |t| ≤ (D : ℝ) →
        ‖∑ p ∈ lemma56PaperPrimes D, θ (p : ZMod r) *
          (p : ℂ) ^ (1 + I * (t : ℂ))‖ ≤
        C * (∑ p ∈ lemma56PaperPrimes D, (p : ℝ)) *
          Real.exp (-((Real.log (D : ℝ)) ^ (9 / 2 : ℝ))) := Iff.rfl

example (D p : ℕ) : p ∈ lemma56PaperPrimes D ↔
    p.Prime ∧ Real.exp ((Real.log (D : ℝ)) ^ 9) < (p : ℝ) ∧
      (p : ℝ) < Real.exp ((Real.log (D : ℝ)) ^ 9) *
        (1 + (Real.log (D : ℝ)) ^ (-68 : ℤ)) := lemma56_mem_paper_primes D p

example {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.LFunction θ s = s *
      (∫ t : ℝ in Set.Ioi 1, (∑ n ∈ Finset.Icc 1 ⌊t⌋₊, θ (n : ZMod r)) *
        (t : ℂ) ^ (-(s + 1))) := lemma56_actual_LFunction_eq_abelIntegral_re_pos θ hθ hs

example {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) (t : ℝ) :
    ‖DirichletCharacter.LFunction θ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ≤
      2 * (r : ℝ) * ‖(1 / 2 : ℂ) + (t : ℂ) * I‖ :=
  lemma56_actual_LFunction_bound_critical_line θ hθ (by simp)

example {D r : ℕ} [NeZero r] (χ : RealPrimitiveCharacter D)
    (θ : DirichletCharacter ℂ r) (hθ : θ.IsPrimitive)
    (hne : (fun n : ℕ => θ (n : ZMod r)) ≠ (fun n : ℕ => χ.chi (n : ZMod D)))
    {s : ℂ} (hs : 0 < s.re) :
    letI : NeZero (D * r) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne r)⟩
    ‖DirichletCharacter.LFunction (lemma44CharacterTwist χ θ) s‖ ≤
      ‖s‖ * (((D * r : ℕ) : ℝ) / s.re) := by
  letI : NeZero (D * r) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne r)⟩
  exact lemma56_actual_LFunction_bound_re_pos (lemma44CharacterTwist χ θ)
    (lemma56_distinct_primitive_twist_nonprincipal χ θ hθ hne) hs

example {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1)
    {t : ℝ} {z : ℂ} (hz : ‖z - lemma55JensenCenter t‖ = (3 / 2 : ℝ)) :
    ‖DirichletCharacter.LFunction θ z‖ ≤ 2 * (r : ℝ) * (7 / 2 + |t|) :=
  lemma56_actual_jensen_disk_bound θ hθ (mem_closedBall_iff_norm.mpr hz.le)

example {D : ℕ} [NeZero D] (χ : RealPrimitiveCharacter D)
    (θ : DirichletCharacter ℂ D) (hθ : θ.IsPrimitive) (hD : 1 < D)
    (hne : (fun n : ℕ => θ (n : ZMod D)) ≠ (fun n : ℕ => χ.chi (n : ZMod D)))
    (hL : 2000 ≤ lemma23PaperL D) (hDT : (D : ℝ) < lemma56PaperT D)
    {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ)) :
    letI : NeZero (D * D) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne D)⟩
    ((∑ᶠ ρ : ℂ, MeromorphicOn.divisor
      (DirichletCharacter.LFunction (lemma44CharacterTwist χ θ))
      (Metric.closedBall (2 + (t : ℂ) * I) (5 / 4 : ℝ)) ρ : ℤ) : ℝ) ≤
        24 * (Real.log (D : ℝ)) ^ (11 / 10 : ℝ) :=
  (lemma56_actual_primitive_pair_jensen_bounds χ θ hθ hD hne hD hL hDT ht).2

example {D r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1)
    (hD : 1 < D) (hL : 2000 ≤ lemma23PaperL D)
    (hr : (r : ℝ) ≤ (D : ℝ) * lemma56PaperT D) :
    (lemma56JensenMultiplicityCount θ (2 * (D : ℝ)) : ℝ) ≤
      24 * lemma23PaperL D ^ (11 / 10 : ℝ) ∧
    (lemma56JensenMultiplicityCount θ (-(2 * (D : ℝ))) : ℝ) ≤
      24 * lemma23PaperL D ^ (11 / 10 : ℝ) := by
  have ht : |2 * (D : ℝ)| ≤ 2 * (D : ℝ) := by
    rw [abs_of_nonneg (by positivity : 0 ≤ 2 * (D : ℝ))]
  exact ⟨lemma56_actual_jensen_paper_budget θ hθ hD hL hr ht,
    lemma56_actual_jensen_paper_budget θ hθ hD hL hr (by simpa only [abs_neg] using ht)⟩

example (D : ℕ) :
    ‖∑ p ∈ lemma56PaperPrimes D, (1 : DirichletCharacter ℂ 1) (p : ZMod 1) *
      (p : ℂ) ^ (1 + I * (0 : ℂ))‖ = ∑ p ∈ lemma56PaperPrimes D, (p : ℝ) :=
  lemma56_principal_paper_sum_zero_height D

#print axioms ZhangLS.Spec.lemma56_mem_paper_primes
#print axioms ZhangLS.Spec.lemma56_paper_prime_family
#print axioms ZhangLS.Spec.lemma56_prime_mass_nonneg
#print axioms ZhangLS.Spec.lemma56_paper_T_pos
#print axioms ZhangLS.Spec.lemma56_decay_pos
#print axioms ZhangLS.Spec.lemma56_principal_paper_sum_zero_height
#print axioms ZhangLS.Spec.lemma56_principal_paper_decay_requires_absorption
#print axioms ZhangLS.Spec.lemma56AbelPartialSum_measurable
#print axioms ZhangLS.Spec.lemma56_norm_abelPartialSum_le
#print axioms ZhangLS.Spec.lemma56_abelIntegral_eq_mellin
#print axioms ZhangLS.Spec.lemma56AbelMellin_differentiableAt
#print axioms ZhangLS.Spec.lemma56_actual_LFunction_eq_abelIntegral_re_pos
#print axioms ZhangLS.Spec.lemma56_actual_LFunction_bound_re_pos
#print axioms ZhangLS.Spec.lemma56_actual_LFunction_bound_critical_line
#print axioms ZhangLS.Spec.lemma56_actual_abel_integrand_integrable
#print axioms ZhangLS.Spec.lemma56_actual_abelIntegral_norm_bound
#print axioms ZhangLS.Spec.lemma56_actual_LFunction_bound_re_gt_one
#print axioms ZhangLS.Spec.lemma56_character_sum_one_period_eq_zero
#print axioms ZhangLS.Spec.lemma56_character_sum_nat_one_period_eq_zero
#print axioms ZhangLS.Spec.lemma56_character_sum_block_eq_zero
#print axioms ZhangLS.Spec.lemma56_character_norm_sum_range_le_modulus
#print axioms ZhangLS.Spec.lemma56_character_norm_sum_Icc_le_modulus
#print axioms ZhangLS.Spec.lemma56_character_sum_Icc_isBigO_one
#print axioms ZhangLS.Spec.lemma56_actual_LFunction_eq_abelIntegral
#print axioms ZhangLS.Spec.lemma56_actual_jensen_disk_bound
#print axioms ZhangLS.Spec.lemma56_actual_L_analyticOnNhd
#print axioms ZhangLS.Spec.lemma56_actual_jensen_center_lower_bound
#print axioms ZhangLS.Spec.lemma56_actual_jensen_center_ne_zero
#print axioms ZhangLS.Spec.lemma56_actual_jensen_multiplicity_bound
#print axioms ZhangLS.Spec.lemma56_actual_jensen_paper_budget
#print axioms ZhangLS.Spec.lemma56_actual_primitive_pair_jensen_bounds
#print axioms ZhangLS.Spec.lemma56_actual_mangoldt_abscissa
#print axioms ZhangLS.Spec.lemma56_actual_logDeriv_mangoldt
#print axioms ZhangLS.Spec.lemma56_actual_higher_logDeriv_mangoldt
#print axioms ZhangLS.Spec.lemma56_actual_normalized_logDeriv_mangoldt
#print axioms ZhangLS.Spec.lemma56_actual_log_power_summable
#print axioms ZhangLS.Spec.lemma56_nonnegative_majorant_series_bound
#print axioms ZhangLS.Spec.lemma56_log_power_twist
#print axioms ZhangLS.Spec.lemma56_actual_twisted_positive_coeffs
#print axioms ZhangLS.Spec.lemma56_actual_twisted_coeff_norm_bound
#print axioms ZhangLS.Spec.lemma56_actual_twisted_coeffs_summable
#print axioms ZhangLS.Spec.lemma56_actual_twisted_pair_mangoldt
#print axioms ZhangLS.Spec.lemma56_actual_four_function_logDeriv_nonpos
#print axioms ZhangLS.Spec.lemma56_actual_weighted_four_function_nonpos
#print axioms ZhangLS.Spec.lemma56_lseries_term_square_bound
#print axioms ZhangLS.Spec.lemma56_actual_L_distance_to_one_bound
#print axioms ZhangLS.Spec.lemma56_actual_L_norm_lower_bound
#print axioms ZhangLS.Spec.lemma56_principal_one_primitive
#print axioms ZhangLS.Spec.lemma56_principal_one_apply_nat
#print axioms ZhangLS.Spec.lemma56_principal_zero_height_prime_sum
#print axioms ZhangLS.Spec.lemma56_principal_zero_height_prime_sum_norm
#print axioms ZhangLS.Spec.lemma56_principal_decay_requires_absorption
#print axioms ZhangLS.Spec.lemma56_principal_one_differs_from_real_character
#print axioms ZhangLS.Spec.lemma56_principal_twist_lifts_equal
#print axioms ZhangLS.Spec.lemma56_principal_twist_conductors_equal
#print axioms ZhangLS.Spec.lemma56_principal_twist_characters_equal
#print axioms ZhangLS.Spec.lemma56_distinct_primitive_twist_nonprincipal
#print axioms ZhangLS.Spec.lemma56_primitive_positive_level_nonprincipal
#print axioms ZhangLS.Spec.lemma56_actual_distinct_twist_entire
#print axioms ZhangLS.Spec.lemma56_actual_nonprincipal_primitive_entire
