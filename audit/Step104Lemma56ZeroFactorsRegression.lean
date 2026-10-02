import ZhangLS.Spec.Lemma56WeakZeroExclusion

#print axioms ZhangLS.Spec.lemma56_actual_analytic_order_finite
#print axioms ZhangLS.Spec.lemma56_actual_local_divisor_eq_order
#print axioms ZhangLS.Spec.lemma56_mem_actual_local_zero_finset
#print axioms ZhangLS.Spec.lemma56_actual_local_zero_order_pos
#print axioms ZhangLS.Spec.lemma56_actual_multiplicity_count_eq_sum_orders
#print axioms ZhangLS.Spec.lemma56_actual_local_zero_card_bound
#print axioms ZhangLS.Spec.lemma56_actual_meromorphic_order_eq_nat
#print axioms ZhangLS.Spec.lemma56_actual_zero_factor_analytic
#print axioms ZhangLS.Spec.lemma56_actual_zero_factor_order
#print axioms ZhangLS.Spec.lemma56_actual_zero_removed_order
#print axioms ZhangLS.Spec.lemma56_actual_zero_removed_analytic
#print axioms ZhangLS.Spec.lemma56_actual_zero_removed_ne_zero
#print axioms ZhangLS.Spec.lemma56_actual_zero_removed_eq_quotient
#print axioms ZhangLS.Spec.lemma56_actual_zero_factorization
#print axioms ZhangLS.Spec.lemma56_actual_zero_factor_eq_product
#print axioms ZhangLS.Spec.lemma56_actual_local_multiplicity_eq_count
#print axioms ZhangLS.Spec.lemma56_actual_zero_factor_center_bound
#print axioms ZhangLS.Spec.lemma56_actual_zero_factor_outer_lower_bound
#print axioms ZhangLS.Spec.lemma56_actual_zero_factor_outer_ne_zero
#print axioms ZhangLS.Spec.lemma56_actual_local_multiplicity_bound
#print axioms ZhangLS.Spec.lemma56_actual_zero_removed_outer_bound
#print axioms ZhangLS.Spec.lemma56_actual_zero_removed_closed_disk_bound
#print axioms ZhangLS.Spec.lemma56_actual_zero_removed_center_lower_bound
#print axioms ZhangLS.Spec.lemma56_jensen_log_size_pos
#print axioms ZhangLS.Spec.lemma56_zero_removed_ratio_bound_gt_one
#print axioms ZhangLS.Spec.lemma56_actual_zero_removed_ratio_bound
#print axioms ZhangLS.Spec.lemma56_actual_zero_removed_log_ratio_bound
#print axioms ZhangLS.Spec.lemma56_actual_zero_removed_log_exists
#print axioms ZhangLS.Spec.lemma56_actual_zero_removed_log_hasDerivAt
#print axioms ZhangLS.Spec.lemma56_actual_zero_removed_log_closed_bound
#print axioms ZhangLS.Spec.lemma56_actual_zero_removed_log_cauchy_bound
#print axioms ZhangLS.Spec.lemma56_actual_zero_factor_logDeriv
#print axioms ZhangLS.Spec.lemma56_actual_local_logDeriv_formula
#print axioms ZhangLS.Spec.lemma56_actual_zero_removed_higher_logDeriv_bound
#print axioms ZhangLS.Spec.lemma56_actual_higher_logDeriv_remainder_eq
#print axioms ZhangLS.Spec.lemma56_actual_higher_logDeriv_remainder_bound
#print axioms ZhangLS.Spec.lemma56_actual_normalized_logDeriv_remainder_bound
#print axioms ZhangLS.Spec.lemma56_actual_logDeriv_remainder_sum_bound
#print axioms ZhangLS.Spec.lemma56_actual_local_zero_higher_derivative
#print axioms ZhangLS.Spec.lemma56_actual_power_sum_remainder_norm_eq
#print axioms ZhangLS.Spec.lemma56_actual_power_sum_remainder_bound
#print axioms ZhangLS.Spec.lemma56_actual_power_sum_remainder_sum_bound
#print axioms ZhangLS.Spec.lemma56_actual_normalized_odd_power_error_bound
#print axioms ZhangLS.Spec.lemma56_actual_weighted_power_error_uniform_bound
#print axioms ZhangLS.Spec.lemma56_actual_weighted_real_power_error_uniform_bound
#print axioms ZhangLS.Spec.lemma56_actual_zero_re_lt_one
#print axioms ZhangLS.Spec.lemma56_actual_local_zero_center_distance
#print axioms ZhangLS.Spec.lemma56_actual_inverse_square_norm_bounds
#print axioms ZhangLS.Spec.lemma56_actual_subset_max_inverse_square
#print axioms ZhangLS.Spec.lemma56_normalized_inverse_square_power_sum
#print axioms ZhangLS.Spec.lemma56_actual_subset_weighted_power_detection
#print axioms ZhangLS.Spec.lemma56_actual_subset_weighted_detection_log_bound
#print axioms ZhangLS.Spec.lemma56_near_one_zero_in_own_local_disk
#print axioms ZhangLS.Spec.lemma56_near_one_zero_inverse_square_lower_bound
#print axioms ZhangLS.Spec.lemma56_actual_mixed_remaining_error_bound
#print axioms ZhangLS.Spec.lemma56_actual_mixed_removed_derivative_nonpos
#print axioms ZhangLS.Spec.lemma56_actual_mixed_remaining_real_upper_bound

open Complex Metric Set ZhangLS.Spec

example {q : ℕ} [NeZero q] (θ : DirichletCharacter ℂ q) (hθ : θ ≠ 1) (t : ℝ) (z : ℂ) :
    DirichletCharacter.LFunction θ z = lemma56LocalZeroFactor θ t z * lemma56ZeroRemovedL θ t z :=
  lemma56_actual_zero_factorization θ hθ t z

example {q : ℕ} [NeZero q] (θ : DirichletCharacter ℂ q) (hθ : θ ≠ 1)
    {t : ℝ} {ρ : ℂ} (hρ : ‖ρ - lemma55JensenCenter t‖ = (5 / 4 : ℝ))
    (hzero : DirichletCharacter.LFunction θ ρ = 0) :
    lemma56ZeroRemovedL θ t ρ ≠ 0 ∧ lemma56LocalZeroFactor θ t ρ = 0 := by
  have hQ := lemma56_actual_zero_removed_ne_zero θ hθ (mem_closedBall_iff_norm.mpr hρ.le)
  refine ⟨hQ, ?_⟩
  have he := lemma56_actual_zero_factorization θ hθ t ρ
  rw [hzero] at he
  exact (mul_eq_zero.mp he.symm).resolve_right hQ

example {q : ℕ} [NeZero q] (θ : DirichletCharacter ℂ q) (hθ : θ ≠ 1) (t : ℝ) (n : ℕ) :
    ‖((-1 : ℂ) ^ n * iteratedDeriv n (logDeriv (DirichletCharacter.LFunction θ))
      (lemma55JensenCenter t) / (n.factorial : ℂ)) -
      (∑ ρ ∈ lemma56LocalZeroFinset θ t, (analyticOrderNatAt (DirichletCharacter.LFunction θ) ρ : ℂ) /
        (lemma55JensenCenter t - ρ) ^ (n + 1))‖ ≤
      450 * ((n : ℝ) + 1) * Real.log (8 * (q : ℝ) * (7 / 2 + |t|)) * (8 / 9 : ℝ) ^ (n + 1) :=
  lemma56_actual_power_sum_remainder_bound θ hθ n

example {D q : ℕ} [NeZero q] (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ q)
    (hθ : θ ≠ 1) (htwist : lemma44CharacterTwist χ θ ≠ 1)
    (hD : 1 < D) (hL : 2000 ≤ Real.log (D : ℝ)) (t : ℝ)
    {β R : ℝ} (hβ : β ≤ 1) (hzero : dirichletLFunction χ (β : ℂ) = 0)
    (hderiv : deriv (dirichletLFunction χ) (β : ℂ) ≠ 0)
    (hmem : (β : ℂ) ∈ lemma55LocalZeroFinset χ 0) (hR : 0 < R)
    (hlower : ((1 + 2 / Real.log (D : ℝ))⁻¹) ^ 2 ≤ R)
    (hUlower : ((1 + 2 / (Real.log (D : ℝ)) ^ 4)⁻¹) ^ 2 ≤ R)
    {v : ℂ} (hv : ‖v‖ ≤ 1) (J : ℕ) :
    letI : NeZero (D * q) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne q)⟩
    (lemma56MixedRemainingPower χ θ t R (β : ℂ) v J).re ≤
      187200 * Real.log (D : ℝ) + 36000 * Real.log (8 * (q : ℝ) * (7 / 2 + |t|)) +
        36000 * Real.log (8 * ((D * q : ℕ) : ℝ) * (7 / 2 + |t|)) +
          2 * (1 - β) * (J : ℝ) * ((J : ℝ) + 1) * Real.exp (4 * (J : ℝ) / (Real.log (D : ℝ)) ^ 4) := by
  have hLp : 0 < Real.log (D : ℝ) := by linarith
  exact lemma56_actual_mixed_remaining_real_upper_bound χ θ hθ htwist hD hL t hβ hzero hderiv hmem hR
    hlower (pow_pos hLp 4) hUlower hv J

-- Expanded original assumptions, actual L-function, and closed height endpoints.
example : ∃ D₀ : ℕ, ∀ {D q : ℕ} [NeZero q] (χ : RealPrimitiveCharacter D)
    (θ : DirichletCharacter ℂ q), D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
    θ.IsPrimitive → 1 < q → (q : ℝ) < Real.exp ((Real.log (D : ℝ)) ^ (11 / 10 : ℝ)) →
    (fun n : ℕ => θ (n : ZMod q)) ≠ (fun n : ℕ => χ.chi (n : ZMod D)) →
    ∀ s : ℂ, 1 - 2 / (Real.log (D : ℝ)) ^ 4 < s.re → |s.im| ≤ 2 * (D : ℝ) →
      DirichletCharacter.LFunction θ s ≠ 0 := by
  obtain ⟨D₀, hD₀⟩ := lemma56_uniform_primitive_weak_zero_exclusion
  refine ⟨D₀, ?_⟩
  intro D q _ χ θ hDN hD hA hθ hq hqT hne s hre ht
  exact hD₀ χ θ hDN hD hA hθ hq hqT hne s ⟨hre, ht⟩

example {D q : ℕ} [NeZero q] (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ q)
    (hD : 1 < D) (hL : 2000 ≤ Real.log (D : ℝ))
    (hC : lemma56RepulsionErrorConstant ≤ Real.log (D : ℝ))
    (hq : (q : ℝ) < lemma56PaperT D) (hθ : θ ≠ 1) (htwist : lemma44CharacterTwist χ θ ≠ 1)
    {β : ℝ} (hβ : 0 < 1 - β) (hclose : 1 - β ≤ 64 * Real.log (D : ℝ) ^ (-2022 : ℤ))
    (hzero : dirichletLFunction χ (β : ℂ) = 0) (hderiv : deriv (dirichletLFunction χ) (β : ℂ) ≠ 0)
    (hmem : (β : ℂ) ∈ lemma55LocalZeroFinset χ 0) {s : ℂ}
    (hre : 1 - 2 / (Real.log (D : ℝ)) ^ 4 < s.re) (him : s.im = 2 * (D : ℝ)) :
    DirichletCharacter.LFunction θ s ≠ 0 := by
  apply lemma56_actual_weak_zero_exclusion χ θ hD hL hC hq hθ htwist hβ hclose hzero hderiv hmem s
  exact ⟨hre, by rw [him, abs_of_nonneg (by positivity)]⟩

example {D q : ℕ} [NeZero q] (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ q)
    (hD : 1 < D) (hL : 2000 ≤ Real.log (D : ℝ))
    (hC : lemma56RepulsionErrorConstant ≤ Real.log (D : ℝ))
    (hq : (q : ℝ) < lemma56PaperT D) (hθ : θ ≠ 1) (htwist : lemma44CharacterTwist χ θ ≠ 1)
    {β : ℝ} (hβ : 0 < 1 - β) (hclose : 1 - β ≤ 64 * Real.log (D : ℝ) ^ (-2022 : ℤ))
    (hzero : dirichletLFunction χ (β : ℂ) = 0) (hderiv : deriv (dirichletLFunction χ) (β : ℂ) ≠ 0)
    (hmem : (β : ℂ) ∈ lemma55LocalZeroFinset χ 0) {s : ℂ}
    (hre : 1 - 2 / (Real.log (D : ℝ)) ^ 4 < s.re) (him : s.im = -(2 * (D : ℝ))) :
    DirichletCharacter.LFunction θ s ≠ 0 := by
  apply lemma56_actual_weak_zero_exclusion χ θ hD hL hC hq hθ htwist hβ hclose hzero hderiv hmem s
  exact ⟨hre, by rw [him, abs_neg, abs_of_nonneg (by positivity)]⟩

-- The two height-zero families and the two theta families retain their tags.
example {D q : ℕ} [NeZero q] (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ q)
    (β ρ : ℂ) : (⟨2, ρ⟩ : Lemma56TaggedZero) ∈ lemma56FourZeroFinset χ θ 0 β ↔
      ρ ∈ lemma56LocalZeroFinset θ 0 := by
  simpa [lemma56ZeroFamily] using lemma56_mem_four_zero_finset χ θ 0 β ⟨2, ρ⟩

example {D : ℕ} [NeZero D] (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ D)
    (β ρ : ℂ) :
    letI : NeZero (D * D) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne D)⟩
    (⟨3, ρ⟩ : Lemma56TaggedZero) ∈ lemma56FourZeroFinset χ θ 0 β ↔
      ρ ∈ lemma56LocalZeroFinset (lemma44CharacterTwist χ θ) 0 := by
  simpa [lemma56ZeroFamily] using lemma56_mem_four_zero_finset χ θ 0 β ⟨3, ρ⟩

example {D q : ℕ} [NeZero q] (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ q)
    (hD : 1 < D) (hL : 2000 ≤ Real.log (D : ℝ)) (hq : (q : ℝ) < lemma56PaperT D)
    (hθ : θ ≠ 1) (htwist : lemma44CharacterTwist χ θ ≠ 1) {t : ℝ}
    (ht : |t| ≤ 2 * (D : ℝ)) (β : ℂ) :
    (∑ a ∈ lemma56FourZeroFinset χ θ t β,
      (analyticOrderNatAt (lemma56FamilyFunction χ θ a.1) a.2 : ℝ)) ≤
      79 * (Real.log (D : ℝ)) ^ (11 / 10 : ℝ) :=
  lemma56_actual_four_zero_order_sum_bound χ θ hD hL hq hθ htwist ht β

example {L δ : ℝ} (hL : 2000 ≤ L) (hC : lemma56RepulsionErrorConstant ≤ L)
    (hδ : 0 ≤ δ) (hclose : δ ≤ 64 * L ^ (-2022 : ℤ)) :
    475200 * L ^ (11 / 10 : ℝ) +
      2 * δ * (⌈2000000 * L ^ (11 / 10 : ℝ)⌉₊ : ℝ) *
        ((⌈2000000 * L ^ (11 / 10 : ℝ)⌉₊ : ℝ) + 1) *
        Real.exp (4 * (⌈2000000 * L ^ (11 / 10 : ℝ)⌉₊ : ℝ) / L ^ 4) <
      (⌈2000000 * L ^ (11 / 10 : ℝ)⌉₊ : ℝ) / 4 - 79 * L ^ (11 / 10 : ℝ) :=
  lemma56_repulsion_strict_budget hL hC hδ hclose

#print axioms ZhangLS.Spec.lemma56_tagged_normalized_power_sum
#print axioms ZhangLS.Spec.lemma56_actual_weighted_tagged_power_sum_eq
#print axioms ZhangLS.Spec.lemma56_actual_weighted_tagged_real_sum_eq
#print axioms ZhangLS.Spec.lemma56_actual_common_maximum_weighted_detection
#print axioms ZhangLS.Spec.lemma56_actual_near_one_zero_four_detected
#print axioms ZhangLS.Spec.lemma56_mem_four_zero_finset
#print axioms ZhangLS.Spec.lemma56_actual_tagged_zero_order_pos
#print axioms ZhangLS.Spec.lemma56_actual_tagged_inverse_square_bounds
#print axioms ZhangLS.Spec.lemma56_actual_jensen_log_paper_budget
#print axioms ZhangLS.Spec.lemma56_actual_local_order_sum_paper_budget
#print axioms ZhangLS.Spec.lemma56_actual_four_zero_order_sum_bound
#print axioms ZhangLS.Spec.lemma56_actual_tagged_power_sum_eq
#print axioms ZhangLS.Spec.lemma56_repulsion_error_constant_pos
#print axioms ZhangLS.Spec.lemma56_repulsion_scale_bounds
#print axioms ZhangLS.Spec.lemma56_repulsion_degree_bounds
#print axioms ZhangLS.Spec.lemma56_repulsion_exponential_cost
#print axioms ZhangLS.Spec.lemma56_repulsion_exceptional_cost_bound
#print axioms ZhangLS.Spec.lemma56_repulsion_strict_budget
#print axioms ZhangLS.Spec.lemma56_uniform_repulsion_modulus_threshold
#print axioms ZhangLS.Spec.lemma56_actual_mixed_paper_upper_bound
#print axioms ZhangLS.Spec.lemma56_weak_region_geometry
#print axioms ZhangLS.Spec.lemma56_actual_weak_zero_exclusion
#print axioms ZhangLS.Spec.lemma56_actual_exceptional_zero_local
#print axioms ZhangLS.Spec.lemma56_uniform_primitive_weak_zero_exclusion
