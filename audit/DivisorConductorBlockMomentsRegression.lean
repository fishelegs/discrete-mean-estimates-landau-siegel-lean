import ZhangLS.Spec.DivisorConductorBlockMomentsCauchy

set_option autoImplicit false
namespace ZhangLS.Spec.DivisorConductorBlockMomentsRegression
open ZhangLS.Spec.DivisorConductorBlockMoments Complex Finset
open scoped Classical ComplexConjugate

theorem conductor_zero_excluded (R : ℝ) : 0 ∉ blockModuli R := by
  simp [mem_blockModuli]

theorem conductor_level_one_retained : 1 ∈ blockModuli 1 := by
  rw [mem_blockModuli]
  norm_num

theorem conductor_upper_open : 2 ∉ blockModuli 1 := by
  rw [mem_blockModuli]
  norm_num

theorem conductor_fractional_lower_included : 2 ∈ blockModuli (3 / 2) := by
  rw [mem_blockModuli]
  norm_num

theorem conductor_fractional_upper_excluded : 3 ∉ blockModuli (3 / 2) := by
  rw [mem_blockModuli]
  norm_num

theorem conductor_real_lower_excluded : 1 ∉ blockModuli (3 / 2) := by
  rw [mem_blockModuli]
  norm_num

theorem zero_long_index_excluded (h : ℕ) (X : ℝ) : 0 ∉ longIndices h X := by
  intro hl
  exact (Nat.lt_irrefl 0) (longIndices_positive hl)

theorem long_lower_inclusive : 2 ∈ longIndices 1 4 := by
  rw [mem_longIndices (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num

theorem long_upper_inclusive : 32 ∈ longIndices 1 4 := by
  rw [mem_longIndices (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num

theorem long_below_lower_excluded : 1 ∉ longIndices 1 4 := by
  rw [mem_longIndices (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num

theorem long_above_upper_excluded : 33 ∉ longIndices 1 4 := by
  rw [mem_longIndices (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num

theorem mask_removes_lower_endpoint : 2 ∉ longIndices 2 4 := by
  rw [mem_longIndices (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num

theorem mask_keeps_coprime : 3 ∈ longIndices 2 4 := by
  rw [mem_longIndices (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num

theorem fractional_upper_inclusive : 10 ∈ longIndices 1 (5 / 4) := by
  rw [mem_longIndices (by norm_num : (0 : ℝ) ≤ 5 / 4)]
  norm_num

theorem fractional_upper_excluded : 11 ∉ longIndices 1 (5 / 4) := by
  rw [mem_longIndices (by norm_num : (0 : ℝ) ≤ 5 / 4)]
  norm_num

theorem fractional_lower_excluded : 1 ∉ longIndices 1 (5 / 2) := by
  rw [mem_longIndices (by norm_num : (0 : ℝ) ≤ 5 / 2)]
  norm_num

theorem fractional_lower_next_integer : 2 ∈ longIndices 1 (5 / 2) := by
  rw [mem_longIndices (by norm_num : (0 : ℝ) ≤ 5 / 2)]
  norm_num

theorem coefficient_zero_bound : CoefficientBound 0 (fun _ => (0 : ℂ)) := by
  intro n hn
  simp

theorem zero_constant_allows_arbitrary_b_zero :
    CoefficientBound 0 (fun n => if n = 0 then (7 : ℂ) else 0) := by
  intro n hn
  simp [Nat.ne_of_gt hn]

theorem coefficient_bound_zero_forces_zero {b : ℕ → ℂ} (hb : CoefficientBound 0 b) :
    ∀ n : ℕ, 0 < n → b n = 0 := by
  intro n hn
  apply norm_eq_zero.mp
  exact le_antisymm (by simpa using hb n hn) (norm_nonneg _)

theorem zero_polynomial (d h r : ℕ) (X t : ℝ) (θ : DirichletCharacter ℂ r) :
    longPolynomial d h X (fun _ => 0) r θ t = 0 := by
  simp [longPolynomial]

theorem zero_block (R X t : ℝ) (d h : ℕ) :
    blockMoment R (fun r θ => longPolynomial d h X (fun _ => 0) r θ t) = 0 := by
  simp [blockMoment, zero_polynomial]

theorem zero_constant_allowed (t : ℝ) :
    blockMoment 1 (fun r θ => longPolynomial 1 1 1 (fun _ => 0) r θ t) ≤
      32 * (33 + Real.pi ^ 2) * (0 : ℝ) ^ 2 * (lemma34Tau 5 1 : ℝ) ^ 2 *
        (1 + Real.log (8 * 1)) ^ 25 :=
  long_block_bound (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    coefficient_zero_bound 1 1 (by decide) t

theorem positive_imaginary_phase_norm (t : ℝ) : ‖(2 : ℂ) ^ (I * (t : ℂ))‖ = 1 :=
  imaginary_power_norm t (by decide)

theorem exact_prime_minus_one : primeCoefficient 0 2 = 1 := by
  norm_num [primeCoefficient]

theorem positive_index_interface (d h : ℕ+) (X t : ℝ) (b : ℕ → ℂ)
    (r : ℕ) (θ : DirichletCharacter ℂ r) :
    positiveLongPolynomial d h X b r θ t = longPolynomial (d : ℕ) (h : ℕ) X b r θ t :=
  positiveLongPolynomial_eq d h X b r θ t

theorem actual_prime_phase_norm (t : ℝ) : ‖primeCoefficient t 2‖ = 1 := by
  simpa using primeCoefficient_norm t (by decide : 0 < 2)

theorem empty_prime_polynomial (r : ℕ) (θ : DirichletCharacter ℂ r) (t : ℝ) :
    primePolynomial ∅ r θ t = 0 := by simp [primePolynomial]

theorem nonunit_prime_vanishes (θ : DirichletCharacter ℂ 2) (t : ℝ) :
    primePolynomial {2} 2 θ t = 0 := by
  have hz : θ (2 : ZMod 2) = 0 := MulChar.map_nonunit θ (by
    change ¬IsUnit ((2 : ℕ) : ZMod 2)
    rw [ZMod.isUnit_iff_coprime]
    decide)
  simp [primePolynomial, hz]

theorem singleton_prime_bound (t : ℝ) :
    blockMoment (3 / 2) (fun r θ => primePolynomial {2} r θ t) ≤
      blockConstant * ((3 / 2 : ℝ) ^ 2 + 1) * 1 ^ 3 := by
  apply prime_block_bound (by norm_num) (by norm_num)
  · intro p hp
    simp only [mem_singleton] at hp
    subst p
    decide
  · intro p hp
    simp only [mem_singleton] at hp
    subst p
    norm_num

theorem finite_cauchy_zero_endpoint (R X t : ℝ) (d h : ℕ) :
    mixedBlock R (fun r θ => longPolynomial d h X (fun _ => 0) r θ t)
      (fun r θ => primePolynomial ∅ r θ t) = 0 := by
  simp [mixedBlock, zero_polynomial]

end ZhangLS.Spec.DivisorConductorBlockMomentsRegression
