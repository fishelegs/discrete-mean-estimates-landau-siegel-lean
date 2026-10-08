import SqrtTwoPellPairs

noncomputable section

namespace PiWeightedColon.Regression

theorem approximation_pairs_exact_type : ∀ (α C η : ℝ), 0 < C → 0 ≤ η → η < 1 →
    (∀ Q : ℤ, 0 < Q → ∃ a b c d : ℤ,
      1 ≤ b ∧ 1 ≤ d ∧ (b : ℝ) ≤ C * (Q : ℝ) ∧ (d : ℝ) ≤ C * (Q : ℝ) ∧
      a * d - b * c ≠ 0 ∧
      |(b : ℝ) * α - (a : ℝ)| ≤ η / (Q : ℝ) ∧
      |(d : ℝ) * α - (c : ℝ)| ≤ η / (Q : ℝ)) →
    ∀ p q : ℤ, 0 < q → ((1 - η) / C) / (q : ℝ) ^ 2 ≤ |α - (p : ℝ) / q| :=
  approximation_pairs_lower_bound

theorem pair_constant_positive : (0 : ℝ) < (1 - (1 / 2 : ℝ)) / 9 := by
  exact approximation_pairs_constant_positive 9 (1 / 2) (by norm_num) (by norm_num)

theorem direct_sqrt_two_exact_type : ∀ p q : ℤ, 0 < q →
    1 / (4 * (q : ℝ) ^ 2) ≤ |Real.sqrt 2 - (p : ℝ) / q| :=
  sqrt_two_integer_rational_bound

theorem direct_sqrt_two_nonprimitive :
    1 / (4 * (2 : ℝ) ^ 2) ≤ |Real.sqrt 2 - (2 : ℝ) / 2| :=
  sqrt_two_integer_rational_bound 2 2 (by norm_num)

theorem direct_sqrt_two_negative_numerator :
    1 / (4 * (3 : ℝ) ^ 2) ≤ |Real.sqrt 2 - (-7 : ℝ) / 3| :=
  by simpa using sqrt_two_integer_rational_bound (-7) 3 (by norm_num)

theorem pell_first_pairs :
    sqrtTwoPellPair 0 = (1, 1) ∧ sqrtTwoPellPair 1 = (3, 2) ∧
    sqrtTwoPellPair 2 = (7, 5) ∧ sqrtTwoPellPair 3 = (17, 12) := by
  norm_num [sqrtTwoPellPair]

theorem pell_first_determinant :
    (sqrtTwoPellP 0 : ℤ) * sqrtTwoPellQ 1 -
      (sqrtTwoPellQ 0 : ℤ) * sqrtTwoPellP 1 = -1 := by
  norm_num [sqrtTwoPellP, sqrtTwoPellQ, sqrtTwoPellPair]

theorem pell_all_positive_integer_scales : ∀ Q : ℤ, 0 < Q → ∃ a b c d : ℤ,
    1 ≤ b ∧ 1 ≤ d ∧ (b : ℝ) ≤ 9 * (Q : ℝ) ∧ (d : ℝ) ≤ 9 * (Q : ℝ) ∧
    a * d - b * c ≠ 0 ∧
    |(b : ℝ) * Real.sqrt 2 - a| ≤ (1 / 2 : ℝ) / Q ∧
    |(d : ℝ) * Real.sqrt 2 - c| ≤ (1 / 2 : ℝ) / Q :=
  sqrt_two_has_approximation_pairs

theorem pell_derived_exact_type : ∀ p q : ℤ, 0 < q →
    (1 / 18 : ℝ) / (q : ℝ) ^ 2 ≤ |Real.sqrt 2 - (p : ℝ) / q| :=
  sqrt_two_pair_lower_bound

/-- Every pair condition except independence is satisfied by a rational number. -/
def DependentApproximationPairs (α C η : ℝ) : Prop :=
  ∀ Q : ℤ, 0 < Q → ∃ a b c d : ℤ,
    1 ≤ b ∧ 1 ≤ d ∧ (b : ℝ) ≤ C * (Q : ℝ) ∧ (d : ℝ) ≤ C * (Q : ℝ) ∧
    |(b : ℝ) * α - (a : ℝ)| ≤ η / (Q : ℝ) ∧
    |(d : ℝ) * α - (c : ℝ)| ≤ η / (Q : ℝ)

theorem rational_zero_dependent_pairs : DependentApproximationPairs 0 1 0 := by
  intro Q hQ
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast (show (1 : ℤ) ≤ Q by omega)
  refine ⟨0, 1, 0, 1, by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩
  · simpa using hQ1
  · simpa using hQ1
  · norm_num
  · norm_num

theorem rational_zero_no_positive_bound (κ : ℝ) (hκ : 0 < κ) :
    ¬ ApproximationLowerBound 0 κ := by
  intro h
  have hz := h 0 1 (by norm_num)
  norm_num at hz
  linarith

theorem independence_is_necessary : DependentApproximationPairs 0 1 0 ∧
    ¬ ApproximationLowerBound 0 ((1 - 0) / 1) := by
  exact ⟨rational_zero_dependent_pairs, rational_zero_no_positive_bound _ (by norm_num)⟩

theorem eta_one_constant_zero (C : ℝ) : (1 - (1 : ℝ)) / C = 0 := by simp

end PiWeightedColon.Regression
