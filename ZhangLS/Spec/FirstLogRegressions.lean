import ZhangLS.Spec.ActualCurvatureConstraint
import ZhangLS.Spec.FirstLogMomentLower

/-! Expanded endpoint/source regressions for the actual first-moment bridge. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex

/-- Fully expanded first-moment conclusion, with the actual second L jet and
actual Euler logarithmic derivative. -/
theorem lemma171_actual_first_log_moment_original (ε : ℝ) (hε : 0 < ε) :
    ∃ D₀ : ℕ, 2 ≤ D₀ ∧ ∀ D : ℕ, D₀ ≤ D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ →
        |(∑ n ∈ Finset.Ico 1 (D ^ 4),
          ‖lemma23NuArithmeticFunction χ n‖^2 * Real.log (n : ℝ) / (n : ℝ)) +
        ((6 / Real.pi^2) * realLDerivAtOne χ ^ 2 *
          ∏ p ∈ D.primeFactors, (p : ℝ) / ((p : ℝ) + 1)) *
        ((iteratedDeriv 2 (dirichletLFunction χ) 1).re / realLDerivAtOne χ +
          2 * Real.eulerMascheroniConstant +
          (deriv (lemma171AnalyticCorrection D) 1 / lemma171AnalyticCorrection D 1).re)| < ε := by
  obtain ⟨D₀, hD₀, h⟩ := lemma171_actual_first_log_moment_uniform ε hε
  refine ⟨D₀, hD₀, ?_⟩
  intro D hD χ hA
  have hh := h D hD χ hA
  simpa [lemma171FirstLogMomentError, lemma171FirstLogMoment, lemma171Coefficient,
    lemma171MainTerm, lemma171RealSecondJet, lemma171CorrectionLogDerivative,
    show ∀ e d : ℝ, 2 * (e / 2) / d = e / d by intros; ring] using hh

example {D : ℕ} (χ : RealPrimitiveCharacter D) :
    0 ≤ ∑ n ∈ Finset.Ico 1 (D ^ 4),
      ‖lemma23NuArithmeticFunction χ n‖^2 * Real.log (n : ℝ) / (n : ℝ) :=
  lemma171_first_log_moment_nonneg χ

example {D : ℕ} (χ : RealPrimitiveCharacter D) :
    (∑ n ∈ Finset.Icc 1 (D ^ 4),
      ‖lemma23NuArithmeticFunction χ n‖^2 * Real.log (n : ℝ) / (n : ℝ)) =
    (∑ n ∈ Finset.Ico 1 (D ^ 4),
      ‖lemma23NuArithmeticFunction χ n‖^2 * Real.log (n : ℝ) / (n : ℝ)) +
      4 * Real.log (D : ℝ) * (D : ℝ)^(-4 : ℤ) :=
  lemma171_first_log_moment_endpoint χ

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 1 ≤ Real.log (D : ℝ)) (hA : NormalizedAssumptionA χ)
    (hAbs : (Real.sqrt (D : ℝ))⁻¹ ≤ Real.log (D : ℝ)^(-2013 : ℤ)) :
    (∑ n ∈ Finset.Ioc (D ^ 4) ⌊lemma23PaperP D ^ 2⌋₊,
      ‖lemma23NuArithmeticFunction χ n‖^2 / (n : ℝ) *
        lemma171LogGaussianWeight D (lemma56PaperT D / n)) ≤
      2520 * Real.log (D : ℝ)^(-2002 : ℤ) :=
  lemma171_log_middle_smoothed_tail_le χ hD hL hA hAbs

example {D : ℕ} (hD : 1 < D) (x : ℝ) (hx : 0 < x) :
    (2 * (Real.pi : ℂ) * I)⁻¹ * ∫ t : ℝ,
      ((x : ℂ)^((1 : ℂ) + (t : ℂ)*I) *
        lemma57OmegaOne D ((1 : ℂ) + (t : ℂ)*I) /
          ((1 : ℂ) + (t : ℂ)*I)^2) * I =
      ((Real.log x * zhangGaussianWeight D x +
        Real.exp (-(Real.log (D : ℝ)^15 * Real.log x)^2) /
          (2 * Real.sqrt Real.pi * Real.log (D : ℝ)^15) : ℝ) : ℂ) :=
  lemma171LogGaussianKernelVerticalIntegral_eq_weight hD zero_lt_one hx

/-- At the minimum allowed conductor, n=4 is still strictly below D^4. -/
example : 4 ∈ Finset.Ico 1 ((2 : ℕ)^4) := by norm_num

example (χ : RealPrimitiveCharacter 2) :
    Real.log 4 / 4 ≤ ∑ n ∈ Finset.Ico 1 ((2 : ℕ)^4),
      ‖lemma23NuArithmeticFunction χ n‖^2 * Real.log (n : ℝ) / (n : ℝ) :=
  lemma171_first_log_moment_ge_log_four χ (by norm_num)

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 2 ≤ D) :
    Real.log 4 / 4 ≤ ∑ n ∈ Finset.Ico 1 (D^4),
      ‖lemma23NuArithmeticFunction χ n‖^2 * Real.log (n : ℝ) / (n : ℝ) :=
  lemma171_first_log_moment_ge_log_four χ hD

end ZhangLS.Spec
