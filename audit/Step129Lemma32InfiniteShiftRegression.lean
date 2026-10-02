import ZhangLS.Spec.Lemma32OriginalCircle
import ZhangLS.Spec.Lemma32ActualSeriesIdentity
import ZhangLS.Spec.Lemma32SmoothingWindow
import ZhangLS.Spec.Lemma32ActualTailReduction
import ZhangLS.Spec.Lemma32RamificationPowerSaving
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex Filter Topology Set
open scoped Classical
set_option maxHeartbeats 2000000

example {D : ℕ} (χ : RealPrimitiveCharacter D) :
    AnalyticOnNhd ℂ (fun s : ℂ => (∏ p ∈ D.primeFactors,
      (1-Complex.exp (-s*(Real.log (p : ℝ) : ℂ)))^4)*
      (∏' p : Nat.Primes, lemma32RegularLocalPolynomial χ p.val
        (Complex.exp (-s*(Real.log (p.val : ℝ) : ℂ))))) {s : ℂ | 1/2 < s.re} :=
    lemma32_analytic_correction_analyticOnNhd χ

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hL : 3 ≤ Real.log (D : ℝ))
    (s : ℂ) (hs : ‖s-1‖ ≤ Real.log (D : ℝ)^(-2024 : ℤ)) :
    ‖(∏ p ∈ D.primeFactors, (1-Complex.exp (-s*(Real.log (p : ℝ) : ℂ)))^4)*
      (∏' p : Nat.Primes, lemma32RegularLocalPolynomial χ p.val
        (Complex.exp (-s*(Real.log (p.val : ℝ) : ℂ))))‖ ≤
      Real.exp (7659*∑' p : Nat.Primes, (p.val : ℝ)^((-2 : ℝ)*(3/4))) :=
    lemma32_analytic_correction_residue_disk_bound χ hL s hs

example {D : ℕ} (hL : 3 ≤ Real.log (D : ℝ)) (s : ℂ)
    (hs : ‖s-1‖ ≤ Real.log (D : ℝ)^(-2024 : ℤ)) :
    3/4 ≤ s.re ∧ |s.im| * Real.log (D : ℝ) ≤ 1 ∧
      ‖s-1‖ ≤ 1/(4*Real.log (D : ℝ)) := lemma32_residue_disk_parameters hL s hs

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2 ≤ Real.log (D : ℝ)) (s : ℂ) (hs : ‖s-1‖ ≤ 1/(4*Real.log (D : ℝ))) :
    ‖deriv (dirichletLFunction χ) s‖ ≤ 16*Real.exp 1*Real.log (D : ℝ)^2 :=
    lemma32_actual_first_derivative_bound χ hD hL hs

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hA : NormalizedAssumptionA χ) :
    ‖dirichletLFunction χ 1‖ ≤ Real.log (D : ℝ)^(-2022 : ℤ) :=
    lemma32_actual_value_at_one_small χ hD hA

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 3 ≤ Real.log (D : ℝ)) (hA : NormalizedAssumptionA χ)
    (s : ℂ) (hs : ‖s-1‖ ≤ Real.log (D : ℝ)^(-2024 : ℤ)) :
    ‖dirichletLFunction χ s‖ ≤ (1+16*Real.exp 1)*Real.log (D : ℝ)^(-2022 : ℤ) :=
    lemma32_actual_L_residue_disk_small χ hD hL hA s hs

example : 0 < lemma32CircleConstant := lemma32_circle_constant_pos

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 3 ≤ Real.log (D : ℝ)) (hA : NormalizedAssumptionA χ) :
    ‖(2*Real.pi*Complex.I : ℂ)⁻¹ * circleIntegral
      (fun w : ℂ =>
        ((∏ p ∈ D.primeFactors, (1-Complex.exp (-(1+w)*(Real.log (p : ℝ) : ℂ)))^4)*
          (∏' p : Nat.Primes, lemma32RegularLocalPolynomial χ p.val
            (Complex.exp (-(1+w)*(Real.log (p.val : ℝ) : ℂ)))))*
        (riemannZeta (1+w)*dirichletLFunction χ (1+w))^8*
        (((D : ℂ)^((8 : ℂ)*w)-(D : ℂ)^((4 : ℂ)*w))*Complex.Gamma w))
      0 (Real.log (D : ℝ)^(-2024 : ℤ))‖ ≤
      lemma32CircleConstant*Real.log (D : ℝ)^(-2007 : ℤ) :=
    lemma32_original_normalized_circle_integral_bound χ hD hL hA

example {D : ℕ} (χ : RealPrimitiveCharacter D) (n : ℕ) :
    ‖lemma23NuArithmeticFunction χ n‖^2*(lemma34Tau 2 n : ℝ)^2 ≤ (lemma34Tau 16 n : ℝ) :=
    lemma32_actual_coefficient_le_tau_sixteen χ n

example {D : ℕ} (χ : RealPrimitiveCharacter D) (s : ℂ) (hs : 1 < s.re) :
    LSeriesSummable (fun n => (‖lemma23NuArithmeticFunction χ n‖^2*(lemma34Tau 2 n : ℝ)^2 : ℂ)) s :=
    by simpa only [lemma32ActualCoefficient,lemma32WeightedDirichletSeries,
      Complex.ofReal_mul,Complex.ofReal_pow] using lemma32_actual_weighted_lseries_summable χ s hs

example {D : ℕ} (χ : RealPrimitiveCharacter D) (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => ∑' e : ℕ,
      LSeries.term (fun n => (‖lemma23NuArithmeticFunction χ n‖^2*(lemma34Tau 2 n : ℝ)^2 : ℂ)) s (p.val^e))
      (LSeries (fun n => (‖lemma23NuArithmeticFunction χ n‖^2*(lemma34Tau 2 n : ℝ)^2 : ℂ)) s) :=
    by simpa only [lemma32ActualCoefficient,lemma32WeightedDirichletSeries,
      Complex.ofReal_mul,Complex.ofReal_pow] using lemma32_actual_weighted_euler_hasProd χ s hs

example {D : ℕ} (χ : RealPrimitiveCharacter D) (s : ℂ) (hs : 1 < s.re) :
    LSeries (fun n => (‖lemma23NuArithmeticFunction χ n‖^2*(lemma34Tau 2 n : ℝ)^2 : ℂ)) s =
      ((∏ p ∈ D.primeFactors, (1-Complex.exp (-s*(Real.log (p : ℝ) : ℂ)))^4)*
        (∏' p : Nat.Primes, lemma32RegularLocalPolynomial χ p.val
          (Complex.exp (-s*(Real.log (p.val : ℝ) : ℂ)))))*
      (riemannZeta s*dirichletLFunction χ s)^8 :=
    by simpa only [lemma32ActualCoefficient,lemma32WeightedDirichletSeries,
      Complex.ofReal_mul,Complex.ofReal_pow] using lemma32_actual_weighted_series_identity χ s hs

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) (hL : 3 ≤ Real.log (D : ℝ)) :
    CircleIntegrable (fun w : ℂ => lemma32AnalyticCorrection χ (1+w)*
      (riemannZeta (1+w)*dirichletLFunction χ (1+w))^8*
      (lemma32SmoothingDifference (Real.log (D : ℝ)) w*Complex.Gamma w))
      0 (Real.log (D : ℝ)^(-2024 : ℤ)) := lemma32_actual_circle_integrable χ hD hL

example (t : ℝ) : ‖Complex.Gamma (1+(t : ℂ)*Complex.I)‖ ≤ 3/(1+t^2) :=
    lemma32_gamma_one_vertical_bound t

example (x : ℝ) (hx : 0 < x) : mellinInv 1 Complex.Gamma x = (Real.exp (-x) : ℂ) :=
    lemma32_actual_Gamma_mellin_inversion x hx

example {D : ℕ} (χ : RealPrimitiveCharacter D) (B : ℝ) (hB : 0 < B) :
    ((1/(2*Real.pi) : ℝ) : ℂ)*(∫ t : ℝ, lemma32AnalyticCorrection χ (2+(t : ℂ)*Complex.I)*
      (riemannZeta (2+(t : ℂ)*Complex.I)*dirichletLFunction χ (2+(t : ℂ)*Complex.I))^8*
      Complex.exp ((1+(t : ℂ)*Complex.I)*(Real.log B : ℂ))*Complex.Gamma (1+(t : ℂ)*Complex.I)) =
      lemma32SmoothedWeightedSeries χ B := lemma32_actual_full_Gamma_mellin χ B hB

example {D : ℕ} (χ : RealPrimitiveCharacter D) :
    MeasureTheory.Integrable (fun t : ℝ => lemma32CircleIntegrand χ (1+(t : ℂ)*Complex.I)) :=
    lemma32_actual_original_right_Gamma_integrable χ

example {D : ℕ} (χ : RealPrimitiveCharacter D) :
    ((1/(2*Real.pi) : ℝ) : ℂ)*(∫ t : ℝ, lemma32CircleIntegrand χ (1+(t : ℂ)*Complex.I)) =
      lemma32SmoothedWeightedSeries χ ((D : ℝ)^8)-lemma32SmoothedWeightedSeries χ ((D : ℝ)^4) :=
    lemma32_actual_original_Gamma_mellin_difference χ

example {D : ℕ} (χ : RealPrimitiveCharacter D) : 0 ≤ (lemma32SmoothedWeightedDifference χ).re :=
    lemma32_actual_real_smoothed_difference_nonneg χ

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 2 ≤ D) :
    lemma32SmoothingWindowLowerBound*(∑ n ∈ Finset.Icc (D^4+1) (D^8),
      ‖lemma23NuArithmeticFunction χ n‖^2*(lemma34Tau 2 n : ℝ)^2/(n : ℝ)) ≤
      (lemma32SmoothedWeightedDifference χ).re := lemma32_actual_weighted_tail_le_smoothed χ hD

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    AnalyticOnNhd ℂ (lemma32RegularNumerator χ) {w : ℂ | -1/2 < w.re} :=
    lemma32_regular_numerator_analyticOnNhd χ hD

example {D : ℕ} (χ : RealPrimitiveCharacter D) (w : ℂ)
    (hw : -1/2 < w.re) (h0 : w ≠ 0) :
    lemma32RegularNumerator χ w = w^8*(lemma32AnalyticCorrection χ (1+w)*
      (riemannZeta (1+w)*dirichletLFunction χ (1+w))^8*
      ((Complex.exp (8*(Real.log (D : ℝ) : ℂ)*w)-Complex.exp (4*(Real.log (D : ℝ) : ℂ)*w))*
        Complex.Gamma w)) := lemma32_regular_numerator_eq χ w hw h0

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 3 ≤ Real.log (D : ℝ)) :
    (2*Real.pi*Complex.I : ℂ)⁻¹*circleIntegral (lemma32CircleIntegrand χ) 0
      (Real.log (D : ℝ)^(-2024 : ℤ)) =
      iteratedDeriv 7 (lemma32RegularNumerator χ) 0/(Nat.factorial 7 : ℂ) :=
    lemma32_actual_original_circle_integral_eq_residue χ hD hL

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 3 ≤ Real.log (D : ℝ)) (hA : NormalizedAssumptionA χ) :
    ‖iteratedDeriv 7 (lemma32RegularNumerator χ) 0/(Nat.factorial 7 : ℂ)‖ ≤
      lemma32CircleConstant*Real.log (D : ℝ)^(-2007 : ℤ) :=
    lemma32_actual_residue_bound χ hD hL hA

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) (n : ℕ) :
    AnalyticOnNhd ℂ (lemma32DividedRemainder χ n) {w : ℂ | -1/2 < w.re} :=
    lemma32_divided_remainder_analyticOnNhd χ hD n

example {D : ℕ} (χ : RealPrimitiveCharacter D) (w : ℂ)
    (hw : -1/2 < w.re) (h0 : w ≠ 0) :
    lemma32CircleIntegrand χ w =
      (∑ k ∈ Finset.range 8, lemma32DividedRemainder χ k 0*w^k/w^8)+
        lemma32DividedRemainder χ 8 w := lemma32_actual_integrand_principal_decomposition χ w hw h0

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    lemma32ActualResidue χ = lemma32DividedRemainder χ 7 0 :=
    lemma32_actual_residue_eq_divided_remainder χ hD

example (T : ℝ) (hT : 0 < T) :
    lemma44GeneralRectangleBoundaryIntegral (fun w : ℂ => w^(-8 : ℤ)) (-1/4) 1 T = 0 :=
    lemma32_rectangle_zpow_zero (-8) (by norm_num) (-1/4) 1 T (by norm_num) (by norm_num) hT

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) (T : ℝ) (hT : 0 < T) :
    lemma44GeneralRectangleBoundaryIntegral
      (fun w : ℂ => ∑ k ∈ Finset.range 8, lemma32DividedRemainder χ k 0*w^k/w^8) (-1/4) 1 T =
      2*Real.pi*I*lemma32ActualResidue χ :=
    lemma32_actual_principal_boundary_residue χ hD (-1/4) T (by norm_num) (by norm_num) hT

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) (T : ℝ) (hT : 0 < T) :
    lemma44GeneralRectangleBoundaryIntegral
      (fun w : ℂ => lemma32AnalyticCorrection χ (1+w)*
        (riemannZeta (1+w)*dirichletLFunction χ (1+w))^8*
        ((Complex.exp (8*(Real.log (D : ℝ) : ℂ)*w)-Complex.exp (4*(Real.log (D : ℝ) : ℂ)*w))*
          Complex.Gamma w)) (-1/4) 1 T = 2*Real.pi*I*lemma32ActualResidue χ :=
    lemma32_actual_finite_rectangle_residue χ hD (-1/4) T (by norm_num) (by norm_num) hT

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) (T : ℝ) (hT : 0 < T) :
    ((1/(2*Real.pi) : ℝ) : ℂ)*
      ((∫ t : ℝ in -T..T, lemma32CircleIntegrand χ (1+(t : ℂ)*I))-
        ∫ t : ℝ in -T..T, lemma32CircleIntegrand χ (((-1/4 : ℝ) : ℂ)+(t : ℂ)*I))+
    (2*Real.pi*I : ℂ)⁻¹*
      ((∫ x : ℝ in (-1/4)..1, lemma32CircleIntegrand χ ((x : ℂ)-(T : ℂ)*I))-
        ∫ x : ℝ in (-1/4)..1, lemma32CircleIntegrand χ ((x : ℂ)+(T : ℂ)*I)) =
      lemma32ActualResidue χ :=
    lemma32_actual_normalized_finite_shift χ hD (-1/4) T (by norm_num) (by norm_num) hT

example (z : ℂ) (hlo : -1/4 ≤ z.re) (hhi : z.re ≤ 1) (hz : z.im ≠ 0) :
    ‖Complex.Gamma z‖ ≤ (1+((20 : ℕ).factorial : ℝ))/|z.im|^20 :=
    lemma32_gamma_strip_polynomial_decay z hlo hhi hz 20 (by norm_num)


example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) (w : ℂ)
    (hlo : -1/4 ≤ w.re) (hhi : w.re ≤ 1) (ht : 1 ≤ |w.im|) :
    ‖lemma32AnalyticCorrection χ (1+w)*(riemannZeta (1+w)*dirichletLFunction χ (1+w))^8*
      (lemma32SmoothingDifference (Real.log (D : ℝ)) w*Complex.Gamma w)‖ ≤
      lemma32GlobalHeightConstant D/|w.im|^4 :=
    lemma32_actual_integrand_height_decay χ hD w hlo hhi ht

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    MeasureTheory.Integrable (fun t : ℝ =>
      lemma32CircleIntegrand χ (((-1/4 : ℝ) : ℂ)+(t : ℂ)*I)) :=
    lemma32_actual_left_vertical_integrable χ hD (-1/4) (by norm_num) (by norm_num) (by norm_num)

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    lemma32SmoothedWeightedSeries χ ((D : ℝ)^8)-lemma32SmoothedWeightedSeries χ ((D : ℝ)^4) =
      iteratedDeriv 7 (lemma32RegularNumerator χ) 0/(Nat.factorial 7 : ℂ)+
      ((1/(2*Real.pi) : ℝ) : ℂ)*(∫ t : ℝ,
        lemma32CircleIntegrand χ (((-1/4 : ℝ) : ℂ)+(t : ℂ)*I)) :=
    lemma32_actual_smoothed_difference_eq_residue_add_left χ hD

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 2 ≤ D)
    (hL : 3 ≤ Real.log (D : ℝ)) (hA : NormalizedAssumptionA χ) :
    lemma32SmoothingWindowLowerBound*(∑ n ∈ Finset.Icc (D^4+1) (D^8),
      ‖lemma23NuArithmeticFunction χ n‖^2*(lemma34Tau 2 n : ℝ)^2/(n : ℝ)) ≤
      lemma32CircleConstant*Real.log (D : ℝ)^(-2007 : ℤ)+
      ‖((1/(2*Real.pi) : ℝ) : ℂ)*(∫ t : ℝ,
        lemma32CircleIntegrand χ (((-1/4 : ℝ) : ℂ)+(t : ℂ)*I))‖ :=
    lemma32_actual_original_tail_reduction χ hD hL hA


example (D : ℕ) (hD : 0 < D) (s : ℂ) (hs : 3/4 ≤ s.re) :
    ‖∏ p ∈ D.primeFactors, (1-Complex.exp (-s*(Real.log (p : ℝ) : ℂ)))^4‖ ≤
      (16 : ℝ)^(Nat.ceil (Real.exp 64))*Real.exp (Real.log (D : ℝ)/128) :=
    lemma32_ramification_uniform_power_saving D hD s hs

example {D : ℕ} (χ : RealPrimitiveCharacter D) (s : ℂ) (hs : 3/4 ≤ s.re) :
    ‖(∏ p ∈ D.primeFactors, (1-Complex.exp (-s*(Real.log (p : ℝ) : ℂ)))^4)*
      (∏' p : Nat.Primes, lemma32RegularLocalPolynomial χ p.val
        (Complex.exp (-s*(Real.log (p.val : ℝ) : ℂ))))‖ ≤
      ((16 : ℝ)^(Nat.ceil (Real.exp 64))*lemma32RegularProductBound (3/4))*
        Real.exp (Real.log (D : ℝ)/128) :=
    lemma32_analytic_correction_uniform_power_saving χ s hs

example (D : ℕ) (hD : 0 < D) :
    (∑ p ∈ D.primeFactors, Real.log (p : ℝ)) ≤ Real.log (D : ℝ) :=
    lemma32_prime_factors_log_sum_bound D hD

#print axioms lemma32_actual_coefficient_nonneg
#print axioms lemma32_tau_two_prime_power
#print axioms lemma32_actual_coefficient_prime_power_of_one
#print axioms lemma32_actual_coefficient_prime_power_of_zero
#print axioms lemma32_actual_coefficient_prime_power_of_neg_one
#print axioms lemma32_actual_coefficient_one
#print axioms lemma32_rising_choose_two
#print axioms lemma32_rising_choose_three
#print axioms lemma32_rising_choose_four
#print axioms lemma32_fourth_power_choose
#print axioms lemma32_fourth_geometric_hasSum
#print axioms lemma32_actual_coefficient_mul
#print axioms lemma32_square_geometric_hasSum
#print axioms lemma32_even_square_geometric_hasSum
#print axioms lemma32_actual_local_series_of_one
#print axioms lemma32_actual_local_series_of_zero
#print axioms lemma32_actual_even_local_series_of_neg_one
#print axioms lemma32_actual_local_series_of_neg_one
#print axioms lemma32_local_correction_of_one
#print axioms lemma32_local_correction_of_zero
#print axioms lemma32_local_correction_of_neg_one
#print axioms lemma32_bounded_polynomial_norm
#print axioms lemma32_plus_factor_remainder
#print axioms lemma32_minus_factor_remainder
#print axioms lemma32_plus_factor_norm_sub_one
#print axioms lemma32_minus_factor_norm_sub_one
#print axioms lemma32_actual_local_correction_norm_sub_one
#print axioms lemma32_character_prime_cases_of_not_dvd
#print axioms lemma32_local_correction_norm_of_not_dvd
#print axioms lemma32_zero_factor_norm
#print axioms lemma32_local_correction_norm_of_dvd
#print axioms lemma32_zero_correction_factorization
#print axioms lemma32_actual_correction_regular_factorization
#print axioms lemma32_regular_local_norm_sub_one
#print axioms lemma32_regular_local_differentiable
#print axioms lemma32_regular_local_at_zero
#print axioms lemma32_prime_monomial_norm
#print axioms lemma32_prime_monomial_norm_square
#print axioms lemma32_prime_monomial_norm_lt_one
#print axioms lemma32_regular_prime_errors_summable
#print axioms lemma32_regular_euler_product_multipliable
#print axioms lemma32_regular_prime_error_uniform
#print axioms lemma32_regular_finite_product_bound
#print axioms lemma32_regular_euler_product_bound
#print axioms lemma32_regular_product_bound_pos
#print axioms lemma32_regular_finite_product_difference
#print axioms lemma32_regular_products_uniform_cauchy
#print axioms lemma32_regular_products_uniform_limit
#print axioms lemma32_prime_monomial_differentiable
#print axioms lemma32_regular_finite_product_differentiable
#print axioms lemma32_regular_products_locally_uniform
#print axioms lemma32_regular_euler_product_differentiableOn
#print axioms lemma32_regular_euler_product_analyticOnNhd
#print axioms lemma32_one_sub_norm_le_one
#print axioms lemma32_prime_monomial_re
#print axioms lemma32_cos_lower_of_abs_le_one
#print axioms lemma32_ramified_prime_factor_norm
#print axioms lemma32_ramification_factor_differentiable
#print axioms lemma32_analytic_correction_analyticOnNhd
#print axioms lemma32_ramification_factor_norm
#print axioms lemma32_analytic_correction_sector_bound
#print axioms lemma32_negative_power_small
#print axioms lemma32_residue_disk_parameters
#print axioms lemma32_analytic_correction_residue_disk_bound
#print axioms lemma32_actual_first_derivative_bound
#print axioms lemma32_actual_L_difference_near_one
#print axioms lemma32_actual_value_at_one_small
#print axioms lemma32_circle_small_value_scale_identity
#print axioms lemma32_actual_L_residue_disk_small
#print axioms lemma32_zeta_pole_removed_local_bound
#print axioms lemma32_actual_zeta_local_pole_bound
#print axioms lemma32_actual_zeta_L_residue_circle_bound
#print axioms lemma32_exists_gamma_local_bound
#print axioms lemma32_gamma_local_bound_pos
#print axioms lemma32_gamma_local_bound
#print axioms lemma32_regularized_gamma_local_bound
#print axioms lemma32_smoothing_difference_local_bound
#print axioms lemma32_smoothing_gamma_local_bound
#print axioms lemma32_circle_constant_pos
#print axioms lemma32_circle_integrand_bound
#print axioms lemma32_residue_circle_scale_identity
#print axioms lemma32_actual_normalized_circle_integral_bound
#print axioms lemma32_modulus_cpow_eq_exp
#print axioms lemma32_original_smoothing_difference
#print axioms lemma32_original_normalized_circle_integral_bound
#print axioms lemma32_multichoose_2_square_le_4
#print axioms lemma32_multichoose_4_square_le_16
#print axioms lemma32_tau2_square_le_tau4
#print axioms lemma32_tau4_square_le_tau16
#print axioms lemma32_tau_two_eq_card_divisors
#print axioms lemma32_actual_coefficient_le_tau_sixteen
#print axioms lemma32_tau_lseries_summable
#print axioms lemma32_actual_weighted_lseries_summable
#print axioms lemma32_actual_weighted_norm_terms_summable
#print axioms lemma32_weighted_term_at_one
#print axioms lemma32_weighted_term_mul
#print axioms lemma32_actual_weighted_euler_hasProd
#print axioms lemma32_actual_weighted_euler_product
#print axioms lemma32_prime_monomial_eq_cpow
#print axioms lemma32_weighted_prime_power_term
#print axioms lemma32_weighted_local_correction_identity
#print axioms lemma32_finite_ramification_prime_product
#print axioms lemma32_ramification_prime_factors_hasProd
#print axioms lemma32_actual_local_corrections_hasProd
#print axioms lemma32_actual_zeta_monomial_euler_hasProd
#print axioms lemma32_actual_L_monomial_euler_hasProd
#print axioms lemma32_actual_weighted_series_identity
#print axioms lemma32_circle_integrand_differentiableAt
#print axioms lemma32_actual_circle_integrable
#print axioms lemma32_gamma_one_vertical_bound
#print axioms lemma32_gamma_one_vertical_integrable
#print axioms lemma32_exponential_mellin_eq_Gamma
#print axioms lemma32_exponential_mellin_convergent
#print axioms lemma32_actual_Gamma_mellin_inversion
#print axioms lemma32_Gamma_mellin_term_norm
#print axioms lemma32_Gamma_mellin_term_integrable
#print axioms lemma32_Gamma_mellin_term_integral_norm_summable
#print axioms lemma32_Gamma_mellin_term_eq_kernel
#print axioms lemma32_Gamma_mellin_term_normalized_integral
#print axioms lemma32_Gamma_mellin_tsum_integrable
#print axioms lemma32_full_series_gamma_mellin
#print axioms lemma32_actual_right_Gamma_integrand_eq_tsum
#print axioms lemma32_actual_right_Gamma_integrand_integrable
#print axioms lemma32_actual_smoothed_weighted_summable
#print axioms lemma32_actual_full_Gamma_mellin
#print axioms lemma32_actual_original_right_Gamma_difference
#print axioms lemma32_actual_original_right_Gamma_integrable
#print axioms lemma32_actual_original_Gamma_mellin_difference
#print axioms lemma32_actual_smoothed_difference_series
#print axioms lemma32_actual_weighted_term_one_real
#print axioms lemma32_actual_real_smoothed_terms_summable
#print axioms lemma32_actual_smoothed_difference_real_series
#print axioms lemma32_actual_real_smoothed_term_nonneg
#print axioms lemma32_actual_real_smoothed_difference_nonneg
#print axioms lemma32_smoothing_window_lower_bound_pos
#print axioms lemma32_exponential_smoothing_window_lower
#print axioms lemma32_actual_smoothing_weight_window_lower
#print axioms lemma32_actual_weighted_tail_le_smoothed
#print axioms lemma32_zeta_pole_removed_differentiableAt
#print axioms lemma32_smoothing_difference_differentiable
#print axioms lemma32_smoothing_dslope_differentiable
#print axioms lemma32_regular_numerator_differentiableAt
#print axioms lemma32_regular_numerator_analyticOnNhd
#print axioms lemma32_regular_numerator_eq
#print axioms lemma32_regular_numerator_differentiableOn_ball
#print axioms lemma32_actual_circle_integral_eq_residue
#print axioms lemma32_actual_original_circle_integral_eq_residue
#print axioms lemma32_actual_residue_bound
#print axioms lemma32_divided_remainder_differentiableOn
#print axioms lemma32_divided_remainder_analyticOnNhd
#print axioms lemma32_divided_remainder_recurrence
#print axioms lemma32_regular_numerator_finite_expansion
#print axioms lemma32_actual_integrand_principal_decomposition
#print axioms lemma32_actual_regular_remainder_rectangle_zero
#print axioms lemma32_divided_remainder_power_series
#print axioms lemma32_divided_remainder_coefficient
#print axioms lemma32_actual_residue_eq_divided_remainder
#print axioms lemma32_laurent_primitive_hasDerivAt
#print axioms lemma32_horizontal_zpow_integral
#print axioms lemma32_vertical_zpow_integral
#print axioms lemma32_rectangle_zpow_zero
#print axioms lemma32_rectangle_inverse_winding
#print axioms lemma32_rectangle_laurent_kernel
#print axioms lemma32_boundary_integrable_punctured
#print axioms lemma32_boundary_integral_add
#print axioms lemma32_boundary_integral_const_mul
#print axioms lemma32_boundary_integral_sum
#print axioms lemma32_laurent_kernel_continuousOn
#print axioms lemma32_principal_part_boundary_integrable
#print axioms lemma32_actual_principal_boundary_residue
#print axioms lemma32_boundary_integrable_halfplane
#print axioms lemma32_actual_finite_rectangle_residue
#print axioms lemma32_mellin_normalizing_factor
#print axioms lemma32_actual_normalized_finite_shift
#print axioms lemma32_gamma_shift_product
#print axioms lemma32_gamma_shift_norm_lower
#print axioms lemma32_gamma_strip_polynomial_decay
#print axioms lemma32_ramification_global_bound
#print axioms lemma32_analytic_correction_global_growth
#print axioms lemma32_positive_strip_high_norm
#print axioms lemma32_actual_zeta_strip_high_growth
#print axioms lemma32_actual_L_strip_high_growth
#print axioms lemma32_actual_zeta_L_strip_high_growth
#print axioms lemma32_smoothing_strip_growth
#print axioms lemma32_global_height_constant_pos
#print axioms lemma32_actual_integrand_height_decay
#print axioms lemma32_actual_integrand_eq_regular_div
#print axioms lemma32_actual_integrand_differentiableAt_global
#print axioms lemma32_actual_vertical_continuous
#print axioms lemma32_integrable_of_quartic_decay
#print axioms lemma32_actual_left_vertical_integrable
#print axioms lemma32_actual_horizontal_integral_bound
#print axioms lemma32_tendsto_zero_of_quartic_norm_bound
#print axioms lemma32_actual_upper_horizontal_decay
#print axioms lemma32_actual_lower_horizontal_decay
#print axioms lemma32_actual_infinite_contour_shift
#print axioms lemma32_actual_smoothed_difference_eq_residue_add_left
#print axioms lemma32_actual_original_tail_reduction

#print axioms lemma32_ramified_prime_small_bound
#print axioms lemma32_large_prime_monomial_small
#print axioms lemma32_ramified_large_prime_saving
#print axioms lemma32_ramification_saving_constant_pos
#print axioms lemma32_prime_factors_log_sum_bound
#print axioms lemma32_ramification_small_prime_count
#print axioms lemma32_ramification_uniform_power_saving
#print axioms lemma32_analytic_correction_uniform_power_saving

end ZhangLS.Spec
