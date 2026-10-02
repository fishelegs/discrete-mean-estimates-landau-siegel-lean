import ZhangLS.Spec.Lemma32PrimeUnpairedHasseBound
import ZhangLS.Spec.Lemma32UnpairedSingleton
import ZhangLS.Spec.Lemma32PrimeRootDifferenceBound
import ZhangLS.Spec.Lemma32PrimeHasseFourthMoment
import ZhangLS.Spec.Lemma32PrimitiveModulusShape
import ZhangLS.Spec.Lemma32OddPrimePowerConductor
import ZhangLS.Spec.Lemma32RealPrimitiveCRTCharacter
import ZhangLS.Spec.Lemma32PrimitiveCRTNontrivial
import ZhangLS.Spec.Lemma32FiniteActualCurvePoints
import ZhangLS.Spec.Lemma32DistinctMomentPointCount
import ZhangLS.Spec.Lemma32PrimeFourthMomentSplit
import ZhangLS.Spec.Lemma32OriginalCircle
import ZhangLS.Spec.Lemma32ActualSeriesIdentity
import ZhangLS.Spec.Lemma32SmoothingWindow
import ZhangLS.Spec.Lemma32ActualTailReduction
import ZhangLS.Spec.Lemma32RamificationPowerSaving
import ZhangLS.Spec.Lemma32BurgessReduction
import ZhangLS.Spec.Lemma32QuarticPermutations
import ZhangLS.Spec.Lemma32ActualPrimeCurveCount
import ZhangLS.Spec.Lemma32ActualOddCurveCount
import ZhangLS.Spec.Lemma32DistinctRootFieldSize
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


example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) (B : ℝ) (hB : 1 ≤ B)
    (hS : ∀ N : ℕ, ‖∑ n ∈ Finset.Icc 1 N, χ.evalNat n‖ ≤ B*(N : ℝ)^(1/2 : ℝ))
    (s : ℂ) (hs : s.re = 3/4) :
    ‖dirichletLFunction χ s‖ ≤ 8*B^(1/2 : ℝ)*‖s‖ :=
    lemma32_actual_L_bound_of_square_root_partial_sums χ hD B hB hS s hs

example : MeasureTheory.Integrable (fun t : ℝ =>
    ‖riemannZeta (1+(((-1/4 : ℝ) : ℂ)+(t : ℂ)*I))‖^8*
    ‖1+(((-1/4 : ℝ) : ℂ)+(t : ℂ)*I)‖^8*
    ‖Complex.Gamma (((-1/4 : ℝ) : ℂ)+(t : ℂ)*I)‖) := lemma32_left_kernel_integrable

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) (C : ℝ) (hC : 1 ≤ C)
    (hS : ∀ N : ℕ, ‖∑ n ∈ Finset.Icc 1 N, χ.evalNat n‖ ≤
      (C*Real.exp ((25/128)*Real.log (D : ℝ)))*(N : ℝ)^(1/2 : ℝ)) :
    ‖((1/(2*Real.pi) : ℝ) : ℂ)*(∫ t : ℝ,
      lemma32CircleIntegrand χ (((-1/4 : ℝ) : ℂ)+(t : ℂ)*I))‖ ≤
      lemma32LeftErrorConstant*C^4*Real.exp (-(27/128)*Real.log (D : ℝ)) :=
    lemma32_actual_left_integral_bound_of_burgess_partial_sums χ hD C hC hS

example (C : ℝ) : ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
    1 < D ∧ 3 ≤ Real.log (D : ℝ) ∧
    lemma32LeftErrorConstant*C^4*Real.exp (-(27/128)*Real.log (D : ℝ)) ≤
      Real.log (D : ℝ)^(-2007 : ℤ) := lemma32_left_error_absorption_threshold C

example (C : ℝ) (hC : 1 ≤ C)
    (hBurgess : ∀ D : ℕ, 2 ≤ D → ∀ χ : RealPrimitiveCharacter D, ∀ N : ℕ,
      ‖∑ n ∈ Finset.Icc 1 N, χ.evalNat n‖ ≤
        (C*Real.exp ((25/128)*Real.log (D : ℝ)))*(N : ℝ)^(1/2 : ℝ)) :
    ∃ K : ℝ, 0 < K ∧ ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
      ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
        (∑ n ∈ Finset.Ioc (D^4) (D^8),
          ‖lemma23NuArithmeticFunction χ n‖^2*(lemma34Tau 2 n : ℝ)^2/(n : ℝ)) ≤
          K*Real.log (D : ℝ)^(-2007 : ℤ) :=
    lemma32_target_of_uniform_burgess_partial_sums C hC hBurgess


example {D : ℕ} [NeZero D] (χ : RealPrimitiveCharacter D) (H : ℕ) :
    (∑ x : ZMod D, ‖∑ h : Fin H, χ.chi (x+(h.val : ZMod D))‖^4) =
      ∑ v : Fin 4 → Fin H, ∑ x : ZMod D,
        (χ.chi (∏ i : Fin 4, (x+((v i).val : ZMod D)))).re :=
    lemma32_actual_burgess_fourth_moment_expansion χ H

example (H : ℕ) : (lemma32DegenerateQuarticTuples H).card ≤ 3*H^2 :=
    lemma32_degenerate_quartic_tuples_card H

example {D : ℕ} [NeZero D] (χ : RealPrimitiveCharacter D) (H : ℕ) :
    (∑ v ∈ lemma32DegenerateQuarticTuples H,
      ∑ x : ZMod D, (χ.chi (∏ i : Fin 4, (x+((v i).val : ZMod D)))).re) ≤
      3*(D : ℝ)*(H : ℝ)^2 := lemma32_degenerate_fourth_moment_contribution_bound χ H

example {H : ℕ} (v : Fin 4 → Fin H) : v ∈ lemma32DegenerateQuarticTuples H ↔
    (v 0=v 1 ∧ v 2=v 3) ∨ (v 0=v 2 ∧ v 1=v 3) ∨ (v 0=v 3 ∧ v 1=v 2) :=
    lemma32_mem_degenerate_iff_paired v

example {p : ℕ} [Fact p.Prime] (χ : RealPrimitiveCharacter p) (a b : ZMod p) (hab : a ≠ b) :
    (∑ x : ZMod p, (χ.chi ((x+a)*(x+b))).re) = -1 :=
    lemma32_actual_prime_two_linear_real_correlation χ a b hab

example {p : ℕ} [Fact p.Prime] (χ : RealPrimitiveCharacter p) (a b c : ZMod p) (hbc : b ≠ c) :
    ‖∑ x : ZMod p, χ.chi ((x+a)^2*(x+b)*(x+c))‖ ≤ 2 :=
    lemma32_actual_prime_repeated_correlation_norm χ a b c hbc

example {D : ℕ} [NeZero D] (χ : RealPrimitiveCharacter D) (H : ℕ) :
    (∑ x : ZMod D, ‖∑ h : Fin H, χ.chi (x+(h.val : ZMod D))‖^4) ≤
      3*(D : ℝ)*(H : ℝ)^2+∑ v ∈ Finset.univ \ lemma32DegenerateQuarticTuples H,
        |∑ x : ZMod D, (χ.chi (∏ i : Fin 4, (x+((v i).val : ZMod D)))).re| :=
    lemma32_actual_fourth_moment_remainder_bound χ H

example {D : ℕ} [NeZero D] (χ : RealPrimitiveCharacter D) : lemma32BurgessFourthMoment χ 0 = 0 :=
    by simp [lemma32BurgessFourthMoment,lemma32ResidueShortSum]

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

#print axioms lemma32_square_quarter_power
#print axioms lemma32_square_negative_quarter_power
#print axioms lemma32_small_quarter_power_integral
#print axioms lemma32_large_quarter_power_integral
#print axioms lemma32_actual_partial_sum_square_root_majorant
#print axioms lemma32_actual_abel_small_majorant
#print axioms lemma32_actual_abel_large_majorant
#print axioms lemma32_actual_abel_square_root_partial_sum_bound
#print axioms lemma32_actual_L_bound_of_square_root_partial_sums
#print axioms lemma32_burgess_scale_half_power
#print axioms lemma32_actual_L_bound_of_burgess_partial_sums
#print axioms lemma32_left_line_Gamma_continuous
#print axioms lemma32_left_line_zeta_continuous
#print axioms lemma32_left_kernel_continuous
#print axioms lemma32_left_kernel_nonneg
#print axioms lemma32_left_kernel_high_bound
#print axioms lemma32_left_kernel_integrable
#print axioms lemma32_left_kernel_constant_pos
#print axioms lemma32_left_kernel_integral_le
#print axioms lemma32_smoothing_left_line_bound
#print axioms lemma32_half_power_eighth
#print axioms lemma32_actual_left_integrand_bound_of_partial_sums
#print axioms lemma32_left_error_constant_pos
#print axioms lemma32_actual_left_integral_bound_of_partial_sums
#print axioms lemma32_burgess_scale_fourth_decay
#print axioms lemma32_actual_left_integral_bound_of_burgess_partial_sums
#print axioms lemma32_left_error_absorption_threshold
#print axioms lemma32_target_of_uniform_burgess_partial_sums

#print axioms lemma32_real_complex_norm_fourth
#print axioms lemma32_actual_quartic_character_product
#print axioms lemma32_actual_burgess_fourth_moment_expansion
#print axioms lemma32_quartic_pairing_image_card
#print axioms lemma32_degenerate_quartic_tuples_card
#print axioms lemma32_actual_quartic_correlation_abs_bound
#print axioms lemma32_degenerate_fourth_moment_contribution_bound
#print axioms lemma32_quadratic_character_value_square
#print axioms lemma32_quadratic_character_inverse
#print axioms lemma32_quadratic_two_linear_correlation
#print axioms lemma32_quadratic_character_norm_le_one
#print axioms lemma32_actual_prime_two_linear_correlation
#print axioms lemma32_actual_prime_two_linear_real_correlation
#print axioms lemma32_quadratic_repeated_root_correlation
#print axioms lemma32_quadratic_repeated_root_correlation_norm
#print axioms lemma32_mem_degenerate_iff_paired
#print axioms lemma32_actual_prime_repeated_correlation_norm
#print axioms lemma32_actual_prime_quartic_repeated_correlation
#print axioms lemma32_actual_fourth_moment_decomposition
#print axioms lemma32_actual_fourth_moment_remainder_bound
#print axioms lemma32_nondegenerate_fourth_moment_nonneg
#print axioms lemma32_quartic_correlation_permutation
#print axioms lemma32_actual_prime_repeated_quartic_permutation_bound


example {F : Type*} [Field F] [Fintype F] (χ : MulChar F ℂ) (hq : χ^2=1)
    (a b c d : F) : (∑ x : F, χ ((x+a)*(x+b)*(x+c)*(x+d))) =
      (∑ u : F, χ ((1+(b-a)*u)*(1+(c-a)*u)*(1+(d-a)*u)))-1 :=
  lemma32_quadratic_quartic_cubic_sum_identity χ hq a b c d

example {F : Type*} [CommRing F] (a b c d : F) :
    (lemma32QuarticWeierstrass a b c d).Δ =
      16*((b-a)*(c-a)*(d-a))^2*(b-c)^2*(b-d)^2*(c-d)^2 :=
  lemma32_quartic_Weierstrass_discriminant a b c d

example {F : Type*} [Field F] (a b c d : F) (h2 : (2 : F) ≠ 0)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    (lemma32QuarticWeierstrass a b c d).IsElliptic :=
  lemma32_quartic_Weierstrass_isElliptic a b c d h2 hab hac had hbc hbd hcd

example {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (χ : MulChar F ℂ) (hn : χ ≠ 1) (hq : χ^2=1) (hF : ringChar F ≠ 2) (a : F) :
    χ a = (quadraticChar F a : ℂ) :=
  lemma32_nontrivial_quadratic_character_canonical_value χ hn hq hF a

example {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (χ : MulChar F ℂ) (hn : χ ≠ 1) (hq : χ^2=1) (hF : ringChar F ≠ 2) (a : F) :
    (({y : F | y^2=a}.toFinset).card : ℂ) = χ a+1 :=
  lemma32_quadratic_square_root_count χ hn hq hF a

example {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (χ : MulChar F ℂ) (hn : χ ≠ 1) (hq : χ^2=1) (hF : ringChar F ≠ 2) (P : F → F) :
    (((Finset.univ : Finset (F × F)).filter (fun v => v.2^2=P v.1)).card : ℂ) =
      (Fintype.card F : ℂ)+(∑ x : F, χ (P x)) :=
  by
    have he : (Finset.univ : Finset (F × F)).filter (fun v => v.2^2=P v.1) =
        lemma32CubicAffineSolutions P := by
      ext v
      simp only [lemma32CubicAffineSolutions,Finset.mem_filter,Finset.mem_univ,true_and]
    rw [he]
    exact lemma32_actual_affine_card_character_sum χ hn hq hF P

example {F : Type*} [Field F] (a b c d x y : F) :
    (lemma32QuarticWeierstrass a b c d).toAffine.Equation x y ↔
      y^2=x^3+((b-a)*(c-a)+(b-a)*(d-a)+(c-a)*(d-a))*x^2+
        ((b-a)*(c-a)*(d-a))*((b-a)+(c-a)+(d-a))*x+((b-a)*(c-a)*(d-a))^2 :=
  lemma32_quartic_curve_affine_equation a b c d x y

example {F : Type*} [Field F] [Fintype F] (W : WeierstrassCurve F) [W.IsElliptic] :
    Nat.card W.toAffine.Point =
      ((Finset.univ : Finset (F × F)).filter (fun v => W.toAffine.Equation v.1 v.2)).card+1 :=
  lemma32_Weierstrass_point_card_affine W

example {p : ℕ} [Fact p.Prime] (χ : RealPrimitiveCharacter p)
    (hF : ringChar (ZMod p) ≠ 2) (a b c d : ZMod p)
    (hA : (b-a)*(c-a)*(d-a) ≠ 0) [(lemma32QuarticWeierstrass a b c d).IsElliptic] :
    (∑ x : ZMod p, χ.chi ((x+a)*(x+b)*(x+c)*(x+d)))+1 =
      (Nat.card (lemma32QuarticWeierstrass a b c d).toAffine.Point : ℂ)-(p : ℂ)-1 :=
  lemma32_actual_prime_quartic_point_count χ hF a b c d hA

#print axioms lemma32_quartic_cubic_substitution
#print axioms lemma32_quadratic_quartic_cubic_point_identity
#print axioms lemma32_quadratic_quartic_cubic_punctured_sum
#print axioms lemma32_quadratic_quartic_cubic_sum_identity
#print axioms lemma32_monic_cubic_normalization
#print axioms lemma32_quadratic_monic_cubic_point_identity
#print axioms lemma32_quadratic_normalized_cubic_sum_identity
#print axioms lemma32_quadratic_quartic_normalized_cubic_sum_identity
#print axioms lemma32_normalized_cubic_root_factorization
#print axioms lemma32_quartic_Weierstrass_discriminant
#print axioms lemma32_cubic_leading_coefficient_nonzero
#print axioms lemma32_quartic_Weierstrass_discriminant_nonzero
#print axioms lemma32_quartic_Weierstrass_isElliptic
#print axioms lemma32_mulchar_eq_of_unit_generator
#print axioms lemma32_nontrivial_quadratic_unit_generator_value
#print axioms lemma32_nontrivial_quadratic_character_unique
#print axioms lemma32_nontrivial_quadratic_character_eq_canonical
#print axioms lemma32_nontrivial_quadratic_character_canonical_value
#print axioms lemma32_affine_solution_card_fibers
#print axioms lemma32_quadratic_square_root_count
#print axioms lemma32_actual_affine_card_character_sum
#print axioms lemma32_quartic_character_sum_affine_card
#print axioms lemma32_quartic_curve_affine_equation
#print axioms lemma32_quartic_curve_affine_solution_finset
#print axioms lemma32_quartic_character_sum_Weierstrass_affine_card
#print axioms lemma32_Weierstrass_point_card_affine
#print axioms lemma32_quartic_character_sum_actual_curve_points
#print axioms lemma32_actual_prime_quartic_point_count
#print axioms lemma32_actual_prime_quartic_correlation_point_count


example {p : ℕ} [Fact p.Prime] (χ : RealPrimitiveCharacter p) : ringChar (ZMod p) ≠ 2 :=
  lemma32_actual_prime_odd_characteristic χ

example {p : ℕ} [Fact p.Prime] (χ : RealPrimitiveCharacter p) (a b c d : ZMod p)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    (∑ x : ZMod p, χ.chi ((x+a)*(x+b)*(x+c)*(x+d)))+1 =
      (Nat.card (lemma32QuarticWeierstrass a b c d).toAffine.Point : ℂ)-(p : ℂ)-1 :=
  lemma32_actual_prime_distinct_quartic_point_count χ a b c d hab hac had hbc hbd hcd

#print axioms lemma32_nontrivial_quadratic_odd_characteristic
#print axioms lemma32_field_two_nonzero_of_odd_characteristic
#print axioms lemma32_actual_prime_odd_characteristic
#print axioms lemma32_actual_prime_distinct_quartic_point_count


example {p : ℕ} [Fact p.Prime] (a b c d : ZMod p)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : 5 ≤ p :=
  lemma32_four_distinct_prime_roots_modulus_ge_five a b c d hab hac had hbc hbd hcd

#print axioms lemma32_four_distinct_roots_injective
#print axioms lemma32_four_distinct_roots_field_card
#print axioms lemma32_four_distinct_prime_roots_modulus_ge_five


example {p : ℕ} [Fact p.Prime] (χ : RealPrimitiveCharacter p) {H : ℕ}
    (hH : H ≤ p) (v : Fin 4 → Fin H)
    (hp : v ∉ lemma32DegenerateQuarticTuples H) (hr : ¬ Function.Injective v) :
    |(∑ x : ZMod p, χ.chi (∏ i : Fin 4, (x+((v i).val : ZMod p)))).re| ≤ 2 := by
  simpa only [lemma32QuarticCorrelation,Complex.re_sum] using
    lemma32_actual_prime_unpaired_collision_correlation χ hH v hp hr

example {H : ℕ} (hH : H ≤ 0) :
    Function.Injective (fun h : Fin H => (h.val : ZMod 0)) :=
  lemma32_short_residue_cast_injective hH

example (H : ℕ) :
    ((Finset.univ : Finset (Fin 4 → Fin H)).filter (fun v => ¬ Function.Injective v)).card ≤
      6*H^3 := lemma32_collision_quartic_tuple_card H

example {p : ℕ} [Fact p.Prime] (χ : RealPrimitiveCharacter p) {H : ℕ} (hH : H ≤ p) :
    (∑ v ∈ (Finset.univ \ lemma32DegenerateQuarticTuples H).filter
      (fun v => ¬ Function.Injective v), |lemma32QuarticCorrelation χ v|) ≤
      12*(H : ℝ)^3 := lemma32_prime_collision_fourth_moment_bound χ hH

example {p : ℕ} [Fact p.Prime] (χ : RealPrimitiveCharacter p) {H : ℕ} (hH : H ≤ p) :
    (∑ x : ZMod p, ‖∑ h : Fin H, χ.chi (x+(h.val : ZMod p))‖^4) ≤
      3*(p : ℝ)*(H : ℝ)^2+12*(H : ℝ)^3+
        ∑ v ∈ (Finset.univ \ lemma32DegenerateQuarticTuples H).filter Function.Injective,
          |lemma32QuarticCorrelation χ v| := by
  simpa only [lemma32BurgessFourthMoment,lemma32ResidueShortSum,lemma32DistinctFourthMoment]
    using lemma32_actual_prime_fourth_moment_distinct_reduction χ hH

#print axioms lemma32_quadratic_unpaired_quartic_collision_bound
#print axioms lemma32_short_residue_cast_injective
#print axioms lemma32_actual_prime_unpaired_collision_correlation
#print axioms lemma32_quartic_noninjective_iff_collision
#print axioms lemma32_collision_tuples_covered
#print axioms lemma32_collision_quartic_tuple_card
#print axioms lemma32_prime_collision_fourth_moment_bound
#print axioms lemma32_nondegenerate_split_by_injectivity
#print axioms lemma32_actual_prime_fourth_moment_distinct_reduction


example {p : ℕ} [Fact p.Prime] (χ : RealPrimitiveCharacter p) {H : ℕ}
    (hH : H ≤ p) (v : Fin 4 → Fin H) (hv : Function.Injective v) :
    (∑ x : ZMod p, (χ.chi (∏ i : Fin 4, (x+((v i).val : ZMod p)))).re)+1 =
      (Nat.card (lemma32QuarticWeierstrass ((v 0).val : ZMod p) ((v 1).val : ZMod p)
        ((v 2).val : ZMod p) ((v 3).val : ZMod p)).toAffine.Point : ℝ)-(p : ℝ)-1 :=
  lemma32_distinct_quartic_correlation_point_count χ hH v hv

example {p : ℕ} [Fact p.Prime] (χ : RealPrimitiveCharacter p) {H : ℕ} (hH : H ≤ p) :
    (∑ v ∈ (Finset.univ \ lemma32DegenerateQuarticTuples H).filter Function.Injective,
      |lemma32QuarticCorrelation χ v|) =
      ∑ v ∈ (Finset.univ \ lemma32DegenerateQuarticTuples H).filter Function.Injective,
        |(Nat.card (lemma32QuarticWeierstrass ((v 0).val : ZMod p) ((v 1).val : ZMod p)
          ((v 2).val : ZMod p) ((v 3).val : ZMod p)).toAffine.Point : ℝ)-(p : ℝ)-2| :=
  lemma32_distinct_fourth_moment_eq_actual_point_discrepancy χ hH

#print axioms lemma32_distinct_quartic_correlation_point_count
#print axioms lemma32_distinct_fourth_moment_eq_actual_point_discrepancy

example {F : Type*} [Field F] [Fintype F] (W : WeierstrassCurve F) [W.IsElliptic] :
    Finite W.toAffine.Point := lemma32_actual_curve_points_finite W

#print axioms lemma32_actual_curve_points_finite
#print axioms lemma32_actual_curve_fintype_card_eq_nat_card

example {R S : Type*} [CommMonoid R] [CommMonoid S] [Fintype R] [Fintype S]
    (χ : MulChar (R × S) ℂ) (f : R → R) (g : S → S) :
    (∑ x : R × S, χ (f x.1,g x.2)) =
      (∑ a : R, χ (f a,1))*(∑ b : S, χ (1,g b)) :=
  lemma32_product_character_finite_sum χ f g

example {R S : Type*} [CommMonoid R] [CommMonoid S]
    (χ : MulChar (R × S) ℂ) (hq : χ^2=1) :
    (lemma32ProductCharacterLeft χ)^2=1 ∧ (lemma32ProductCharacterRight χ)^2=1 :=
  ⟨lemma32_product_character_left_quadratic χ hq,
    lemma32_product_character_right_quadratic χ hq⟩

example {m n : ℕ} [NeZero m] [NeZero n] (h : m.Coprime n)
    (χ : DirichletCharacter ℂ (m*n)) (a b c d : ZMod (m*n)) :
    let e := ZMod.chineseRemainder h
    ‖∑ x : ZMod (m*n), χ ((x+a)*(x+b)*(x+c)*(x+d))‖ =
      ‖∑ x : ZMod m, lemma32CRTCharacterLeft h χ
        ((x+(e a).1)*(x+(e b).1)*(x+(e c).1)*(x+(e d).1))‖*
      ‖∑ x : ZMod n, lemma32CRTCharacterRight h χ
        ((x+(e a).2)*(x+(e b).2)*(x+(e c).2)*(x+(e d).2))‖ := by
  have he := congrArg (fun z : ℂ => ‖z‖)
    (lemma32_actual_CRT_quartic_character_sum h χ a b c d)
  simpa only [lemma32QuarticRootProduct,norm_mul] using he

example {m n : ℕ} (h : m.Coprime n) (χ : RealPrimitiveCharacter (m*n)) :
    (lemma32CRTCharacterLeft h χ.chi)^2=1 ∧ (lemma32CRTCharacterRight h χ.chi)^2=1 :=
  lemma32_actual_CRT_character_quadratic h χ.chi χ.quadratic

example {m n : ℕ} (h : m.Coprime n) (χ : DirichletCharacter ℂ (m*n))
    (hr : lemma32CRTCharacterRight h χ = 1) :
    ∃ (hd : m ∣ m*n) (χ₀ : DirichletCharacter ℂ m),
      χ=DirichletCharacter.changeLevel hd χ₀ :=
  lemma32_actual_CRT_factorsThrough_left h χ hr

example {m n : ℕ} [NeZero m] [NeZero n] (h : m.Coprime n)
    (χ : RealPrimitiveCharacter (m*n)) (hm : 1 < m) :
    lemma32CRTCharacterLeft h χ.chi ≠ 1 :=
  lemma32_actual_primitive_CRT_left_nontrivial h χ.chi χ.primitive hm

example {m n : ℕ} [NeZero m] [NeZero n] (h : m.Coprime n)
    (χ : RealPrimitiveCharacter (m*n)) (hn : 1 < n) :
    lemma32CRTCharacterRight h χ.chi ≠ 1 :=
  lemma32_actual_primitive_CRT_right_nontrivial h χ.chi χ.primitive hn

#print axioms lemma32_product_character_factorization
#print axioms lemma32_product_character_finite_sum
#print axioms lemma32_product_character_left_quadratic
#print axioms lemma32_product_character_right_quadratic
#print axioms lemma32_product_quartic_character_sum
#print axioms lemma32_character_equiv_pullback_quadratic
#print axioms lemma32_character_equiv_pullback_nontrivial
#print axioms lemma32_quartic_character_sum_ring_equiv
#print axioms lemma32_actual_CRT_character_quadratic
#print axioms lemma32_actual_CRT_quartic_character_sum
#print axioms lemma32_actual_CRT_character_factorization
#print axioms lemma32_actual_CRT_factorsThrough_left
#print axioms lemma32_actual_CRT_factorsThrough_right
#print axioms lemma32_actual_primitive_CRT_left_nontrivial
#print axioms lemma32_actual_primitive_CRT_right_nontrivial

example {m n : ℕ} [NeZero m] [NeZero n] (h : m.Coprime n)
    (χ : RealPrimitiveCharacter (m*n)) :
    (lemma32CRTCharacterLeft h χ.chi).IsPrimitive ∧
      (lemma32CRTCharacterRight h χ.chi).IsPrimitive :=
  lemma32_actual_primitive_CRT_characters h χ.chi χ.primitive

example {m n : ℕ} [NeZero m] [NeZero n] (h : m.Coprime n)
    (χ : RealPrimitiveCharacter (m*n)) :
    (lemma32RealCRTLeft h χ).chi.conductor=m :=
  (lemma32RealCRTLeft h χ).primitive

example {m n : ℕ} [NeZero m] [NeZero n] (h : m.Coprime n)
    (χ : RealPrimitiveCharacter (m*n)) (a : ZMod m) :
    ((lemma32RealCRTLeft h χ).chi a).im=0 :=
  (lemma32RealCRTLeft h χ).real_valued a

example {m n : ℕ} [NeZero m] [NeZero n] (h : m.Coprime n)
    (χ : RealPrimitiveCharacter (m*n)) :
    (lemma32RealCRTRight h χ).chi^2=1 :=
  (lemma32RealCRTRight h χ).quadratic

example {m n : ℕ} [NeZero m] [NeZero n] (h : m.Coprime n)
    (χ : RealPrimitiveCharacter (m*n)) (a : ZMod (m*n)) :
    χ.chi a = (lemma32RealCRTLeft h χ).chi ((ZMod.chineseRemainder h a).1) *
      (lemma32RealCRTRight h χ).chi ((ZMod.chineseRemainder h a).2) :=
  lemma32_real_primitive_CRT_factorization h χ a

example {m n : ℕ} [NeZero m] [NeZero n] (h : m.Coprime n)
    (χ : RealPrimitiveCharacter (m*n)) (a b c d : ZMod (m*n)) :
    let e := ZMod.chineseRemainder h
    ‖∑ x : ZMod (m*n), χ.chi (lemma32QuarticRootProduct a b c d x)‖ =
      ‖∑ x : ZMod m, (lemma32RealCRTLeft h χ).chi
        (lemma32QuarticRootProduct (e a).1 (e b).1 (e c).1 (e d).1 x)‖ *
      ‖∑ x : ZMod n, (lemma32RealCRTRight h χ).chi
        (lemma32QuarticRootProduct (e a).2 (e b).2 (e c).2 (e d).2 x)‖ := by
  have he := congrArg (fun z : ℂ => ‖z‖)
    (lemma32_real_primitive_CRT_quartic_sum h χ a b c d)
  simpa only [norm_mul] using he

#print axioms lemma32_changeLevel_factorsThrough_conductor

#print axioms lemma32_changeLevel_conductor_dvd

#print axioms lemma32_actual_CRT_changeLevel_product

#print axioms lemma32_actual_CRT_conductor_dvd_lcm

#print axioms lemma32_actual_primitive_CRT_characters

#print axioms lemma32_real_primitive_CRT_factorization

#print axioms lemma32_real_primitive_CRT_quartic_sum

example {p : ℕ} (hp : p.Prime) (k : ℕ) :
    Nat.card (ZMod.unitsMap (dvd_pow_self p (Nat.succ_ne_zero k))).ker=p^k :=
  lemma32_prime_power_reduction_kernel_card hp k

example {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (k : ℕ)
    (χ : RealPrimitiveCharacter (p^(k+1))) : χ.chi.FactorsThrough p :=
  lemma32_odd_prime_power_quadratic_factorsThrough hp hodd k χ.chi χ.quadratic

example {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (k : ℕ)
    (χ : RealPrimitiveCharacter (p^(k+1))) : χ.chi.conductor ∣ p :=
  lemma32_odd_prime_power_quadratic_conductor_dvd hp hodd k χ.chi χ.quadratic

example {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (k : ℕ)
    (χ : RealPrimitiveCharacter (p^(k+1))) : k=0 :=
  lemma32_odd_prime_power_primitive_quadratic_exponent hp hodd k χ.chi
    χ.quadratic χ.primitive

example (k : ℕ) (χ : RealPrimitiveCharacter (3^(k+1))) : k=0 := by
  exact lemma32_odd_prime_power_primitive_quadratic_exponent (by decide) (by decide)
    k χ.chi χ.quadratic χ.primitive

example (k : ℕ) (χ : RealPrimitiveCharacter (5^(k+1))) : k=0 := by
  exact lemma32_odd_prime_power_primitive_quadratic_exponent (by decide) (by decide)
    k χ.chi χ.quadratic χ.primitive

#print axioms lemma32_quadratic_hom_odd_card_eq_one

#print axioms lemma32_quadratic_character_factorsThrough_odd_kernel

#print axioms lemma32_units_reduction_kernel_card

#print axioms lemma32_prime_power_reduction_kernel_card

#print axioms lemma32_odd_prime_power_quadratic_factorsThrough

#print axioms lemma32_odd_prime_power_quadratic_conductor_dvd

#print axioms lemma32_odd_prime_power_primitive_quadratic_exponent

example (k : ℕ) :
    Nat.card (ZMod.unitsMap (lemma32TwoPowerReductionDvd k)).ker = 2^k :=
  lemma32_two_power_reduction_kernel_card k

example (k : ℕ) (χ : RealPrimitiveCharacter (2^(k+3))) : χ.chi.FactorsThrough 8 :=
  lemma32_two_power_quadratic_factorsThrough k χ.chi χ.quadratic

example (k : ℕ) (χ : RealPrimitiveCharacter (2^(k+3))) : χ.chi.conductor ∣ 8 :=
  lemma32_two_power_quadratic_conductor_dvd k χ.chi χ.quadratic

example (k : ℕ) (χ : RealPrimitiveCharacter (2^(k+3))) : k=0 :=
  lemma32_two_power_primitive_quadratic_exponent k χ.chi χ.quadratic χ.primitive

example {D p : ℕ} (χ : RealPrimitiveCharacter D) (hp : p.Prime) (hodd : p ≠ 2) :
    D.factorization p ≤ 1 := lemma32_real_primitive_odd_prime_exponent χ hp hodd

example {D : ℕ} (χ : RealPrimitiveCharacter D) : D.factorization 2 ≤ 3 :=
  lemma32_real_primitive_two_adic_exponent χ

example {D : ℕ} (χ : RealPrimitiveCharacter D) : Squarefree (D / 2^(D.factorization 2)) :=
  lemma32_real_primitive_odd_part_squarefree χ

example {D : ℕ} (χ : RealPrimitiveCharacter D) :
    ∃ e m : ℕ, e ≤ 3 ∧ Odd m ∧ Squarefree m ∧ D=2^e*m :=
  lemma32_real_primitive_modulus_shape χ

example (χ : RealPrimitiveCharacter 9) : False := by
  have he := lemma32_odd_prime_power_primitive_quadratic_exponent (p := 3)
    (by decide) (by decide) 1 χ.chi χ.quadratic χ.primitive
  omega

example (χ : RealPrimitiveCharacter 16) : False := by
  have he := lemma32_two_power_primitive_quadratic_exponent 1 χ.chi χ.quadratic χ.primitive
  omega

#print axioms lemma32_two_power_reduction_kernel_card

#print axioms lemma32_two_power_five_unit_order

#print axioms lemma32_two_power_five_square_order

#print axioms lemma32_two_power_reduction_kernel_generator

#print axioms lemma32_two_power_quadratic_factorsThrough

#print axioms lemma32_two_power_quadratic_conductor_dvd

#print axioms lemma32_two_power_primitive_quadratic_exponent

#print axioms lemma32_real_primitive_odd_prime_exponent

#print axioms lemma32_real_primitive_two_adic_exponent

#print axioms lemma32_real_primitive_odd_part_squarefree

#print axioms lemma32_real_primitive_modulus_shape

example {p : ℕ} [Fact p.Prime] (χ : RealPrimitiveCharacter p)
    (a b c d : ZMod p) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ‖∑ x : ZMod p, χ.chi ((x+a)*(x+b)*(x+c)*(x+d))‖ ≤ 2*Real.sqrt (p : ℝ)+1 :=
  lemma32_actual_prime_distinct_quartic_hasse_bound χ a b c d hab hac had hbc hbd hcd

example {p : ℕ} [Fact p.Prime] (χ : RealPrimitiveCharacter p) {H : ℕ} (hH : H ≤ p) :
    (∑ x : ZMod p, ‖∑ h : Fin H, χ.chi (x+(h.val : ZMod p))‖^4) ≤
      3*(p : ℝ)*(H : ℝ)^2+12*(H : ℝ)^3+(H : ℝ)^4*(2*Real.sqrt (p : ℝ)+1) :=
  lemma32_actual_prime_fourth_moment_hasse_bound χ hH

example {p : ℕ} [Fact p.Prime] (χ : RealPrimitiveCharacter p) {H : ℕ} (hH : H ≤ p)
    (v : Fin 4 → Fin H) (hv : Function.Injective v) :
    |∑ x : ZMod p, (χ.chi ((x+(v 0).val)*(x+(v 1).val)*
      (x+(v 2).val)*(x+(v 3).val))).re| ≤ 2*Real.sqrt (p : ℝ)+1 := by
  simpa only [lemma32QuarticCorrelation,Fin.prod_univ_four] using
    lemma32_actual_prime_distinct_quartic_correlation_bound χ hH v hv

#print axioms lemma32_actual_curve_hasse_nat_card

#print axioms lemma32_actual_prime_distinct_quartic_hasse_bound

#print axioms lemma32_actual_prime_distinct_quartic_correlation_bound

#print axioms lemma32_actual_prime_distinct_fourth_moment_bound

#print axioms lemma32_actual_prime_fourth_moment_hasse_bound

example {p : ℕ} [Fact p.Prime] (χ : RealPrimitiveCharacter p)
    (a b c d : ZMod p) (hp : ¬ ((a=b ∧ c=d) ∨ (a=c ∧ b=d) ∨ (a=d ∧ b=c))) :
    ‖∑ x : ZMod p, χ.chi ((x+a)*(x+b)*(x+c)*(x+d))‖ ≤ 3*Real.sqrt (p : ℝ) :=
  lemma32_actual_prime_unpaired_quartic_hasse_bound χ a b c d hp

example {H : ℕ} (v : Fin 4 → Fin H) (hv : v ∉ lemma32DegenerateQuarticTuples H) :
    ∃ j : Fin 4, ∀ i : Fin 4, i ≠ j → v j ≠ v i := by
  apply lemma32_unpaired_quartic_tuple_has_singleton v
  intro hp
  exact hv ((lemma32_mem_degenerate_iff_paired v).mpr hp)

example {p : ℕ} [Fact p.Prime] (χ : RealPrimitiveCharacter p) (a b c d : ZMod p) :
    ‖∑ x : ZMod p, χ.chi ((x+a)*(x+b)*(x+c)*(x+d))‖ ≤
      3*Real.sqrt (p : ℝ)*(if (a-b)*(a-c)*(a-d)=0 then Real.sqrt (p : ℝ) else 1) :=
  lemma32_actual_prime_quartic_root_difference_bound χ a b c d

#print axioms lemma32_prime_sqrt_ge_one

#print axioms lemma32_actual_prime_unpaired_quartic_hasse_bound

#print axioms lemma32_actual_prime_isolated_root_hasse_bound

#print axioms lemma32_unpaired_quartic_tuple_has_singleton

#print axioms lemma32_actual_quartic_sum_trivial_norm

#print axioms lemma32_actual_prime_quartic_root_difference_bound

end ZhangLS.Spec

#print axioms HasseWeil.WeilPairing.hasse_bound
#print axioms HasseWeil.WeilPairing.hasse_bound_unconditional
