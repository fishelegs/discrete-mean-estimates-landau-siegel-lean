import ZhangLS.Spec.Proposition71FiniteContourZBound
import ZhangLS.Spec.Proposition71FinitePolynomialGrowth
import ZhangLS.Spec.Proposition71FiniteContourShift
import ZhangLS.Spec.Proposition71FiniteCriticalMean
import ZhangLS.Spec.Proposition71FiniteExceptionalContour
import ZhangLS.Spec.Proposition71FrontLargeTail
import ZhangLS.Spec.Proposition71FrontLargeTailRate
import ZhangLS.Spec.Proposition71FrontHeadTail
import ZhangLS.Spec.Proposition71InfiniteExceptionalContour
import ZhangLS.Spec.Proposition71ActualKappaSeries
import ZhangLS.Spec.Proposition71OriginalFrontAttachment
import ZhangLS.Spec.Proposition71OriginalExceptional
import ZhangLS.Spec.Proposition71OriginalFamilyExtension
import ZhangLS.Spec.Proposition71OriginalDeltaReduction

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Finset
open scoped Classical
set_option maxRecDepth 4096

-- Strict head / closed tail endpoint, with no rounded replacement.
example (D : ℕ) (c : ℕ → ℂ) (m : ℕ) (hm : (m : ℝ)=lemma23PaperP D^2) :
    proposition71LongHead D c m=0 ∧ proposition71LongTail D c m=c m := by
  simp [proposition71LongHead,proposition71LongTail,hm]

-- Original coefficient support remains strict.
example {D : ℕ} {B : ℝ} (a : ℕ → ℂ) (ha : Lemma81AdmissibleSequence D B a)
    (n : ℕ) (hn : lemma81Cutoff D≤(n : ℝ)) : a n=0 := ha.2 n hn

-- The functional-equation character and coefficient character remain distinct.
example {N p : ℕ} [NeZero N] (D : ℕ) (θ : DirichletCharacter ℂ N)
    (ψ : DirichletCharacter ℂ p) (Y X : ℕ) (c a : ℕ → ℂ) (s : ℂ) :
    proposition71FiniteFrontKernel D θ ψ Y X c a s=
      (lemma23DirichletZ θ s)⁻¹*lemma81FiniteCharacterPolynomial Y c ψ s*
        lemma81FiniteCharacterPolynomial X a ψ⁻¹ (1-s)*lemma81Omega D s := rfl

-- The long nonunit branch is retained as an actual zero character factor.
example {p : ℕ} [Fact p.Prime] (D : ℕ) (c a : ℕ → ℂ)
    (ψ : DirichletCharacter ℂ p) (S : Finset ℕ) (m : ℕ) (hm : (m : ZMod p)=0) :
    proposition71DeltaOneDoubleTerm D (fun n => c n*ψ (n : ZMod p)) S a (p : ℝ) m=0 := by
  have hzero : ψ 0=0 := DirichletCharacter.map_zero' ψ (Fact.out : p.Prime).ne_one
  simp [proposition71DeltaOneDoubleTerm,hm,hzero]

-- Original ds=i dt and normalization are related by the exact 2πi factor.
example (D : ℕ) (f : ℂ → ℂ) :
    I*(∫t in -(lemma23PaperL D^405)..lemma23PaperL D^405, f (lemma81SegmentPoint D 1 t))=
      (((2*Real.pi : ℝ) : ℂ)*I)*lemma81NormalizedSegmentIntegral D 1 f :=
  proposition71_unnormalized_segment_eq D 1 f

-- The complete original (7.3), (7.6), and Gauss-ready analytic reduction.
#check proposition71_original_seven_three
#check proposition71_original_seven_six
#check proposition71_original_delta_one_reduction
#check proposition71_infinite_exceptional_contour_little_o
end ZhangLS.Spec
#print axioms ZhangLS.Spec.proposition71_Z_log_derivative_wide
#print axioms ZhangLS.Spec.proposition71_inverse_Z_finite_contour_bound
#print axioms ZhangLS.Spec.proposition71_tau_unweighted_sum
#print axioms ZhangLS.Spec.proposition71_finite_tau_polynomial_norm
#print axioms ZhangLS.Spec.proposition71_long_finite_polynomial_exponential
#print axioms ZhangLS.Spec.proposition71_short_finite_polynomial_norm
#print axioms ZhangLS.Spec.proposition71FiniteFrontKernel
#print axioms ZhangLS.Spec.proposition71_finite_front_differentiableAt
#print axioms ZhangLS.Spec.proposition71_finite_front_boundary_envelope
#print axioms ZhangLS.Spec.proposition71_finite_front_shift
#print axioms ZhangLS.Spec.proposition71_normalized_segment_const_mul
#print axioms ZhangLS.Spec.proposition71_finite_front_critical_norm
#print axioms ZhangLS.Spec.proposition71_finite_front_segment_integrable
#print axioms ZhangLS.Spec.proposition71_finite_critical_exceptional_little_o
#print axioms ZhangLS.Spec.proposition71_finite_exceptional_contour_little_o
#print axioms ZhangLS.Spec.proposition71_delta_one_norm_eq_delta
#print axioms ZhangLS.Spec.proposition71ShortLinearMass
#print axioms ZhangLS.Spec.proposition71_short_linear_mass_nonneg
#print axioms ZhangLS.Spec.proposition71_delta_one_scaled_tail
#print axioms ZhangLS.Spec.proposition71_front_large_tail_term_bound
#print axioms ZhangLS.Spec.proposition71_front_large_tail_tsum_bound
#print axioms ZhangLS.Spec.proposition71_short_linear_mass_bound
#print axioms ZhangLS.Spec.proposition71_primitive_gauss_normalized_norm_le_one
#print axioms ZhangLS.Spec.proposition71FrontLargeTailConstant
#print axioms ZhangLS.Spec.proposition71_front_large_tail_constant_pos
#print axioms ZhangLS.Spec.proposition71_front_large_tail_main_rate
#print axioms ZhangLS.Spec.proposition71_front_large_tail_contour_rate
#print axioms ZhangLS.Spec.proposition71LongHead
#print axioms ZhangLS.Spec.proposition71LongTail
#print axioms ZhangLS.Spec.proposition71_long_head_tail
#print axioms ZhangLS.Spec.proposition71_long_head_majorant
#print axioms ZhangLS.Spec.proposition71_long_tail_majorant
#print axioms ZhangLS.Spec.proposition71_twisted_coefficient_majorant
#print axioms ZhangLS.Spec.proposition71_long_head_series_eq_finite
#print axioms ZhangLS.Spec.proposition71_long_series_head_tail
#print axioms ZhangLS.Spec.proposition71InfiniteFrontKernel
#print axioms ZhangLS.Spec.proposition71_infinite_front_eq_actual_kernel
#print axioms ZhangLS.Spec.proposition71_infinite_front_head_tail
#print axioms ZhangLS.Spec.proposition71_infinite_front_differentiableAt
#print axioms ZhangLS.Spec.proposition71_infinite_front_segment_integrable
#print axioms ZhangLS.Spec.proposition71_infinite_contour_head_tail
#print axioms ZhangLS.Spec.proposition71_front_conductor_log_bound
#print axioms ZhangLS.Spec.proposition71_infinite_exceptional_contour_little_o
#print axioms ZhangLS.Spec.proposition71_kappa_twist_summable
#print axioms ZhangLS.Spec.proposition71_kappa_twist_LSeries_ratio
#print axioms ZhangLS.Spec.proposition71_arithmetic_sequence_strict_support
#print axioms ZhangLS.Spec.proposition71_arithmetic_sequence_LSeries
#print axioms ZhangLS.Spec.proposition71_actual_ratio_convolution
#print axioms ZhangLS.Spec.proposition71_original_polynomial_eq_cutoff_prefix
#print axioms ZhangLS.Spec.proposition71_actual_C_infinite_kernel
#print axioms ZhangLS.Spec.proposition71_actual_C_contour_eq_infinite
#print axioms ZhangLS.Spec.proposition71_original_short_support_geometry
#print axioms ZhangLS.Spec.proposition71_original_seven_three_normalized
#print axioms ZhangLS.Spec.proposition71_unnormalized_segment_eq
#print axioms ZhangLS.Spec.proposition71_original_seven_three
#print axioms ZhangLS.Spec.proposition71_actual_family_partition
#print axioms ZhangLS.Spec.proposition71_original_full_family_C_reduction
#print axioms ZhangLS.Spec.proposition71_original_seven_six
#print axioms ZhangLS.Spec.proposition71OriginalDeltaOneMean
#print axioms ZhangLS.Spec.proposition71_original_short_shifted_power
#print axioms ZhangLS.Spec.proposition71_actual_C_strict_front_kernel
#print axioms ZhangLS.Spec.proposition71_actual_C_strict_front_contour
#print axioms ZhangLS.Spec.proposition71_original_delta_one_series_summable
#print axioms ZhangLS.Spec.proposition71_original_delta_one_reduction
#print ZhangLS.Spec.proposition71OriginalDeltaOneMean
#print ZhangLS.Spec.proposition71DeltaOneDoubleTerm
#print ZhangLS.Spec.proposition71LongHead
#print ZhangLS.Spec.proposition71LongTail
#print ZhangLS.Spec.proposition71FiniteFrontKernel
#print ZhangLS.Spec.proposition71InfiniteFrontKernel
#print ZhangLS.Spec.proposition71_actual_ratio_convolution
#print ZhangLS.Spec.proposition71_actual_C_strict_front_kernel
#print ZhangLS.Spec.proposition71_original_short_support_geometry
#print ZhangLS.Spec.proposition71_original_seven_three
#print ZhangLS.Spec.proposition71_original_seven_six
#print ZhangLS.Spec.proposition71_original_delta_one_reduction
#print ZhangLS.Spec.proposition71_infinite_exceptional_contour_little_o
#print ZhangLS.Spec.proposition71_front_large_tail_contour_rate
#print ZhangLS.Spec.lemma81ThetaOne
#print ZhangLS.Spec.lemma81ActualC
#print ZhangLS.Spec.lemma81CIntegrand
#print ZhangLS.Spec.lemma81NormalizedSegmentIntegral
#print ZhangLS.Spec.lemma81SegmentPoint
#print ZhangLS.Spec.Lemma81AdmissibleSequence
#print ZhangLS.Spec.lemma81PolynomialIndices
#print ZhangLS.Spec.lemma81Cutoff
#print ZhangLS.Spec.lemma33ActualFamily
#print ZhangLS.Spec.proposition21ActualPsi2Family
#print ZhangLS.Spec.Lemma23InPsi
#print ZhangLS.Spec.Lemma23InPsi1
#print ZhangLS.Spec.Lemma23GoodPartialSums
#print ZhangLS.Spec.lemma33ActualPrimeMass
#print ZhangLS.Spec.lemma83PaperBeta
#print ZhangLS.Spec.lemma83Kappa
#print ZhangLS.Spec.proposition71ArithmeticSequence
#print ZhangLS.Spec.NormalizedAssumptionA
#print ZhangLS.Spec.Proposition71Target
#print ZhangLS.Spec.Proposition71AtConstant
#print ZhangLS.Spec.proposition71ArithmeticSum
#print ZhangLS.Spec.proposition71ErrorScale
#print ZhangLS.Spec.proposition71MainTerm
