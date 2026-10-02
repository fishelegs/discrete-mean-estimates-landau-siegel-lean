import ZhangLS.Spec.Lemma102MixedLittleO
import ZhangLS.Spec.Lemma102Boundary
set_option autoImplicit false
open scoped Classical
namespace ZhangLS.Spec
open Complex MeasureTheory

/-- The Section 8 Nat smoothing index zero is beta7, not frequency zero. -/
example (D : ℕ) : lemma84SmoothingBeta D 0=5*I*(lemma44PaperAlpha D:ℂ)/2 := by
  simp [lemma84SmoothingBeta]

/-- Literal actual xi/tent regression, with neither a model coefficient nor
an assumed integral value. -/
example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1<D)
    (c : ℝ) (j : Fin 3) (d r : ℕ) (hd : 0<d) (hr : 0<r) :
    lemma102Sum χ c j d r = ∑' n : ℕ,
      χ.evalNat n*lemma83Xi (lemma83PaperBeta D c) j n d r/(n:ℂ)*
        (lemma111Tent (Real.log ((d*r:ℝ)*(n:ℝ))/Real.log (lemma23PaperP D)):ℂ) :=
  lemma102_sum_eq_tsum χ hD c j d r hd hr

example (a b ℓ : ℂ) {R : ℝ} (hR : 0<R) :
    (2*Real.pi*I:ℂ)⁻¹*circleIntegral
      (fun s : ℂ => (s+a)*(s+b)/s*exp (s*ℓ)/s^2) 0 R =
        1+(a+b)*ℓ+a*b/2*ℓ^2 := lemma102_model_circle_integral a b ℓ hR

example {D : ℕ} (χ : RealPrimitiveCharacter D) (c : ℝ) (j : Fin 3)
    (d r : ℕ) (hd : 0<d) (hr : 0<r) {b x : ℝ} (hb : 0<b) (hx : 0<x) :
    lemma102LogSum χ c j d r x=(2*Real.pi:ℂ)⁻¹*(∫ t : ℝ,
      lemma83XiDirichletSeries χ (lemma83PaperBeta D c) j d r (1+((b:ℂ)+I*(t:ℂ)))*
        ((x:ℂ)^((b:ℂ)+I*(t:ℂ))/((b:ℂ)+I*(t:ℂ))^2)) :=
  lemma102_actual_xi_perron χ c j d r hd hr hb hx

example (D : ℕ) (y : ℝ) : Lemma101Transition D y ↔
    y ∈ Set.Ioc (lemma23PaperP D^(1/2:ℝ)/lemma56PaperT D) (lemma23PaperP D^(1/2:ℝ)) ∪
      Set.Ioc (lemma23PaperP D^(251/500:ℝ)/lemma56PaperT D) (lemma23PaperP D^(251/500:ℝ)) ∪
      Set.Ioo (lemma23PaperP D^(63/125:ℝ)/lemma56PaperT D) (lemma23PaperP D^(63/125:ℝ)) := Iff.rfl

end ZhangLS.Spec

namespace ZhangLS.Spec
open Complex Finset

example : ∀ c : ℝ, 0<c → ∀ ε : ℝ, 0<ε → ∃ D₀ : ℕ, 2≤D₀ ∧
    ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
    ∀ j : Fin 3, ‖lemma102MixedRaw χ c j-lemma102MixedMain χ c j‖≤ε*lemma44PaperAlpha D :=
  lemma102_mixed_full_xi_replacement_little_o

example : ∀ c : ℝ, 0<c → ∀ ε : ℝ, 0<ε → ∃ D₀ : ℕ, 2≤D₀ ∧
    ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
    ∀ j : Fin 3,
      ‖(∑ a∈lemma84Section8Pairs D, lemma84Section8Weight χ c j a.1 a.2*
        (lemma84Section8FirstSource χ c j 6 (a.1*a.2)+
          lemma84Section8Iota*lemma84Section8FirstSource χ c j 7 (a.1*a.2))*
        (∑' n : ℕ, χ.evalNat n*lemma83Xi (lemma83PaperBeta D c) j n a.1 a.2/(n:ℂ)*
          (lemma111Tent (Real.log ((a.1*a.2:ℝ)*(n:ℝ))/Real.log (lemma23PaperP D)):ℂ)))-
        lemma102MixedMain χ c j‖≤ε*lemma44PaperAlpha D :=
  lemma102_source_full_xi_replacement_little_o

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1<D)
    (hL : 1<lemma23PaperL D) (c : ℝ) (j : Fin 3)
    (hcut : lemma23PaperP D^(63/125:ℝ)<lemma23PaperP D*lemma56PaperT D^(-2:ℤ)) :
    (∑ a∈(lemma84Section8Pairs D).filter (fun a => Lemma101Transition D (a.1*a.2:ℝ)),
      ‖lemma84Section8Weight χ c j a.1 a.2‖)≤
        24*lemma84WeightScale (lemma23PaperL D^9)*Real.log (lemma56PaperT D) :=
  lemma102_transition_weight_mass χ hD hL c j hcut

example {D : ℕ} (χ : RealPrimitiveCharacter D) (c : ℝ) (j : Fin 3) :
    lemma102MixedMain χ c j =
      ∑ a∈lemma84Section8Pairs D, lemma84Section8Weight χ c j a.1 a.2*
        lemma84Section8FirstCombined χ c j (a.1*a.2)*
          (if (a.1*a.2:ℝ)≤lemma23PaperP D^(1/2:ℝ) then lemma102MainInitial χ c j a.1 a.2
           else if (a.1*a.2:ℝ)≤lemma23PaperP D^(251/500:ℝ) then lemma102MainLower χ c j a.1 a.2
           else lemma102MainUpper χ c j a.1 a.2) := rfl

end ZhangLS.Spec
#print axioms ZhangLS.Spec.lemma102Sum
#print axioms ZhangLS.Spec.lemma102Y1
#print axioms ZhangLS.Spec.lemma102Y2
#print axioms ZhangLS.Spec.lemma102MainInitial
#print axioms ZhangLS.Spec.lemma102MainLower
#print axioms ZhangLS.Spec.lemma102MainUpper
#print axioms ZhangLS.Spec.Lemma102Target
#print axioms ZhangLS.Spec.lemma102LogSum
#print axioms ZhangLS.Spec.lemma102LogMain
#print axioms ZhangLS.Spec.lemma102_actual_xi_perron
#print axioms ZhangLS.Spec.lemma102_actual_xi_perron_factored
#print axioms ZhangLS.Spec.lemma102PaperCircle
#print axioms ZhangLS.Spec.lemma102_zero_shift_norm
#print axioms ZhangLS.Spec.lemma102_unshifted_actual_finite_contour
#print axioms ZhangLS.Spec.lemma102_unshifted_actual_normalized_finite_contour
#print axioms ZhangLS.Spec.lemma102_unshifted_actual_ratio_right_bound
#print axioms ZhangLS.Spec.lemma102_unshiftedRightLineMajorant
#print axioms ZhangLS.Spec.lemma102_unshifted_right_line_majorant_nonneg
#print axioms ZhangLS.Spec.lemma102_unshifted_actual_right_line_numerator_bound
#print axioms ZhangLS.Spec.lemma102_unshifted_actual_right_line_integrable
#print axioms ZhangLS.Spec.lemma102_unshifted_actual_integrand_eq_log_kernel
#print axioms ZhangLS.Spec.lemma102_unshifted_actual_integrand_right_bound
#print axioms ZhangLS.Spec.lemma102_unshifted_actual_right_tails
#print axioms ZhangLS.Spec.lemma102_unshifted_integral_split_three
#print axioms ZhangLS.Spec.lemma102_unshifted_normalizer_norms
#print axioms ZhangLS.Spec.lemma102_unshifted_normalized_boundary_error
#print axioms ZhangLS.Spec.lemma102_unshifted_actual_sum_circle_boundary_error
#print axioms ZhangLS.Spec.lemma102_unshiftedPaperIntegrand
#print axioms ZhangLS.Spec.lemma102_unshiftedContourNumerator
#print axioms ZhangLS.Spec.Lemma102UnshiftedContourPoint
#print axioms ZhangLS.Spec.lemma102_unshifted_alpha_log_x_le_pi
#print axioms ZhangLS.Spec.lemma102_unshifted_actual_left_bound
#print axioms ZhangLS.Spec.lemma102_unshifted_actual_horizontal_bounds
#print axioms ZhangLS.Spec.lemma102_paper_left_exponential
#print axioms ZhangLS.Spec.lemma102_unshifted_actual_sum_circle_quantitative
#print axioms ZhangLS.Spec.lemma102_unshiftedContourTransferConstant
#print axioms ZhangLS.Spec.lemma102_unshifted_contour_transfer_constant_pos
#print axioms ZhangLS.Spec.lemma102_unshifted_actual_sum_circle_polynomial
#print axioms ZhangLS.Spec.lemma102_unshifted_actual_sum_circle_transfer
#print axioms ZhangLS.Spec.lemma102_exponential_triple_circle
#print axioms ZhangLS.Spec.lemma102_model_circle_integral
#print axioms ZhangLS.Spec.lemma102_circle_approximation_with_pi
#print axioms ZhangLS.Spec.lemma102_paper_circle_error_explicit
#print axioms ZhangLS.Spec.lemma102_paper_circle_error_with_pi
#print axioms ZhangLS.Spec.lemma102_unshifted_main_error_bounds
#print axioms ZhangLS.Spec.lemma102_unshifted_error_with_pi
#print axioms ZhangLS.Spec.lemma102_positive_log_sum
#print axioms ZhangLS.Spec.lemma102_sum_exact_bridge
#print axioms ZhangLS.Spec.lemma102_log_sum_zero_of_le_one
#print axioms ZhangLS.Spec.lemma102_sum_eq_tsum
#print axioms ZhangLS.Spec.lemma102_initial_main_identity
#print axioms ZhangLS.Spec.lemma102_lower_main_identity
#print axioms ZhangLS.Spec.lemma102_upper_main_identity
#print axioms ZhangLS.Spec.lemma102_second_difference_norm
#print axioms ZhangLS.Spec.lemma102_two_term_norm
#print axioms ZhangLS.Spec.lemma102_scale_error
#print axioms ZhangLS.Spec.lemma102_genuine_interior_error_with_pi
#print axioms ZhangLS.Spec.lemma102_boundary_xi_perron_bound
#print axioms ZhangLS.Spec.lemma102_boundary_xi_small_x
#print axioms ZhangLS.Spec.lemma102LogMainBound
#print axioms ZhangLS.Spec.lemma102_log_main_bound_pos
#print axioms ZhangLS.Spec.lemma102_log_main_bound
#print axioms ZhangLS.Spec.lemma102BoundaryBound
#print axioms ZhangLS.Spec.lemma102_genuine_boundary_bound
#print axioms ZhangLS.Spec.lemma102FullMain
#print axioms ZhangLS.Spec.lemma102MixedRaw
#print axioms ZhangLS.Spec.lemma102MixedMain
#print axioms ZhangLS.Spec.lemma102MixedHybrid
#print axioms ZhangLS.Spec.lemma102_mixed_source_exact
#print axioms ZhangLS.Spec.lemma102MixedInteriorConstant
#print axioms ZhangLS.Spec.lemma102_mixed_interior_constant_pos
#print axioms ZhangLS.Spec.lemma102_mixed_interior_quantitative
#print axioms ZhangLS.Spec.lemma102_full_main_bound
#print axioms ZhangLS.Spec.lemma102MixedBoundaryExponent
#print axioms ZhangLS.Spec.lemma102MixedBoundaryConstant
#print axioms ZhangLS.Spec.lemma102_mixed_boundary_constant_pos
#print axioms ZhangLS.Spec.lemma102_mixed_boundary_pointwise
#print axioms ZhangLS.Spec.lemma102_closed_weight_layer
#print axioms ZhangLS.Spec.lemma102TransitionPairs
#print axioms ZhangLS.Spec.lemma102_transition_weight_mass
#print axioms ZhangLS.Spec.lemma102MixedBoundaryTotalExponent
#print axioms ZhangLS.Spec.lemma102MixedBoundaryTotalConstant
#print axioms ZhangLS.Spec.lemma102_mixed_boundary_total_constant_pos
#print axioms ZhangLS.Spec.lemma102_mixed_boundary_quantitative
#print axioms ZhangLS.Spec.lemma102_mixed_interior_little_o
#print axioms ZhangLS.Spec.lemma102_mixed_boundary_little_o
#print axioms ZhangLS.Spec.lemma102_mixed_full_xi_replacement_little_o
#print axioms ZhangLS.Spec.lemma102MixedSource
#print axioms ZhangLS.Spec.lemma102_source_full_xi_replacement_little_o
