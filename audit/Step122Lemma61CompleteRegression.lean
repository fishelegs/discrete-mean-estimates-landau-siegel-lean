import ZhangLS.Spec.Lemma61

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Real Topology

example : ∃ C k : ℝ, 0 < C ∧ 0 < k ∧ ∃ D₀ : ℕ,
    ∀ {D p : ℕ} [NeZero p] (ψ : DirichletCharacter ℂ p),
      D₀ ≤ D → Lemma23InPsi (D := D) ψ → ∀ {s : ℂ},
      (|s.re - 1 / 2| < 2 * lemma44PaperAlpha D ∧
        |s.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 2) →
      ‖DirichletCharacter.LFunction ψ s - lemma61ActualK D ψ s -
        lemma23DirichletZ ψ s * lemma61ActualN D ψ⁻¹ (1 - s)‖ ≤
          C * lemma61ActualE1 D ψ s k := by
  simpa only [Lemma61Target,Lemma61InRegion] using lemma61_proved

example {D p : ℕ} [NeZero p] (ψ : DirichletCharacter ℂ p)
    (hψ : Lemma23InPsi (D := D) ψ) (hD : 1 < D) (hL : 64 ≤ lemma23PaperL D)
    {s : ℂ} (hs : Lemma61InRegion D s) :
    ‖DirichletCharacter.LFunction ψ s -
      (∑ n ∈ Finset.Icc 1 ⌈2 * lemma61PaperP4 D⌉₊,
        ψ (n : ZMod p) * exp (-s * (Real.log (n : ℝ) : ℂ)) *
          ((if 1 / 2 < lemma61PaperP4 D / n then
            zhangGaussianWeight D (lemma61PaperP4 D / n) else 0 : ℝ) : ℂ)) -
      lemma23DirichletZ ψ s *
        (∑ n ∈ Finset.Icc 1 ⌈2 * lemma56PaperT D ^ 2⌉₊,
          ψ⁻¹ (n : ZMod p) * exp (-(1 - s) * (Real.log (n : ℝ) : ℂ)) *
            ((if 1 / 2 < lemma56PaperT D ^ 2 / n then
              zhangGaussianWeight D (lemma56PaperT D ^ 2 / n) else 0 : ℝ) : ℂ))‖ ≤
      lemma61ApproximationConstant * lemma61ActualE1 D ψ s (1 / 8) := by
  simpa only [lemma61ActualK,lemma61ActualN,lemma61WeightedPolynomial,lemma61GaussianStar]
    using lemma61_actual_approximation_bound ψ hψ hD hL hs

example {D p : ℕ} [NeZero p] (ψ : DirichletCharacter ℂ p)
    (hψ : Lemma23InPsi (D := D) ψ) (hD : 1 < D) (hL : 64 ≤ lemma23PaperL D)
    {s : ℂ} (hs : Lemma61InRegion D s) :
    ‖DirichletCharacter.LFunction ψ s - lemma61ActualK D ψ s -
      lemma23DirichletZ ψ s * lemma61ActualN D ψ⁻¹ (1 - s)‖ ≤
      lemma61ApproximationConstant *
        (lemma23PaperL D ^ (-68 : ℤ) *
          (∫ v : ℝ in -(lemma23PaperL D ^ 20)..(lemma23PaperL D ^ 20),
            ‖∑ n ∈ (Finset.Icc 1 ⌈lemma56PaperT D ^ 3⌉₊).filter
              (fun (n : ℕ) => (n : ℝ) < lemma56PaperT D ^ 3),
                ψ (n : ZMod p) * exp (-(s + I * (v : ℂ)) * (Real.log (n : ℝ) : ℂ))‖ *
                  Real.exp (-(v ^ 2) / (4 * lemma23PaperL D ^ 30))) +
          Real.exp (-(lemma23PaperL D ^ 10) / 8)) := by
  convert lemma61_actual_approximation_bound ψ hψ hD hL hs using 1
  unfold lemma61ActualE1 lemma61ShortPolynomial
  congr 2
  ring

end ZhangLS.Spec

#print axioms ZhangLS.Spec.lemma61_short_mellin_eq_finite_sum
#print axioms ZhangLS.Spec.lemma61_short_mellin_integrable
#print axioms ZhangLS.Spec.lemma61_actual_short_gaussian_mellin
#print axioms ZhangLS.Spec.lemma61_short_star_sum_eq_weighted
#print axioms ZhangLS.Spec.lemma61_short_gaussian_cutoff_bound
#print axioms ZhangLS.Spec.lemma61_N_support_inside_short_sum
#print axioms ZhangLS.Spec.lemma61_actual_full_short_mellin_N_bound
#print axioms ZhangLS.Spec.lemma61_short_right_gaussian_bound
#print axioms ZhangLS.Spec.lemma61_short_gaussian_exponent_absorption
#print axioms ZhangLS.Spec.lemma61_actual_short_right_truncation
#print axioms ZhangLS.Spec.lemma61_actual_finite_short_mellin_N_bound
#print axioms ZhangLS.Spec.lemma61_reciprocal_model_reflection
#print axioms ZhangLS.Spec.lemma61_reciprocal_model_vertical_identity
#print axioms ZhangLS.Spec.lemma61_actual_finite_reciprocal_model_N_bound
#print axioms ZhangLS.Spec.lemma61_actual_original_left_integrand_split
#print axioms ZhangLS.Spec.lemma61_reciprocal_model_interval_integrable
#print axioms ZhangLS.Spec.lemma61_actual_left_tail_interval_integrable
#print axioms ZhangLS.Spec.lemma61_actual_original_left_integral_split
#print axioms ZhangLS.Spec.lemma61_actual_original_left_N_bound
#print axioms ZhangLS.Spec.lemma61_family_modulus_bound
#print axioms ZhangLS.Spec.lemma61_shifted_argument_norm_bounds
#print axioms ZhangLS.Spec.lemma61_actual_L_quarter_plane_bound
#print axioms ZhangLS.Spec.lemma61_P4_exponential_rectangle_bound
#print axioms ZhangLS.Spec.lemma61_T_left_rectangle_exponential_bound
#print axioms ZhangLS.Spec.lemma61_actual_shifted_L_positive_bound
#print axioms ZhangLS.Spec.lemma61_actual_shifted_L_dual_bound
#print axioms ZhangLS.Spec.lemma61_actual_positive_L_P4_bound
#print axioms ZhangLS.Spec.lemma61_actual_negative_L_P4_bound
#print axioms ZhangLS.Spec.lemma61_actual_L_P4_rectangle_bound
#print axioms ZhangLS.Spec.lemma61_actual_horizontal_L_point_bound
#print axioms ZhangLS.Spec.lemma61_horizontal_L_exponent_absorption
#print axioms ZhangLS.Spec.lemma61_actual_horizontal_L_integral_bound
#print axioms ZhangLS.Spec.lemma61_actual_approximation_bound
#print axioms ZhangLS.Spec.lemma61_approximation_constant_pos
#print axioms ZhangLS.Spec.lemma61_parameters_at_threshold
#print axioms ZhangLS.Spec.lemma61_proved
