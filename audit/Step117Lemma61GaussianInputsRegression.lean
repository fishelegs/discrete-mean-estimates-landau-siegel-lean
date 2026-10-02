import ZhangLS.Spec.Lemma61GaussianCutoff

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Real Topology
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

example {D p : ℕ} (ψ : DirichletCharacter ℂ p) (s : ℂ) :
    (∑' n : ℕ, if n = 0 then 0 else ψ (n : ZMod p) *
      Complex.exp (-s * (Real.log (n : ℝ) : ℂ)) *
        ((if (1 / 2 : ℝ) < lemma61PaperP4 D / n then
          zhangGaussianWeight D (lemma61PaperP4 D / n) else 0 : ℝ) : ℂ)) =
    ∑ n ∈ Finset.Icc 1 ⌈2 * lemma61PaperP4 D⌉₊, ψ (n : ZMod p) *
      Complex.exp (-s * (Real.log (n : ℝ) : ℂ)) *
        ((if (1 / 2 : ℝ) < lemma61PaperP4 D / n then
          zhangGaussianWeight D (lemma61PaperP4 D / n) else 0 : ℝ) : ℂ) :=
  lemma61_actual_weighted_tsum_eq_finite ψ (lemma61PaperP4 D) s

example {D p : ℕ} [NeZero p] (ψ : DirichletCharacter ℂ p)
    (hD : 1 < D) (hL : 3 ≤ lemma23PaperL D) {s : ℂ}
    (hs : |s.re - 1 / 2| < 2 * lemma44PaperAlpha D ∧
      |s.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 2)
    {σ : ℝ} (hσ : 0 < σ) (hsσ : 1 < s.re + σ) :
    ‖(2 * (Real.pi : ℂ) * I)⁻¹ * (∫ t : ℝ,
        (DirichletCharacter.LFunction ψ (s + ((σ : ℂ) + (t : ℂ) * I)) *
          exp (((σ : ℂ) + (t : ℂ) * I) * (Real.log (lemma61PaperP4 D) : ℂ)) *
          lemma57OmegaOne D ((σ : ℂ) + (t : ℂ) * I) /
          ((σ : ℂ) + (t : ℂ) * I)) * I) -
      (∑ n ∈ Finset.Icc 1 ⌈2 * lemma61PaperP4 D⌉₊, ψ (n : ZMod p) *
        Complex.exp (-s * (Real.log (n : ℝ) : ℂ)) *
          ((if (1 / 2 : ℝ) < lemma61PaperP4 D / n then
            zhangGaussianWeight D (lemma61PaperP4 D / n) else 0 : ℝ) : ℂ))‖ ≤
      lemma44InverseSquareMass * Real.exp (-(lemma23PaperL D ^ 10)) := by
  change ‖(2 * (Real.pi : ℂ) * I)⁻¹ *
      (∫ t : ℝ, lemma61RightMellinIntegrand (D := D) ψ s (lemma61PaperP4 D) σ t * I) -
        lemma61ActualK D ψ s‖ ≤ _
  rw [lemma61_actual_K_right_mellin_identity ψ s hD hσ hsσ,add_sub_cancel_left]
  exact lemma61_actual_K_cutoff_correction_bound ψ hD hL (lemma61_region_real_parts hL hs).1.le

example {D p : ℕ} (ψ : DirichletCharacter ℂ p) (hD : 1 < D)
    (hL : 3 ≤ lemma23PaperL D) {s : ℂ} (hs : Lemma61InRegion D s) (k : ℝ) :
    0 < lemma23PaperL D ^ (-68 : ℤ) *
      (∫ v in (-(lemma23PaperL D ^ 20))..(lemma23PaperL D ^ 20),
        ‖(∑ n ∈ (Finset.Icc 1 ⌈lemma56PaperT D ^ 3⌉₊).filter
          (fun (n : ℕ) => (n : ℝ) < lemma56PaperT D ^ 3),
          ψ (n : ZMod p) * Complex.exp (-(s + I * (v : ℂ)) * (Real.log (n : ℝ) : ℂ)))‖ *
          Real.exp (-(v ^ 2) / (4 * lemma23PaperL D ^ 30))) +
        Real.exp (-k * lemma23PaperL D ^ 10) ∧
    ‖∑' n : ℕ, LSeries.term (fun m => ψ⁻¹ (m : ZMod p)) (1 - s) n *
      ((zhangGaussianWeight D (lemma56PaperT D ^ 2 / n) -
        (if (1 / 2 : ℝ) < lemma56PaperT D ^ 2 / n then
          zhangGaussianWeight D (lemma56PaperT D ^ 2 / n) else 0) : ℝ) : ℂ)‖ ≤
      lemma44InverseSquareMass * Real.exp (-(lemma23PaperL D ^ 10)) := by
  change 0 < lemma61ActualE1 D ψ s k ∧
    ‖lemma61GaussianCutoffCorrection D ψ⁻¹ (lemma56PaperT D ^ 2) (1 - s)‖ ≤ _
  exact ⟨lemma61_E1_pos ψ s k,
    lemma61_actual_N_cutoff_correction_bound ψ⁻¹ hD hL (lemma61_region_real_parts hL hs).2.le⟩


#print axioms lemma61_gaussian_star_below_half
#print axioms lemma61_gaussian_star_above_half
#print axioms lemma61_gaussian_star_nonneg
#print axioms lemma61_P4_pos
#print axioms lemma61_complementary_scales
#print axioms lemma61_weighted_term_vanishes_outside
#print axioms lemma61_actual_weighted_tsum_eq_finite
#print axioms lemma61_weighted_polynomial_continuous
#print axioms lemma61_short_polynomial_continuous
#print axioms lemma61_error_integrand_continuous
#print axioms lemma61_error_integrand_interval_integrable
#print axioms lemma61_E1_pos
#print axioms lemma61_gaussian_star_norm_le_one
#print axioms lemma61_gaussian_reciprocal_complement
#print axioms lemma61_weighted_term_eq_LSeries_term
#print axioms lemma61_actual_weighted_terms_summable
#print axioms lemma61_region_real_parts
#print axioms lemma61_weighted_polynomial_differentiable
#print axioms lemma61_short_polynomial_differentiable
#print axioms lemma61_omega_one_imaginary_axis
#print axioms lemma61_right_mellin_integrand_eq_tsum
#print axioms lemma61_actual_right_gaussian_mellin
#print axioms lemma61_actual_right_mellin_with_cutoff_correction
#print axioms lemma61_actual_K_right_mellin_identity
#print axioms lemma61_cutoff_endpoint_budget
#print axioms lemma61_cutoff_gaussian_weight_bound
#print axioms lemma61_cutoff_correction_term_bound
#print axioms lemma61_cutoff_correction_summable_and_bound
#print axioms lemma61_P4_log_bound
#print axioms lemma61_T_squared_log_bound
#print axioms lemma61_actual_K_cutoff_correction_bound
#print axioms lemma61_actual_N_cutoff_correction_bound
end ZhangLS.Spec
