import ZhangLS.Spec.Lemma61ActualZError

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Set MeasureTheory
open scoped Real Topology ComplexConjugate
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

example {z : ℂ} (him : 1 ≤ |z.im|) :
    ‖logDeriv Complex.Gamma z - Complex.log ((z.im : ℂ) * I)‖ ≤
      (12 + |z.re|) / |z.im| := lemma61_Gamma_logDeriv_im_axis_all him

example {D p : ℕ} [NeZero p] (ψ : DirichletCharacter ℂ p)
    (hψ : Lemma23InPsi (D := D) ψ) (hL : 3 ≤ lemma23PaperL D) {s w : ℂ}
    (hs : |s.re - 1 / 2| < 2 * lemma44PaperAlpha D ∧
      |s.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 2)
    (hwre : |w.re| ≤ 4 * lemma44PaperAlpha D) (hwim : |w.im| ≤ lemma23PaperL D ^ 20) :
    ‖(lemma23DirichletZ ψ (s + w) - lemma23DirichletZ ψ s *
      ((lemma23PaperP D * lemma51PaperT0 D : ℝ) : ℂ) ^ (-w)) / w‖ ≤
        (35 * Real.exp (238 * Real.pi)) * lemma23PaperL D ^ (-68 : ℤ) :=
  lemma61_actual_complex_Z_shift ψ hψ hL hs hwre hwim

example {D p : ℕ} [NeZero p] (ψ : DirichletCharacter ℂ p)
    (hψ : Lemma23InPsi (D := D) ψ) (hL : 3 ≤ lemma23PaperL D) {s : ℂ}
    (hs : |s.re - 1 / 2| < 2 * lemma44PaperAlpha D ∧
      |s.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 2) (k : ℝ) :
    ‖(2 * (Real.pi : ℂ) * I)⁻¹ *
      (∫ v in (-(lemma23PaperL D ^ 20))..(lemma23PaperL D ^ 20),
        (((lemma23DirichletZ ψ (s + (((1 - 2 * s.re : ℝ) : ℂ) + I * (v : ℂ))) -
          lemma23DirichletZ ψ s *
            ((lemma23PaperP D * lemma51PaperT0 D : ℝ) : ℂ) ^
              (-(((1 - 2 * s.re : ℝ) : ℂ) + I * (v : ℂ)))) /
            (((1 - 2 * s.re : ℝ) : ℂ) + I * (v : ℂ))) *
          lemma61ShortPolynomial D ψ⁻¹ (1 - s - (((1 - 2 * s.re : ℝ) : ℂ) + I * (v : ℂ))) *
          exp ((((1 - 2 * s.re : ℝ) : ℂ) + I * (v : ℂ)) * (Real.log (lemma61PaperP4 D) : ℂ)) *
          lemma57OmegaOne D (((1 - 2 * s.re : ℝ) : ℂ) + I * (v : ℂ))) * I)‖ ≤
      (35 * Real.exp (246 * Real.pi + 1)) *
        (lemma23PaperL D ^ (-68 : ℤ) *
          (∫ v in (-(lemma23PaperL D ^ 20))..(lemma23PaperL D ^ 20),
            ‖lemma61ShortPolynomial D ψ (s + I * (v : ℂ))‖ *
              Real.exp (-(v ^ 2) / (4 * lemma23PaperL D ^ 30))) +
          Real.exp (-k * lemma23PaperL D ^ 10)) :=
  lemma61_actual_normalized_error_contour_bound ψ hψ hL hs k


#print axioms lemma61_Gamma_logDeriv_recurrence_bound
#print axioms lemma61_Gamma_logDeriv_im_axis_positive
#print axioms lemma61_Gamma_logDeriv_im_axis_all
#print axioms lemma61_GammaR_logDeriv_im_axis_all
#print axioms lemma61_gammaFactor_logDeriv_im_axis_all
#print axioms lemma61_DirichletZ_logDeriv_all_real
#print axioms lemma61_wide_height_data
#print axioms lemma61_DirichletZ_logDeriv_at_T0_wide
#print axioms lemma61_family_Z_logDeriv_normalized_wide
#print axioms lemma61_family_Z_log_modulus_wide
#print axioms lemma61_family_Z_norm_model_wide
#print axioms lemma61_six_alpha_le_quarter
#print axioms lemma61_PT0_log_bounds
#print axioms lemma61_family_Z_norm_thin
#print axioms lemma61_thin_real_in_wide
#print axioms lemma61_complex_transport
#print axioms lemma61_shift_segment_bounds
#print axioms lemma61_actual_complex_Z_shift
#print axioms lemma61_short_polynomial_conjugation
#print axioms lemma61_error_contour_reflection
#print axioms lemma61_error_contour_bounds
#print axioms lemma61_error_contour_short_norm
#print axioms lemma61_P4_log_nonneg
#print axioms lemma61_P4_exponential_thin_bound
#print axioms lemma61_omega_one_thin_gaussian_bound
#print axioms lemma61_actual_error_contour_point_bound
#print axioms lemma61_actual_error_contour_integral_bound
#print axioms lemma61_actual_normalized_error_contour_bound
end ZhangLS.Spec
