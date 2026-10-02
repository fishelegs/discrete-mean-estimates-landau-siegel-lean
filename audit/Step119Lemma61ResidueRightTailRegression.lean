import ZhangLS.Spec.Lemma61SingleResidue
import ZhangLS.Spec.Lemma61RightTruncation

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Real Topology
example {D p : ℕ} [NeZero p] (ψ : DirichletCharacter ℂ p)
    (hψ : Lemma23InPsi (D := D) ψ) (s : ℂ) {H : ℝ} (hH : 0 < H) :
    lemma61RectangleBoundaryIntegral
      (fun w : ℂ => DirichletCharacter.LFunction ψ (s + w) *
        Complex.exp (w * (Real.log (lemma61PaperP4 D) : ℂ)) *
        lemma57OmegaOne D w / w) H =
      2 * (Real.pi : ℂ) * I * DirichletCharacter.LFunction ψ s := by
  exact lemma61_actual_wide_rectangle_residue ψ hψ s (lemma61PaperP4 D) hH

example {p : ℕ} [NeZero p] (ψ : DirichletCharacter ℂ p) (v : ℝ) :
    ‖DirichletCharacter.LFunction ψ ((2 : ℂ) + (v : ℂ) * I)‖ ≤
      ∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹ := by
  exact lemma61_single_series_norm_le_square_mass ψ (by simp)

example {D p : ℕ} [NeZero p] (ψ : DirichletCharacter ℂ p) (hD : 1 < D)
    (hL : 64 ≤ lemma23PaperL D) {s : ℂ}
    (hre : |s.re - 1 / 2| < 2 * lemma44PaperAlpha D)
    (him : |s.im - (2 * Real.pi * lemma23PaperL D ^ 519)| <
      lemma23PaperL D ^ 405 + 2) :
    ‖(2 * (Real.pi : ℂ) * I)⁻¹ *
      (∫ v : ℝ in -(lemma23PaperL D ^ 20)..(lemma23PaperL D ^ 20),
        DirichletCharacter.LFunction ψ (s + ((2 : ℂ) + (v : ℂ) * I)) *
          Complex.exp (((2 : ℂ) + (v : ℂ) * I) * (Real.log (lemma61PaperP4 D) : ℂ)) *
          lemma57OmegaOne D ((2 : ℂ) + (v : ℂ) * I) /
            ((2 : ℂ) + (v : ℂ) * I) * I) - lemma61ActualK D ψ s‖ ≤
        9 * lemma44InverseSquareMass * Real.exp (-(lemma23PaperL D ^ 10) / 8) := by
  apply lemma61_actual_finite_right_K_bound ψ hD hL
  refine ⟨hre,?_⟩
  simpa [lemma23PaperCenter] using him
end ZhangLS.Spec

#print axioms ZhangLS.Spec.lemma61_family_nonprincipal
#print axioms ZhangLS.Spec.lemma61_single_mellin_numerator_entire
#print axioms ZhangLS.Spec.lemma61_single_mellin_rectangle_residue
#print axioms ZhangLS.Spec.lemma61_actual_single_functional_equation
#print axioms ZhangLS.Spec.lemma61_interval_integral_double
#print axioms ZhangLS.Spec.lemma61_rectangle_scale_identity
#print axioms ZhangLS.Spec.lemma61_simple_pole_wide_rectangle
#print axioms ZhangLS.Spec.lemma61_actual_wide_rectangle_residue
#print axioms ZhangLS.Spec.lemma61_actual_rectangle_identity
#print axioms ZhangLS.Spec.lemma61_single_series_norm_le_square_mass
#print axioms ZhangLS.Spec.lemma61_right_mellin_gaussian_bound
#print axioms ZhangLS.Spec.lemma61_right_gaussian_exponent_absorption
#print axioms ZhangLS.Spec.lemma61_actual_right_mellin_truncation
#print axioms ZhangLS.Spec.lemma61_mellin_normalization_norm_le_one
#print axioms ZhangLS.Spec.lemma61_actual_finite_right_K_bound
