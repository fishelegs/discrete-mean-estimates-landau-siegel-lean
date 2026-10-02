import ZhangLS.Spec.Lemma44FiniteProductShift

/-!
# Full Mellin, smoothing and finite-shift regression

The paper-facing inputs below are the actual `Ψ₁`, `Ω₃`, and the already
verified explicit threshold. The full approximate functional equation is
still not asserted: reflected short/tail and horizontal bounds remain open.
-/

namespace ZhangLS.Spec

private theorem step77_modulus_one_lt {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : lemma23SectionFourModulusThreshold ≤ D) : 1 < D := by
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have hDp : (0 : ℝ) < D := by exact_mod_cast χ.modulus_pos
  have hDr : (1 : ℝ) < D := by
    have h := Real.exp_lt_exp.mpr (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3) hL)
    simpa [lemma23PaperL, Real.exp_log hDp] using h
  exact_mod_cast hDr

example {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D)
    (hψ : Lemma23InPsi1 χ ψ) {s : ℂ} (hs : Lemma44InOmega3 D s) :
    ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      (∫ t : ℝ, lemma44ProductMellinIntegrand χ ψ s (lemma44PaperGaussianScale D) 1 t * Complex.I) -
        lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p)) s‖ ≤
      (1 + 5 * Real.exp (2 * Real.pi) + lemma44InverseSquareMass) *
        lemma23PaperL D ^ (-180 : ℤ) :=
  lemma44_right_mellin_approximation χ ψ (step77_modulus_one_lt χ hD)
    (lemma44_parameters_at_explicit_threshold hD).1 hψ hs

example {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D)
    (hψ : Lemma23InPsi1 χ ψ) {s : ℂ} (hs : Lemma44InOmega3 D s) :
    letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    lemma44TruncatedProductMellin χ ψ s (lemma44PaperGaussianScale D) 1 (lemma23PaperL D ^ 20) =
      DirichletCharacter.LFunction ψ s *
          DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) s +
        lemma44TruncatedProductMellin χ ψ s (lemma44PaperGaussianScale D)
          (-s.re - 1 / 2) (lemma23PaperL D ^ 20) +
          lemma44ProductHorizontalError χ ψ s (lemma44PaperGaussianScale D)
            (-s.re - 1 / 2) (lemma23PaperL D ^ 20) := by
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  exact lemma44_product_finite_shift χ ψ hL hψ.1 hs _ (by positivity)

example {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D)
    (hψ : Lemma23InPsi1 χ ψ) {s : ℂ} (hs : Lemma44InOmega3 D s)
    {v : ℝ} (hv : |v| ≤ lemma23PaperL D ^ 20) :
    let w : ℂ := ((-s.re - 1 / 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I
    lemma44ProductMellinIntegrand χ ψ s (lemma44PaperGaussianScale D) (-s.re - 1 / 2) v =
      lemma44ActualZtilde χ ψ (s + w) *
        LSeries (fun n => lemma23NuArithmeticFunction χ n * ψ⁻¹ (n : ZMod p)) (1 - s - w) *
          Complex.exp (w * (Real.log (lemma44PaperGaussianScale D) : ℂ)) *
            lemma57OmegaOne D w / w :=
  lemma44_left_product_mellin_eq_reflected_series χ ψ
    (lemma44_parameters_at_explicit_threshold hD).1 hψ.1 hs _ hv

#print axioms lemma44_product_gaussian_mellin_identity
#print axioms lemma44_short_smoothing_error
#print axioms lemma44_gaussian_tail_summable_and_bound
#print axioms lemma44_full_gaussian_series_decomposition
#print axioms lemma44_right_mellin_approximation
#print axioms lemma44_product_mellin_rectangle_residue
#print axioms lemma44_simple_pole_rectangle_left
#print axioms lemma44_product_finite_shift
#print axioms lemma44_left_product_mellin_eq_reflected_series

end ZhangLS.Spec
