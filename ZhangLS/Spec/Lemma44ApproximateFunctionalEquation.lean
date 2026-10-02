import ZhangLS.Spec.Lemma44LeftContourSplit
import ZhangLS.Spec.Lemma44ReflectedPolynomialBounds

/-!
# Lemma 4.4 for the actual Dirichlet L-functions

All contour identities, convergence witnesses, and errors are proved from
the genuine family and region. The final constant is absolute: its two
series masses have no modulus or character parameters.
-/

namespace ZhangLS.Spec

open Complex MeasureTheory

set_option maxHeartbeats 2000000

noncomputable def lemma44ErrorConstant180 : ℝ :=
  (1 + 5 * Real.exp (2 * Real.pi) + lemma44InverseSquareMass) +
    8 * lemma44DivisorSeriesMass * Real.exp 1 + 2 * Real.exp 1 +
    26 * Real.exp 1 + 6 * Real.exp 1 +
    4 * lemma44DivisorSeriesMass * Real.exp (1 + (9 / 5 : ℝ) * Real.pi) +
    2097152 * Real.exp 1

noncomputable def lemma44ErrorConstant : ℝ :=
  lemma44ErrorConstant180 + 5 * Real.exp (3 + 4 * Real.pi)

theorem lemma44_error_constant180_nonneg : 0 ≤ lemma44ErrorConstant180 := by
  have hd := lemma44_divisor_series_mass_nonneg
  have hi : 0 ≤ lemma44InverseSquareMass := tsum_nonneg (fun _ => by positivity)
  unfold lemma44ErrorConstant180
  positivity

theorem lemma44_error_constant_pos : 0 < lemma44ErrorConstant := by
  unfold lemma44ErrorConstant
  exact add_pos_of_nonneg_of_pos lemma44_error_constant180_nonneg (by positivity)

private theorem norm_eight_terms (a b c d e f g h : ℂ) :
    ‖a - b - c - d + e + f - g - h‖ ≤
      ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖f‖ + ‖g‖ + ‖h‖ := by
  calc
    _ ≤ ‖a - b - c - d + e + f - g‖ + ‖h‖ := norm_sub_le _ _
    _ ≤ (‖a - b - c - d + e + f‖ + ‖g‖) + ‖h‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ ((‖a - b - c - d + e‖ + ‖f‖) + ‖g‖) + ‖h‖ := by gcongr; exact norm_add_le _ _
    _ ≤ (((‖a - b - c - d‖ + ‖e‖) + ‖f‖) + ‖g‖) + ‖h‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ((((‖a - b - c‖ + ‖d‖) + ‖e‖) + ‖f‖) + ‖g‖) + ‖h‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ (((((‖a - b‖ + ‖c‖) + ‖d‖) + ‖e‖) + ‖f‖) + ‖g‖) + ‖h‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ _ := by gcongr; exact norm_sub_le _ _

/-- Lemma 4.4: the actual product equals the two actual short polynomials
with a uniform, absolute `O(L^-179)` error on the full paper region. -/
theorem lemma44_actual_approximate_functional_equation {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    {s : ℂ} (hs : Lemma44InOmega3 D s) :
    letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    ‖DirichletCharacter.LFunction ψ s *
        DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) s -
      (lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p)) s +
        lemma44ActualZtilde χ ψ s *
          lemma23ActualSectionFourF χ (fun n => ψ⁻¹ (n : ZMod p)) (1 - s))‖ ≤
      lemma44ErrorConstant * lemma23PaperL D ^ (-179 : ℤ) := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have hT : 0 < lemma23PaperL D ^ 20 := pow_pos (by linarith) 20
  let F := lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p)) s
  let f := lemma23ActualSectionFourF χ (fun n => ψ⁻¹ (n : ZMod p))
  let m := lemma44LongDirichletSum χ ψ⁻¹
  let R := (2 * (Real.pi : ℂ) * I)⁻¹ *
    (∫ v : ℝ, lemma44ProductMellinIntegrand χ ψ s (lemma44PaperGaussianScale D) 1 v * I)
  let Rt := lemma44TruncatedProductMellin χ ψ s (lemma44PaperGaussianScale D) 1 (lemma23PaperL D ^ 20)
  let Sr := lemma44TruncatedReflectedPolynomial χ ψ s f 10 (lemma23PaperL D ^ 20)
  let Mr := lemma44TruncatedReflectedPolynomial χ ψ s m (-lemma44PaperAlpha D) (lemma23PaperL D ^ 20)
  let Hs := lemma44HorizontalError (fun w => lemma44ReflectedPolynomialNumerator χ ψ s f w / w)
    (-s.re - 1 / 2) 10 (lemma23PaperL D ^ 20)
  let Hm := lemma44HorizontalError (fun w => lemma44ReflectedPolynomialNumerator χ ψ s m w / w)
    (-s.re - 1 / 2) (-lemma44PaperAlpha D) (lemma23PaperL D ^ 20)
  let Tail := (2 * (Real.pi : ℂ) * I)⁻¹ *
    (∫ v : ℝ in -(lemma23PaperL D ^ 20)..lemma23PaperL D ^ 20,
      lemma44ReflectedTailContourIntegrand χ ψ s v * I)
  let Hp := lemma44ProductHorizontalError χ ψ s (lemma44PaperGaussianScale D)
    (-s.re - 1 / 2) (lemma23PaperL D ^ 20)
  have hprod := lemma44_product_finite_shift χ ψ hL hψ.1 hs (lemma44PaperGaussianScale D) hT
  have hleft := lemma44_left_product_contour_decomposition χ ψ hD hψ.1 hs
  have hshort := lemma44_reflected_polynomial_residue_shift χ ψ hL hs f
    (lemma44_short_polynomial_differentiable χ ψ⁻¹)
  have hmiddle := lemma44_reflected_polynomial_middle_shift χ ψ hL hs m
    (lemma44_long_polynomial_differentiable χ ψ⁻¹)
  have he : DirichletCharacter.LFunction ψ s *
      DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) s -
        (F + lemma44ActualZtilde χ ψ s * f (1 - s)) =
      (R - F) - (R - Rt) - Sr - Mr + Hs + Hm - Tail - Hp := by
    dsimp only [F, R, Rt, Sr, Mr, Hs, Hm, Tail, Hp, f, m] at *
    linear_combination -hprod - hleft + hshort + hmiddle
  have hR := lemma44_right_mellin_approximation χ ψ
    (lemma44_modulus_one_lt_at_threshold χ hD) hL hψ hs
  have hRt := lemma44_right_vertical_truncation_bound χ ψ hD hs
  have hSr := lemma44_short_right_contour_bound χ ψ hD hψ.1 hs
  have hMr := lemma44_middle_reflected_polynomial_bound χ ψ hD hψ hs
  have hHs := lemma44_short_horizontal_error_bound χ ψ hD hψ.1 hs
  have hHm := lemma44_long_horizontal_error_bound χ ψ hD hψ.1 hs
  have hTail := lemma44_reflected_tail_contour_bound χ ψ hD hψ.1 hs
  have hHp := lemma44_product_horizontal_error_bound χ ψ hD hψ.1 hs
  change ‖R - F‖ ≤ _ at hR
  change ‖R - Rt‖ ≤ _ at hRt
  change ‖Sr‖ ≤ _ at hSr
  change ‖Mr‖ ≤ _ at hMr
  change ‖Hs‖ ≤ _ at hHs
  change ‖Hm‖ ≤ _ at hHm
  change ‖Tail‖ ≤ _ at hTail
  change ‖Hp‖ ≤ _ at hHp
  have hn := norm_eight_terms (R - F) (R - Rt) Sr Mr Hs Hm Tail Hp
  have hpow : lemma23PaperL D ^ (-180 : ℤ) ≤ lemma23PaperL D ^ (-179 : ℤ) :=
    zpow_le_zpow_right₀ (by linarith : 1 ≤ lemma23PaperL D) (by norm_num)
  change ‖DirichletCharacter.LFunction ψ s *
    DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) s -
      (F + lemma44ActualZtilde χ ψ s * f (1 - s))‖ ≤ _
  rw [he]
  calc
    _ ≤ lemma44ErrorConstant180 * lemma23PaperL D ^ (-180 : ℤ) +
        (5 * Real.exp (3 + 4 * Real.pi)) * lemma23PaperL D ^ (-179 : ℤ) := by
      unfold lemma44ErrorConstant180
      nlinarith only [hn, hR, hRt, hSr, hMr, hHs, hHm, hTail, hHp]
    _ ≤ lemma44ErrorConstant * lemma23PaperL D ^ (-179 : ℤ) := by
      have hm := mul_le_mul_of_nonneg_left hpow lemma44_error_constant180_nonneg
      unfold lemma44ErrorConstant
      nlinarith only [hm]

/-- The absolute constant is positive, and the threshold is an explicit
computable natural number independent of both characters. -/
theorem lemma44_uniform_error_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (D p : ℕ) [NeZero p]
      (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p),
      lemma23SectionFourModulusThreshold ≤ D → Lemma23InPsi1 χ ψ →
      ∀ s : ℂ, Lemma44InOmega3 D s →
      letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
      ‖DirichletCharacter.LFunction ψ s *
          DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) s -
        (lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p)) s +
          lemma44ActualZtilde χ ψ s *
            lemma23ActualSectionFourF χ (fun n => ψ⁻¹ (n : ZMod p)) (1 - s))‖ ≤
        C * lemma23PaperL D ^ (-179 : ℤ) := by
  refine ⟨lemma44ErrorConstant, lemma44_error_constant_pos, ?_⟩
  intro D p _ χ ψ hD hψ s hs
  exact lemma44_actual_approximate_functional_equation χ ψ hD hψ hs

end ZhangLS.Spec
