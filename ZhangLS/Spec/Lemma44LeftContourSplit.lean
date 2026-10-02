import ZhangLS.Spec.Lemma44ReflectedSeriesSplit
import ZhangLS.Spec.Lemma44ReflectedPolynomialContours

/-! # The actual three-part split of the initial left contour -/

namespace ZhangLS.Spec

open Complex MeasureTheory Set

set_option maxHeartbeats 1000000

theorem lemma44_left_product_contour_decomposition {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hs : Lemma44InOmega3 D s) :
    lemma44TruncatedProductMellin χ ψ s (lemma44PaperGaussianScale D)
      (-s.re - 1 / 2) (lemma23PaperL D ^ 20) =
      lemma44TruncatedReflectedPolynomial χ ψ s
        (lemma23ActualSectionFourF χ (fun n => ψ⁻¹ (n : ZMod p)))
          (-s.re - 1 / 2) (lemma23PaperL D ^ 20) +
        lemma44TruncatedReflectedPolynomial χ ψ s (lemma44LongDirichletSum χ ψ⁻¹)
          (-s.re - 1 / 2) (lemma23PaperL D ^ 20) +
        (2 * (Real.pi : ℂ) * I)⁻¹ *
          (∫ v : ℝ in -(lemma23PaperL D ^ 20)..lemma23PaperL D ^ 20,
            lemma44ReflectedTailContourIntegrand χ ψ s v * I) := by
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have hre := lemma44_omega3_re_pos hL hs
  have hσ := (lemma44_initial_left_shift_abs_re hL hs 0).trans (by norm_num : (3 : ℝ) ≤ 15)
  simp only [lemma44_initial_left_shift_re] at hσ
  have hσ0 : -s.re - 1 / 2 ≠ 0 := by linarith only [hre]
  let short := lemma23ActualSectionFourF χ (fun n => ψ⁻¹ (n : ZMod p))
  let middle := lemma44LongDirichletSum χ ψ⁻¹
  have hshort := (lemma44_reflected_polynomial_intervalIntegrable χ ψ hL hs short
    (lemma44_short_polynomial_differentiable χ ψ⁻¹) hσ hσ0).mul_const I
  have hmiddle := (lemma44_reflected_polynomial_intervalIntegrable χ ψ hL hs middle
    (lemma44_long_polynomial_differentiable χ ψ⁻¹) hσ hσ0).mul_const I
  have htail := (lemma44_reflected_tail_contour_intervalIntegrable χ ψ hD hs).mul_const I
  have hpoint (v : ℝ) (hv : |v| ≤ lemma23PaperL D ^ 20) :
      lemma44ProductMellinIntegrand χ ψ s (lemma44PaperGaussianScale D) (-s.re - 1 / 2) v * I =
        lemma44ReflectedPolynomialNumerator χ ψ s short (lemma44InitialLeftShift s v) /
          lemma44InitialLeftShift s v * I +
        lemma44ReflectedPolynomialNumerator χ ψ s middle (lemma44InitialLeftShift s v) /
          lemma44InitialLeftShift s v * I + lemma44ReflectedTailContourIntegrand χ ψ s v * I := by
    have hfe := lemma44_left_product_mellin_eq_reflected_series χ ψ hL hψ hs
      (lemma44PaperGaussianScale D) hv
    have hmir : (1 - s - lemma44InitialLeftShift s v).re = 3 / 2 := by simp; ring
    have hsplit := lemma44_reflected_series_decomposition χ ψ⁻¹ hL hmir
    change lemma44ProductMellinIntegrand χ ψ s (lemma44PaperGaussianScale D)
      (-s.re - 1 / 2) v = _ at hfe
    rw [hfe]
    change _ = _ at hsplit
    change (lemma44ActualZtilde χ ψ (s + lemma44InitialLeftShift s v) *
      LSeries (fun n => lemma23NuArithmeticFunction χ n * ψ⁻¹ (n : ZMod p))
        (1 - s - lemma44InitialLeftShift s v) *
        exp (lemma44InitialLeftShift s v * (Real.log (lemma44PaperGaussianScale D) : ℂ)) *
        lemma57OmegaOne D (lemma44InitialLeftShift s v) / lemma44InitialLeftShift s v) * I = _
    rw [hsplit]
    unfold lemma44ReflectedPolynomialNumerator lemma44ReflectedTailContourIntegrand
    dsimp only [short, middle]
    ring
  unfold lemma44TruncatedProductMellin lemma44TruncatedReflectedPolynomial
  have hT : 0 ≤ lemma23PaperL D ^ 20 := by positivity
  have he : (∫ v : ℝ in -(lemma23PaperL D ^ 20)..lemma23PaperL D ^ 20,
      lemma44ProductMellinIntegrand χ ψ s (lemma44PaperGaussianScale D) (-s.re - 1 / 2) v * I) =
      ∫ v : ℝ in -(lemma23PaperL D ^ 20)..lemma23PaperL D ^ 20,
        ((lemma44ReflectedPolynomialNumerator χ ψ s short (lemma44InitialLeftShift s v) /
          lemma44InitialLeftShift s v * I +
        lemma44ReflectedPolynomialNumerator χ ψ s middle (lemma44InitialLeftShift s v) /
          lemma44InitialLeftShift s v * I) + lemma44ReflectedTailContourIntegrand χ ψ s v * I) := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le (by linarith : -(lemma23PaperL D ^ 20) ≤ lemma23PaperL D ^ 20)] at hv
    exact hpoint v (abs_le.mpr hv)
  rw [he]
  dsimp only [lemma44InitialLeftShift]
  rw [intervalIntegral.integral_add (hshort.add hmiddle) htail,
    intervalIntegral.integral_add hshort hmiddle]
  dsimp only [short, middle]
  ring

theorem lemma44_middle_reflected_polynomial_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    {s : ℂ} (hs : Lemma44InOmega3 D s) :
    ‖lemma44TruncatedReflectedPolynomial χ ψ s (lemma44LongDirichletSum χ ψ⁻¹)
      (-lemma44PaperAlpha D) (lemma23PaperL D ^ 20)‖ ≤
      5 * Real.exp (3 + 4 * Real.pi) * lemma23PaperL D ^ (-179 : ℤ) := by
  have h := lemma44_truncated_middle_contour_bound χ ψ hD hψ hs
  have hT : 0 ≤ lemma23PaperL D ^ 20 := by positivity
  unfold lemma44TruncatedReflectedPolynomial lemma44ReflectedPolynomialNumerator
  rw [intervalIntegral.integral_of_le (by linarith : -(lemma23PaperL D ^ 20) ≤ lemma23PaperL D ^ 20)]
  simpa only [ofReal_neg, lemma44MiddleContourIntegrand] using h

end ZhangLS.Spec
