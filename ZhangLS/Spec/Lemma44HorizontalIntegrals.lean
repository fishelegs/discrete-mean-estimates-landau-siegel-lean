import ZhangLS.Spec.Lemma44HorizontalKernel
import ZhangLS.Spec.Lemma44RightVerticalTruncation

/-! # The normalized horizontal errors of the finite product shift -/

namespace ZhangLS.Spec

open Complex MeasureTheory Set

set_option maxHeartbeats 1000000

noncomputable def lemma44HorizontalError (f : ℂ → ℂ) (a b T : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ) * I)⁻¹ *
    ((∫ x : ℝ in a..b, f ((x : ℂ) + (T : ℂ) * I)) -
      (∫ x : ℝ in a..b, f ((x : ℂ) - (T : ℂ) * I)))

theorem lemma44_horizontal_error_bound (f : ℂ → ℂ) {a b T K : ℝ}
    (hK : 0 ≤ K)
    (hp : ∀ x ∈ uIcc a b, ‖f ((x : ℂ) + (T : ℂ) * I)‖ ≤ K)
    (hm : ∀ x ∈ uIcc a b, ‖f ((x : ℂ) - (T : ℂ) * I)‖ ≤ K) :
    ‖lemma44HorizontalError f a b T‖ ≤ 2 * K * |b - a| := by
  have htop := intervalIntegral.norm_integral_le_of_norm_le_const
    (fun x hx => hp x (uIoc_subset_uIcc hx))
  have hbottom := intervalIntegral.norm_integral_le_of_norm_le_const
    (fun x hx => hm x (uIoc_subset_uIcc hx))
  unfold lemma44HorizontalError
  rw [norm_mul]
  calc
    _ ≤ 1 * ‖(∫ x : ℝ in a..b, f ((x : ℂ) + (T : ℂ) * I)) -
        (∫ x : ℝ in a..b, f ((x : ℂ) - (T : ℂ) * I))‖ :=
      mul_le_mul_of_nonneg_right lemma44_mellin_normalization_norm_le_one (norm_nonneg _)
    _ ≤ 2 * K * |b - a| := by
      have ht := norm_sub_le
        (∫ x : ℝ in a..b, f ((x : ℂ) + (T : ℂ) * I))
        (∫ x : ℝ in a..b, f ((x : ℂ) - (T : ℂ) * I))
      simp only [one_mul]
      nlinarith only [ht, htop, hbottom]

theorem lemma44_product_horizontal_error_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hs : Lemma44InOmega3 D s) :
    ‖lemma44ProductHorizontalError χ ψ s (lemma44PaperGaussianScale D)
      (-s.re - 1 / 2) (lemma23PaperL D ^ 20)‖ ≤
      2097152 * Real.exp 1 * lemma23PaperL D ^ (-180 : ℤ) := by
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have hre := lemma44_omega3_re_pos hL hs
  have ha := lemma44_alpha_pos_le_one hL
  have hpoint (x : ℝ) (hx : x ∈ uIcc (-s.re - 1 / 2) 1)
      (v : ℝ) (hv : |v| = lemma23PaperL D ^ 20) :
      ‖lemma44ProductMellinNumerator χ ψ s (lemma44PaperGaussianScale D)
        ((x : ℂ) + (v : ℂ) * I) / ((x : ℂ) + (v : ℂ) * I)‖ ≤
      262144 * Real.exp 1 * lemma23PaperL D ^ (-180 : ℤ) := by
    rw [uIcc_of_le (by linarith : -s.re - 1 / 2 ≤ 1)] at hx
    apply lemma44_product_horizontal_point_bound χ ψ hD hψ hs hx.1 _ hv
    apply abs_le.mpr
    constructor <;> linarith only [hx.1, hx.2, hs.2.1, ha.2]
  have hT : 0 ≤ lemma23PaperL D ^ 20 := by positivity
  have he := lemma44_horizontal_error_bound
    (fun w => lemma44ProductMellinNumerator χ ψ s (lemma44PaperGaussianScale D) w / w)
    (a := -s.re - 1 / 2) (b := 1) (T := lemma23PaperL D ^ 20)
    (K := 262144 * Real.exp 1 * lemma23PaperL D ^ (-180 : ℤ)) (by positivity)
    (fun x hx => hpoint x hx _ (abs_of_nonneg hT))
    (by
      intro x hx
      simpa only [ofReal_neg, neg_mul, sub_eq_add_neg] using
        hpoint x hx (-(lemma23PaperL D ^ 20)) (by rw [abs_neg, abs_of_nonneg hT]))
  change ‖lemma44ProductHorizontalError χ ψ s (lemma44PaperGaussianScale D)
    (-s.re - 1 / 2) (lemma23PaperL D ^ 20)‖ ≤ _ at he
  apply he.trans
  have hwidth : |1 - (-s.re - 1 / 2)| ≤ 4 := by
    rw [abs_of_pos (by linarith : 0 < 1 - (-s.re - 1 / 2))]
    linarith only [hs.2.1, ha.2]
  calc
    _ ≤ 2 * (262144 * Real.exp 1 * lemma23PaperL D ^ (-180 : ℤ)) * 4 :=
      mul_le_mul_of_nonneg_left hwidth (by positivity)
    _ = _ := by ring

end ZhangLS.Spec
