import ZhangLS.Spec.FourthResidue
import ZhangLS.Spec.GaussianVerticalNumerator
import ZhangLS.Spec.Lemma171ContourInfinite

/-! Genuine contour estimates for the extra Perron division. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex MeasureTheory Set Filter
open scoped Topology

noncomputable def lemma171LogVerticalIntegral {D : ℕ} (χ : RealPrimitiveCharacter D)
    (σ : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ) * I)⁻¹ *
    ∫ t : ℝ, lemma171LogMellinIntegrand χ ((σ : ℂ) + (t : ℂ) * I) * I

lemma lemma171_log_vertical_integrable {D : ℕ} (χ : RealPrimitiveCharacter D)
    {σ : ℝ} (hσ : σ ≠ 0)
    (hi : Integrable (fun t : ℝ => lemma171MellinIntegrand χ ((σ : ℂ) + (t : ℂ) * I))) :
    Integrable (fun t : ℝ => lemma171LogMellinIntegrand χ ((σ : ℂ) + (t : ℂ) * I)) :=
  lemma171_integrable_div_vertical hσ hi

lemma lemma171_log_right_vertical_integrable {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) :
    Integrable (fun t : ℝ => lemma171LogMellinIntegrand χ ((1 : ℂ) + (t : ℂ) * I)) :=
  lemma171_log_vertical_integrable χ one_ne_zero (lemma171_right_vertical_integrable χ hD)

lemma lemma171_log_left_vertical_integrable {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) :
    Integrable (fun t : ℝ => lemma171LogMellinIntegrand χ (((-1/4 : ℝ) : ℂ) + (t : ℂ) * I)) :=
  lemma171_log_vertical_integrable χ (by norm_num) (lemma171_left_vertical_integrable χ hD)

lemma lemma171_log_mellin_horizontal_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (σ t : ℝ) (hlo : -1/4 ≤ σ) (hhi : σ ≤ 1)
    (ht : 1 ≤ |t|) :
    ‖lemma171LogMellinIntegrand χ ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      lemma171HorizontalConstant D * Real.exp (-t ^ 2 / (8 * lemma23PaperL D ^ 30)) := by
  have hn : 1 ≤ ‖(σ : ℂ) + (t : ℂ) * I‖ := by
    have hh := Complex.abs_im_le_norm ((σ : ℂ) + (t : ℂ) * I)
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, zero_add, add_zero] at hh
    exact ht.trans hh
  rw [lemma171LogMellinIntegrand, norm_div]
  exact (div_le_self (norm_nonneg _) hn).trans
    (lemma171_mellin_horizontal_bound χ hD σ t hlo hhi ht)

lemma lemma171_log_left_integrand_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (t : ℝ) :
    ‖lemma171LogMellinIntegrand χ (((-1/4 : ℝ) : ℂ) + (t : ℂ) * I) * I‖ ≤
      4 * lemma171LeftEnvelope D t := by
  let w : ℂ := ((-1/4 : ℝ) : ℂ) + (t : ℂ) * I
  have hn : 1/4 ≤ ‖w‖ := by
    have hh := Complex.abs_re_le_norm w
    norm_num [w] at hh ⊢
    exact hh
  have hn0 : 0 < ‖w‖ := lt_of_lt_of_le (by norm_num) hn
  have hb := lemma171_left_integrand_bound χ hD t
  simp only [norm_mul, norm_I, mul_one] at hb
  rw [lemma171LogMellinIntegrand, norm_mul, norm_I, mul_one, norm_div]
  change ‖lemma171MellinIntegrand χ w‖ / ‖w‖ ≤ _
  calc
    _ ≤ 4 * ‖lemma171MellinIntegrand χ w‖ := by
      apply (div_le_iff₀ hn0).mpr
      nlinarith [norm_nonneg (lemma171MellinIntegrand χ w)]
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (by norm_num)

lemma lemma171_log_left_vertical_norm_le_majorant {D : ℕ}
    (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    ‖lemma171LogVerticalIntegral χ (-1/4)‖ ≤ 4 * lemma171LeftMajorant D := by
  have hn : ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ = (2 * Real.pi)⁻¹ := by
    simp [norm_inv, Real.pi_pos.le]
  have hb : ‖∫ t : ℝ,
      lemma171LogMellinIntegrand χ (((-1/4 : ℝ) : ℂ) + (t : ℂ) * I) * I‖ ≤
      ∫ t : ℝ, 4 * lemma171LeftEnvelope D t :=
    norm_integral_le_of_norm_le ((lemma171_left_envelope_integrable hD).const_mul 4)
      (Eventually.of_forall (lemma171_log_left_integrand_bound χ hD))
  unfold lemma171LogVerticalIntegral
  rw [norm_mul, hn]
  calc
    _ ≤ (2 * Real.pi)⁻¹ * ∫ t : ℝ, 4 * lemma171LeftEnvelope D t :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by
      unfold lemma171LeftEnvelope lemma171LeftMajorant lemma171StripConstant
      rw [integral_const_mul, integral_const_mul, integral_gaussian]
      have he : Real.pi / (1 / (8 * lemma23PaperL D ^ 30)) =
          8 * Real.pi * lemma23PaperL D ^ 30 := by
        simp only [div_eq_mul_inv, one_mul, inv_inv]
        ring
      rw [he]
      ring

end ZhangLS.Spec
