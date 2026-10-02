import ZhangLS.Spec.Lemma171ContourFinite
import ZhangLS.Spec.Lemma171CorrectionBounds
import ZhangLS.Spec.Lemma32StripLSeriesGrowth
import ZhangLS.Spec.Lemma57GaussianQuadraticMoment

/-! # Lemma 17.1: proven strip growth and Gaussian damping -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex MeasureTheory Set Filter
open scoped Classical Topology

noncomputable def lemma171UndampedFactor {D : ℕ}
    (χ : RealPrimitiveCharacter D) (w : ℂ) : ℂ :=
  lemma171AnalyticCorrection D (1+w)*
    (riemannZeta (1+w)*dirichletLFunction χ (1+w))^2/w

noncomputable def lemma171StripConstant (D : ℕ) : ℝ :=
  4*64^2*lemma32RegularProductBound (3/4)*(D : ℝ)^4

lemma lemma171_strip_constant_pos {D : ℕ} (hD : 0 < D) :
    0 < lemma171StripConstant D := by
  unfold lemma171StripConstant
  have hk := lemma32_regular_product_bound_pos (3/4)
  have hp : (0 : ℝ) < D := by exact_mod_cast hD
  positivity

lemma lemma171_zeta_L_strip_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (w : ℂ) (hlo : -1/4 ≤ w.re) (hhi : w.re ≤ 1)
    (hn : 1/4 ≤ ‖w‖) :
    ‖riemannZeta (1+w)*dirichletLFunction χ (1+w)‖ ≤
      64*(D : ℝ)*(1+w.im^2) := by
  let s : ℂ := 1+w
  have hs : 0 < s.re := by dsimp [s];linarith
  have hslo : 3/4 ≤ s.re := by dsimp [s];linarith
  have hshi : s.re ≤ 2 := by dsimp [s];linarith
  have hs1 : s ≠ 1 := by
    intro h
    have hw : w = 0 := by dsimp [s] at h;linear_combination h
    simp [hw] at hn
    linarith
  have hden : 0 < ‖s-1‖ := by simpa [s] using (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/4) hn)
  have hfirst : ‖s‖/‖s-1‖ ≤ 4*‖s‖ := by
    apply (div_le_iff₀ hden).mpr
    have hd : 1/4 ≤ ‖s-1‖ := by simpa [s] using hn
    nlinarith [norm_nonneg s]
  have hsecond : ‖s‖/s.re ≤ (4/3)*‖s‖ := by
    apply (div_le_iff₀ hs).mpr
    nlinarith [norm_nonneg s]
  have hz : ‖riemannZeta s‖ ≤ 6*‖s‖ := by
    rw [riemannZeta_eq_fractionalPart_formula_of_pos_re hs hs1]
    calc
      _ ≤ ‖s/(s-1)‖+‖s*mellin zetaFractionalPart (-s)‖ := norm_sub_le _ _
      _ ≤ ‖s‖/‖s-1‖+‖s‖*(1/s.re) := by
        rw [norm_div,norm_mul]
        gcongr
        exact norm_mellin_zetaFractionalPart_le hs
      _ = ‖s‖/‖s-1‖+‖s‖/s.re := by ring
      _ ≤ _ := by nlinarith [norm_nonneg s]
  have hl : ‖dirichletLFunction χ s‖ ≤ (4/3)*(D : ℝ)*‖s‖ := by
    calc
      _ ≤ ‖s‖*((D : ℝ)/s.re) := χ.norm_dirichletLFunction_le_of_pos_re hD hs
      _ = (D : ℝ)*(‖s‖/s.re) := by ring
      _ ≤ (D : ℝ)*((4/3)*‖s‖) := mul_le_mul_of_nonneg_left hsecond (Nat.cast_nonneg D)
      _ = _ := by ring
  have hsq : ‖s‖^2 ≤ 8*(1+w.im^2) := by
    have he : ‖s‖^2 = s.re^2+s.im^2 := by rw [Complex.sq_norm,Complex.normSq_apply];ring
    rw [he]
    have him : s.im = w.im := by simp [s]
    rw [him]
    nlinarith [sq_nonneg s.re,sq_nonneg w.im]
  change ‖riemannZeta s*dirichletLFunction χ s‖ ≤ _
  rw [norm_mul]
  calc
    _ ≤ (6*‖s‖)*((4/3)*(D : ℝ)*‖s‖) :=
      mul_le_mul hz hl (norm_nonneg _) (by positivity)
    _ = 8*(D : ℝ)*‖s‖^2 := by ring
    _ ≤ 8*(D : ℝ)*(8*(1+w.im^2)) := mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = _ := by ring

lemma lemma171_undamped_strip_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (w : ℂ) (hlo : -1/4 ≤ w.re) (hhi : w.re ≤ 1)
    (hn : 1/4 ≤ ‖w‖) :
    ‖lemma171UndampedFactor χ w‖ ≤ lemma171StripConstant D*(1+w.im^2)^2 := by
  have hc := lemma171_correction_global_bound D χ.modulus_pos (1+w)
    (by simp only [Complex.add_re,Complex.one_re];linarith)
  have hz := lemma171_zeta_L_strip_bound χ hD w hlo hhi hn
  have hk := lemma32_regular_product_bound_pos (3/4)
  have hnp : 0 < ‖w‖ := lt_of_lt_of_le (by norm_num) hn
  unfold lemma171UndampedFactor
  rw [norm_div,norm_mul,norm_pow]
  calc
    _ ≤ (lemma32RegularProductBound (3/4)*(D : ℝ)^2)*
        (64*(D : ℝ)*(1+w.im^2))^2/‖w‖ := by
      gcongr
    _ ≤ 4*((lemma32RegularProductBound (3/4)*(D : ℝ)^2)*
        (64*(D : ℝ)*(1+w.im^2))^2) := by
      apply (div_le_iff₀ hnp).mpr
      have hb : 0 ≤ (lemma32RegularProductBound (3/4)*(D : ℝ)^2)*
          (64*(D : ℝ)*(1+w.im^2))^2 := by positivity
      nlinarith
    _ = _ := by unfold lemma171StripConstant;ring

lemma lemma171_gaussian_norm_vertical (D : ℕ) (σ t : ℝ) :
    ‖lemma171GaussianMellinFactor D ((σ : ℂ)+(t : ℂ)*I)‖ =
      Real.exp (lemma23PaperL D^(11/10:ℝ)*σ+
        (σ^2-t^2)/(4*lemma23PaperL D^30)) := by
  rw [lemma171GaussianMellinFactor,norm_exp]
  congr 1
  have hcast : (4*(Real.log (D:ℝ):ℂ)^30) = ((4*Real.log (D:ℝ)^30:ℝ):ℂ) := by push_cast;ring
  rw [hcast]
  simp only [Complex.add_re,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,
    zero_add,add_zero,mul_one]
  rw [Complex.div_ofReal_re]
  simp only [pow_two,Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,
    zero_mul,sub_zero,zero_add,add_zero,mul_one]
  rfl

lemma lemma171_mellin_eq_undamped (D : ℕ) (χ : RealPrimitiveCharacter D) (w : ℂ) :
    lemma171MellinIntegrand χ w = lemma171UndampedFactor χ w*
      lemma171GaussianMellinFactor D w := by
  unfold lemma171MellinIntegrand lemma171UndampedFactor
  ring

lemma lemma171_quartic_gaussian_bound {b : ℝ} (hb : 0 < b) (t : ℝ) :
    (1+t^2)^2*Real.exp (-(4*b)*t^2) ≤
      (1+b⁻¹)^2*Real.exp (-(2*b)*t^2) := by
  have h := one_add_sq_mul_gaussian_le hb t
  have hn : 0 ≤ (1+t^2)*Real.exp (-(2*b)*t^2) := by positivity
  have hp := pow_le_pow_left₀ hn h 2
  simp only [mul_pow,← Real.exp_nat_mul] at hp
  convert hp using 1 <;> congr 2 <;> push_cast <;> ring

end ZhangLS.Spec
