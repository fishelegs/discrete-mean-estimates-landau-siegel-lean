import ZhangLS.Spec.Lemma44ModulusControl

/-!
# Cancellation on the middle contour in Lemma 4.4

Reality of the genuine `ν` coefficients converts the inverse-character
sum at negative height into a conjugate sum at positive height. The
good-set estimate then cancels the conductor growth of the actual factor
on `Re w = -α`, throughout the paper's truncated vertical line.
-/

namespace ZhangLS.Spec

open Complex ComplexConjugate

set_option maxHeartbeats 1000000

theorem lemma44_Nu_conj {D : ℕ} (χ : RealPrimitiveCharacter D) (n : ℕ) :
    conj (lemma23NuArithmeticFunction χ n) = lemma23NuArithmeticFunction χ n := by
  rw [lemma23NuArithmeticFunction_apply, map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  exact χ.conj_eval _

/-- No inverse-character good-set assumption is required: the parameter
is reflected and the genuine real coefficients are conjugated. -/
theorem lemma44_long_sum_inv_eq_conj {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N) (s : ℂ) :
    lemma44LongDirichletSum χ ψ⁻¹ s = conj (lemma44LongDirichletSum χ ψ (conj s)) := by
  have hc (n : ℕ) : conj (ψ (n : ZMod N)) = ψ⁻¹ (n : ZMod N) :=
    MulChar.star_apply' ψ _
  simp only [lemma44LongDirichletSum, map_sum, map_mul, lemma44_Nu_conj,
    hc, ← Complex.exp_conj, map_neg, Complex.conj_ofReal, conj_conj]

noncomputable def lemma44MiddleReflectedArgument (D : ℕ) (s : ℂ) (v : ℝ) : ℂ :=
  1 + (lemma44PaperAlpha D : ℂ) - conj s + (v : ℂ) * Complex.I

theorem lemma44_middle_reflected_displacement {D : ℕ} {s : ℂ} {v : ℝ}
    (hL : 3 ≤ lemma23PaperL D) (hs : Lemma44InOmega3 D s)
    (hv : |v| ≤ lemma23PaperL D ^ 20) :
    ‖lemma23PaperCenter D - lemma44MiddleReflectedArgument D s v‖ ≤
      4 * lemma23PaperL D ^ 405 := by
  have ha := lemma44_alpha_pos_le_one hL
  have hre : |(lemma23PaperCenter D - lemma44MiddleReflectedArgument D s v).re| ≤ 2 := by
    have heq : (lemma23PaperCenter D - lemma44MiddleReflectedArgument D s v).re =
        1 / 2 - (1 + lemma44PaperAlpha D - s.re) := by
      simp [lemma44MiddleReflectedArgument, lemma23PaperCenter]
    rw [heq]
    apply abs_le.mpr
    constructor <;> linarith [hs.1, hs.2.1]
  have hp : lemma23PaperL D ^ 20 ≤ lemma23PaperL D ^ 405 :=
    pow_le_pow_right₀ (by linarith : 1 ≤ lemma23PaperL D) (by norm_num)
  have him : |(lemma23PaperCenter D - lemma44MiddleReflectedArgument D s v).im| ≤
      2 * lemma23PaperL D ^ 405 + 3 := by
    have htri := abs_add_le ((lemma23PaperCenter D).im - s.im) (-v)
    simp only [abs_neg, abs_sub_comm] at htri
    have heq : (lemma23PaperCenter D - lemma44MiddleReflectedArgument D s v).im =
        (lemma23PaperCenter D).im - s.im - v := by
      simp [lemma44MiddleReflectedArgument]
      ring
    rw [heq]
    have htri' : |(lemma23PaperCenter D).im - s.im - v| ≤
        |s.im - (lemma23PaperCenter D).im| + |v| := by
      simpa only [sub_eq_add_neg] using htri
    exact htri'.trans (by linarith [hs.2.2])
  have hpow : 3 ≤ lemma23PaperL D ^ 405 :=
    hL.trans (le_self_pow₀ (by linarith : 1 ≤ lemma23PaperL D) (by norm_num))
  exact (Complex.norm_le_abs_re_add_abs_im _).trans (by linarith)

/-- The reflected long sum grows only by the real-part loss displayed here. -/
theorem lemma44_reflected_long_sum_bound {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hL : 3 ≤ lemma23PaperL D) (hψ : Lemma23InPsi1 χ ψ)
    {s : ℂ} (hs : Lemma44InOmega3 D s) {v : ℝ} (hv : |v| ≤ lemma23PaperL D ^ 20) :
    ‖lemma44LongDirichletSum χ ψ⁻¹
      (1 - s - (-(lemma44PaperAlpha D : ℂ) + (v : ℂ) * Complex.I))‖ ≤
        5 * Real.exp (2 * lemma23PaperL D ^ 9 *
          max 0 (s.re - 1 / 2 - lemma44PaperAlpha D)) * lemma23PaperL D ^ (-180 : ℤ) := by
  have harg : conj (1 - s - (-(lemma44PaperAlpha D : ℂ) + (v : ℂ) * Complex.I)) =
      lemma44MiddleReflectedArgument D s v := by
    apply Complex.ext <;> simp [lemma44MiddleReflectedArgument] <;> ring
  rw [lemma44_long_sum_inv_eq_conj, Complex.norm_conj, harg]
  have hdisp := lemma44_middle_reflected_displacement hL hs hv
  have hLpos : 0 < lemma23PaperL D := by linarith
  have hpow : 1 ≤ lemma23PaperL D ^ 405 := one_le_pow₀ (by linarith : 1 ≤ lemma23PaperL D)
  have hprod : lemma23PaperL D ^ 405 * lemma23PaperL D ^ (-585 : ℤ) =
      lemma23PaperL D ^ (-180 : ℤ) := by
    rw [← zpow_natCast, ← zpow_add₀ hLpos.ne']
    norm_num
  have hcoef : (1 + ‖lemma23PaperCenter D - lemma44MiddleReflectedArgument D s v‖) *
      lemma23PaperL D ^ (-585 : ℤ) ≤ 5 * lemma23PaperL D ^ (-180 : ℤ) := by
    calc
      _ ≤ (5 * lemma23PaperL D ^ 405) * lemma23PaperL D ^ (-585 : ℤ) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by rw [mul_assoc, hprod]
  have hb := lemma44_long_sum_bound χ ψ (lemma44MiddleReflectedArgument D s v) hL hψ.2
  have hre : 1 / 2 - (lemma44MiddleReflectedArgument D s v).re =
      s.re - 1 / 2 - lemma44PaperAlpha D := by
    simp [lemma44MiddleReflectedArgument]
    ring
  rw [hre] at hb
  have he := mul_le_mul_of_nonneg_left hcoef (Real.exp_nonneg
    (2 * lemma23PaperL D ^ 9 * max 0 (s.re - 1 / 2 - lemma44PaperAlpha D)))
  exact hb.trans (by nlinarith only [he])

/-- On `Re w=-α`, the actual factor's conductor growth has just the opposite
real-part exponent to the reflected long sum. -/
theorem lemma44_middle_Z_norm_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D)
    (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hs : Lemma44InOmega3 D s) {v : ℝ} (hv : |v| ≤ lemma23PaperL D ^ 20) :
    ‖lemma44ActualZtilde χ ψ
      (s + (-(lemma44PaperAlpha D : ℂ) + (v : ℂ) * Complex.I))‖ ≤
        Real.exp (2 + 2 * lemma23PaperL D ^ 9 *
          (1 / 2 - s.re + lemma44PaperAlpha D)) := by
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have ha := lemma44_alpha_pos_le_one hL
  let z := s + (-(lemma44PaperAlpha D : ℂ) + (v : ℂ) * Complex.I)
  have hz : Lemma44InExtendedGammaRegion D z :=
    lemma44_truncated_shift_in_extended_gamma_region hL hs
      (by simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re,
        Complex.mul_re, Complex.ofReal_im, Complex.I_re, mul_zero, zero_mul,
        sub_zero, add_zero, abs_neg]
          rw [abs_of_pos ha.1]; linarith [ha.2]) (by simpa using hv)
  have hre : z.re = s.re - lemma44PaperAlpha D := by simp [z]; ring
  have hlogP : Real.log (lemma23PaperP D) = lemma23PaperL D ^ 9 := by
    simp [lemma23PaperP]
  by_cases hr : 1 / 2 ≤ z.re
  · have hb := lemma44ActualZtilde_norm_le_right χ ψ hD hψ hz hr
    apply hb.trans
    rw [hre, hlogP]
    apply Real.exp_le_exp.mpr
    ring_nf
    linarith
  · have hb := lemma44ActualZtilde_norm_le_left χ ψ hD hψ hz (le_of_not_ge hr)
    have hsmall : 3 * lemma23PaperL D * (1 / 2 - z.re) ≤ 2 := by
      have hm := mul_le_mul_of_nonneg_left (show 1 / 2 - z.re ≤ 2 * lemma44PaperAlpha D by
        rw [hre]; linarith [hs.1]) (by linarith : 0 ≤ 3 * lemma23PaperL D)
      nlinarith only [hm, lemma44_alpha_horizontal_loss hL]
    apply hb.trans
    rw [hre, hlogP] at *
    apply Real.exp_le_exp.mpr
    nlinarith only [hsmall]

/-- The exponential conductor factors cancel before integration. This is
the key uniform pointwise estimate for the middle-contour piece (4.8). -/
theorem lemma44_middle_product_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    {s : ℂ} (hs : Lemma44InOmega3 D s) {v : ℝ} (hv : |v| ≤ lemma23PaperL D ^ 20) :
    ‖lemma44ActualZtilde χ ψ
        (s + (-(lemma44PaperAlpha D : ℂ) + (v : ℂ) * Complex.I)) *
      lemma44LongDirichletSum χ ψ⁻¹
        (1 - s - (-(lemma44PaperAlpha D : ℂ) + (v : ℂ) * Complex.I))‖ ≤
      5 * Real.exp (2 + 4 * Real.pi) * lemma23PaperL D ^ (-180 : ℤ) := by
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have ha := lemma44_alpha_pos_le_one hL
  have hLpos : 0 < lemma23PaperL D := by linarith
  have hz := lemma44_middle_Z_norm_bound χ ψ hD hψ.1 hs hv
  have hf := lemma44_reflected_long_sum_bound χ ψ hL hψ hs hv
  rw [norm_mul]
  have hp := mul_le_mul hz hf (norm_nonneg _) (Real.exp_nonneg _)
  apply hp.trans
  have hmax : (1 / 2 - s.re + lemma44PaperAlpha D) +
      max 0 (s.re - 1 / 2 - lemma44PaperAlpha D) ≤ 2 * lemma44PaperAlpha D := by
    rcases le_total 0 (s.re - 1 / 2 - lemma44PaperAlpha D) with h | h
    · rw [max_eq_right h]
      linarith [ha.1]
    · rw [max_eq_left h]
      linarith [hs.1]
  have halpha : lemma23PaperL D ^ 9 * lemma44PaperAlpha D = Real.pi := by
    simp only [lemma44PaperAlpha, lemma23PaperP, Real.log_exp]
    field_simp
  have he : Real.exp (2 + 2 * lemma23PaperL D ^ 9 *
      (1 / 2 - s.re + lemma44PaperAlpha D)) *
      Real.exp (2 * lemma23PaperL D ^ 9 * max 0 (s.re - 1 / 2 - lemma44PaperAlpha D)) ≤
        Real.exp (2 + 4 * Real.pi) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_left hmax (by positivity : 0 ≤ lemma23PaperL D ^ 9)
    nlinarith only [hm, halpha]
  have hm := mul_le_mul_of_nonneg_right he (by positivity : 0 ≤ 5 * lemma23PaperL D ^ (-180 : ℤ))
  nlinarith only [hm]

end ZhangLS.Spec
