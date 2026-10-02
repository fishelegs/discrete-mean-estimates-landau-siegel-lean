import ZhangLS.Spec.Lemma81ZetaPerronBounds
import ZhangLS.Spec.Lemma56PrincipalPerronBoundaryBounds

/-! # Actual principal Perron error from the unconditional thin strip -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set Metric
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

lemma lemma81_principal_perron_smoothed_main_error_of_strip {D : ℕ}
    (hD : 4 ≤ D) (hL : 2000 ≤ Real.log (D : ℝ))
    (hfree : ∀ ρ : ℂ, 1 - 1 / (10000000 * Real.log (D : ℝ)) < ρ.re →
      |ρ.im| ≤ D → zetaPoleRemoved ρ ≠ 0)
    {B x : ℝ} (hB : 0 < B) (hx : 1 ≤ x) :
    let a := 1 - lemma81ZetaContourDelta D
    let M := lemma81ZetaContourBound D
    let H := (D : ℝ) / 2
    ‖lemma56PerronMangoldtSum (1 : DirichletCharacter ℂ 1) B x 0 -
      ((x * Real.exp (1 / (4 * B ^ 2)) : ℝ) : ℂ)‖ ≤
      6 * M * x ^ a * Real.exp (a ^ 2 / (4 * B ^ 2)) * Real.log (1 + H) +
        (4 * M + 4 * lemma56GaussianRightConstant * B ^ 2) *
          x ^ 2 * Real.exp (1 / B ^ 2 - H ^ 2 / (4 * B ^ 2)) / H := by
  have hx0 : 0 < x := by linarith only [hx]
  have hD4 : (4 : ℝ) ≤ D := by exact_mod_cast hD
  obtain ⟨hδ, hδsmall, hwidth⟩ := lemma81_zeta_contour_delta hL
  let a := 1 - lemma81ZetaContourDelta D
  let M := lemma81ZetaContourBound D
  let H := (D : ℝ) / 2
  have hHp : 0 < H := by dsimp [H]; linarith only [hD4]
  have haHalf : (1 / 2 : ℝ) ≤ a := by dsimp [a]; linarith only [hδsmall]
  have ha1 : a < 1 := by dsimp [a]; linarith only [hδ]
  have hL0 : 0 ≤ Real.log (D : ℝ) := by linarith only [hL]
  have hM : 0 ≤ M := by unfold M lemma81ZetaContourBound; positivity
  let c : ℝ := 1 / (2 * Real.pi)
  let P := lemma56PerronMangoldtSum (1 : DirichletCharacter ℂ 1) B x 0
  let m : ℂ := ((x * Real.exp (1 / (4 * B ^ 2)) : ℝ) : ℂ)
  let R := ∫ t : ℝ in -H..H, lemma56PrincipalPerronArithmeticIntegrand B x (((2 : ℝ) : ℂ) + (t : ℂ) * I)
  let S := ∫ t : ℝ in -H..H, lemma56PrincipalPerronArithmeticIntegrand B x ((a : ℂ) + (t : ℂ) * I)
  let U := ∫ σ : ℝ in a..2, lemma56PrincipalPerronArithmeticIntegrand B x ((σ : ℂ) + (H : ℂ) * I)
  let V := ∫ σ : ℝ in a..2, lemma56PrincipalPerronArithmeticIntegrand B x ((σ : ℂ) - (H : ℂ) * I)
  let Rt := 4 * lemma56GaussianRightConstant * x ^ 2 * (B ^ 2 / H) *
    Real.exp (1 / B ^ 2 - H ^ 2 / (4 * B ^ 2))
  have hs := lemma56_actual_principal_perron_rectangle_shift hx0
    (by linarith only [haHalf] : 0 < a) ha1 hHp B
    (fun z hz _hz2 ht => hfree z (by rw [hwidth]; dsimp [a] at hz; linarith only [hz, hδ])
      (by dsimp [H] at ht; linarith only [ht, hD4]))
  change I * R = I * S + U - V + 2 * (Real.pi : ℂ) * I * m at hs
  have hR : R = S - I * U + I * V + 2 * (Real.pi : ℂ) * m := by
    calc
      R = -(I * (I * R)) := by rw [← mul_assoc, I_mul_I]; ring
      _ = -(I * (I * S + U - V + 2 * (Real.pi : ℂ) * I * m)) := by rw [hs]
      _ = _ := by ring_nf; simp [Complex.I_sq]
  have hc : 0 < c := by dsimp [c]; positivity
  have hc1 : c ≤ 1 := by
    dsimp [c]
    apply (div_le_one (by positivity : 0 < 2 * Real.pi)).mpr
    linarith only [Real.one_le_pi_div_two]
  have hnc : ‖(c : ℂ)‖ = c := by rw [norm_real, Real.norm_eq_abs, abs_of_pos hc]
  have hcn : (c : ℂ) * 2 * (Real.pi : ℂ) = 1 := by
    dsimp [c]
    push_cast
    field_simp [ofReal_ne_zero.mpr Real.pi_ne_zero]
  have hmid : (c : ℂ) * R - m = (c : ℂ) * S - (c : ℂ) * I * U + (c : ℂ) * I * V := by
    rw [hR]
    linear_combination m * hcn
  have hfinite : ‖(c : ℂ) * R - m‖ ≤ ‖S‖ + ‖U‖ + ‖V‖ := by
    rw [hmid]
    calc
      _ ≤ (‖(c : ℂ) * S‖ + ‖(c : ℂ) * I * U‖) + ‖(c : ℂ) * I * V‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) (le_refl _))
      _ = c * (‖S‖ + ‖U‖ + ‖V‖) := by simp only [norm_mul, norm_I, hnc, mul_one]; ring
      _ ≤ _ := by
        convert mul_le_mul_of_nonneg_right hc1
          (by positivity : 0 ≤ ‖S‖ + ‖U‖ + ‖V‖) using 1; ring
  have hS : ‖S‖ ≤ 6 * M * x ^ a * Real.exp (a ^ 2 / (4 * B ^ 2)) * Real.log (1 + H) := by
    simp_rw [S, lemma56_actual_principal_perron_arithmetic_eq]
    apply lemma56_perron_vertical_integral_bound (1 : DirichletCharacter ℂ 1)
      hB hx0 hHp.le hM haHalf 0
    intro t ht
    simpa only [DirichletCharacter.LFunction_modOne_eq, ofReal_zero, zero_mul, sub_zero, a, M, H] using
      lemma81_zeta_paper_left_bound hD hL hfree ht
  have hHorizontal (t : ℝ) (ht : |t| = H) :
      ‖∫ σ : ℝ in a..2, lemma56PrincipalPerronArithmeticIntegrand B x ((σ : ℂ) + (t : ℂ) * I)‖ ≤
        2 * M * x ^ 2 * Real.exp (1 / B ^ 2 - H ^ 2 / (4 * B ^ 2)) / H := by
    simp_rw [lemma56_actual_principal_perron_arithmetic_eq]
    apply lemma56_perron_horizontal_integral_bound (1 : DirichletCharacter ℂ 1)
      hB hx hHp hM (by linarith only [haHalf]) (by linarith only [ha1]) ht.ge 0
    intro σ hσ hσ2
    simpa only [DirichletCharacter.LFunction_modOne_eq, ofReal_zero, zero_mul, sub_zero, M] using
      lemma81_zeta_paper_horizontal_bound hD hL hfree hσ hσ2 ht
  have hU := hHorizontal H (abs_of_pos hHp)
  change ‖U‖ ≤ 2 * M * x ^ 2 * Real.exp (1 / B ^ 2 - H ^ 2 / (4 * B ^ 2)) / H at hU
  have hV := hHorizontal (-H) (by rw [abs_neg, abs_of_pos hHp])
  have hpoint (σ : ℝ) : (σ : ℂ) + ((-H : ℝ) : ℂ) * I = (σ : ℂ) - (H : ℂ) * I := by push_cast; ring
  simp_rw [hpoint] at hV
  change ‖V‖ ≤ 2 * M * x ^ 2 * Real.exp (1 / B ^ 2 - H ^ 2 / (4 * B ^ 2)) / H at hV
  have htwo : ((2 : ℝ) : ℂ) = (2 : ℂ) := by norm_num
  have htr : ‖P - (c : ℂ) * R‖ ≤ c * Rt := by
    simpa only [P, c, R, Rt, htwo, lemma56PrincipalPerronArithmeticIntegrand,
      lemma56PerronComplexKernel, lemma56PerronArithmeticIntegrand,
      DirichletCharacter.LFunction_modOne_eq, ofReal_zero, zero_mul, sub_zero] using
      lemma56_actual_perron_mangoldt_truncation (1 : DirichletCharacter ℂ 1) hB hx0 hHp 0
  have hCr := lemma56_gaussian_right_constant_nonneg
  have hRt : 0 ≤ Rt := by dsimp [Rt]; positivity
  have htail : ‖P - (c : ℂ) * R‖ ≤ Rt := htr.trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hc1 hRt)
  have htri := norm_add_le (P - (c : ℂ) * R) ((c : ℂ) * R - m)
  rw [sub_add_sub_cancel] at htri
  have hb : ‖P - m‖ ≤ Rt +
      6 * M * x ^ a * Real.exp (a ^ 2 / (4 * B ^ 2)) * Real.log (1 + H) +
        2 * (2 * M * x ^ 2 * Real.exp (1 / B ^ 2 - H ^ 2 / (4 * B ^ 2)) / H) := by
    linarith only [htri, htail, hfinite, hS, hU, hV]
  change ‖P - m‖ ≤ 6 * M * x ^ a * Real.exp (a ^ 2 / (4 * B ^ 2)) * Real.log (1 + H) +
    (4 * M + 4 * lemma56GaussianRightConstant * B ^ 2) *
      x ^ 2 * Real.exp (1 / B ^ 2 - H ^ 2 / (4 * B ^ 2)) / H
  convert hb using 1; dsimp [Rt]; ring

end ZhangLS.Spec
