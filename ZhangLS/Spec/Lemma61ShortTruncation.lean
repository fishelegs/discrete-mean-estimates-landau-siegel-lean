import ZhangLS.Spec.Lemma61ShortCutoff

/-! # Faithful original Lemma 6.1

Finite short-polynomial Gaussian inversion, actual original-left integral
decomposition and N approximation, actual full horizontal L edges and
uniform constants/thresholds yield lemma61_proved : Lemma61Target.
Original Psi, strict region and actual L/K/N/E1 are retained.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Real Topology
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

lemma lemma61_short_right_gaussian_bound {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hL : 3 ≤ lemma23PaperL D)
    {s : ℂ} (hs : 0 ≤ s.re) (v : ℝ) :
    ‖lemma61ShortRightMellinIntegrand D ψ s (lemma56PaperT D ^ 2) 1 v * I‖ ≤
      (2 * Real.exp (1 + 5 * lemma23PaperL D ^ 9)) *
        Real.exp (-(1 / (4 * lemma23PaperL D ^ 30)) * v ^ 2) := by
  let w : ℂ := 1 + (v : ℂ) * I
  have hTpos : 0 < lemma56PaperT D := Real.exp_pos _
  have hz : 0 ≤ (s + w).re := by simp [w]; linarith only [hs]
  have hp := lemma61_short_polynomial_norm_bound ψ hL hz
  have hn : 1 ≤ ‖w‖ := by simpa [w] using Complex.abs_re_le_norm w
  have hinv : ‖w‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hn
  have hscale : ‖exp (w * (Real.log (lemma56PaperT D ^ 2) : ℂ))‖ =
      Real.exp (2 * Real.log (lemma56PaperT D)) := by
    rw [norm_exp,mul_re,Real.log_pow]
    simp [w]
  have homega : ‖lemma57OmegaOne D w‖ ≤
      Real.exp 1 * Real.exp (-(1 / (4 * lemma23PaperL D ^ 30)) * v ^ 2) := by
    change ‖lemma57OmegaOne D (((1 : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤ _
    rw [lemma44_Omega_norm_vertical,← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h0 : 0 < lemma23PaperL D := by linarith
    have hp30 : 1 ≤ lemma23PaperL D ^ 30 := one_le_pow₀ (by linarith : 1 ≤ lemma23PaperL D)
    field_simp
    nlinarith only [hp30]
  have ht3 : lemma56PaperT D ^ 3 = Real.exp (3 * Real.log (lemma56PaperT D)) := by
    simpa only [Real.log_pow,Nat.cast_ofNat] using
      (Real.exp_log (pow_pos (show 0 < lemma56PaperT D from Real.exp_pos _) 3)).symm
  unfold lemma61ShortRightMellinIntegrand
  change ‖lemma61ShortPolynomial D ψ (s + w) *
    exp (w * (Real.log (lemma56PaperT D ^ 2) : ℂ)) * lemma57OmegaOne D w / w * I‖ ≤ _
  simp only [norm_mul,norm_inv,norm_I,mul_one,div_eq_mul_inv,hscale]
  calc
    _ ≤ (2 * lemma56PaperT D ^ 3) * Real.exp (2 * Real.log (lemma56PaperT D)) *
        (Real.exp 1 * Real.exp (-(1 / (4 * lemma23PaperL D ^ 30)) * v ^ 2)) * 1 :=
      mul_le_mul (mul_le_mul (mul_le_mul hp le_rfl (by positivity) (by positivity))
        homega (norm_nonneg _) (by positivity)) hinv
        (inv_nonneg.mpr (norm_nonneg _)) (by positivity)
    _ = 2 * Real.exp (1 + 5 * Real.log (lemma56PaperT D)) *
        Real.exp (-(1 / (4 * lemma23PaperL D ^ 30)) * v ^ 2) := by
      rw [ht3,show 1 + 5 * Real.log (lemma56PaperT D) =
        3 * Real.log (lemma56PaperT D) + 2 * Real.log (lemma56PaperT D) + 1 by ring]
      simp only [Real.exp_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (by linarith only [(lemma61_T_log_bounds hL).2])) (by norm_num)) (by positivity)

lemma lemma61_short_gaussian_exponent_absorption {L : ℝ} (hL : 64 ≤ L) :
    L ^ 10 * Real.exp (1 + 5 * L ^ 9 - L ^ 10 / 4) ≤
      Real.exp (-(L ^ 10) / 8) := by
  have h0 : 0 < L := by linarith
  have h1 : 1 ≤ L := by linarith
  have hlog : Real.log (L ^ 10) ≤ 10 * L := by
    rw [Real.log_pow]
    have h := Real.log_le_sub_one_of_pos h0
    norm_num
    linarith
  have hpoly : L ^ 3 ≤ L ^ 10 := pow_le_pow_right₀ h1 (by norm_num)
  have h2 : 64 * L ≤ L ^ 2 := by
    nlinarith only [mul_le_mul_of_nonneg_right hL h0.le]
  have h3 : 4096 * L ≤ L ^ 3 := by
    nlinarith only [h2,mul_le_mul_of_nonneg_right h2 h0.le]
  have h9 : 64 * L ^ 9 ≤ L ^ 10 := by
    have h := mul_le_mul_of_nonneg_right hL (pow_nonneg h0.le 9)
    convert h using 1 <;> ring
  have hex : 10 * L + 1 + 5 * L ^ 9 ≤ L ^ 10 / 8 := by
    linarith only [hpoly,h3,h9,hL]
  calc
    _ ≤ Real.exp (10 * L) * Real.exp (1 + 5 * L ^ 9 - L ^ 10 / 4) :=
      mul_le_mul_of_nonneg_right (Real.le_exp_of_log_le hlog) (Real.exp_nonneg _)
    _ = Real.exp (10 * L + (1 + 5 * L ^ 9 - L ^ 10 / 4)) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [hex])

lemma lemma61_actual_short_right_truncation {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hD : 1 < D)
    (hL : 64 ≤ lemma23PaperL D) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖(∫ v : ℝ, lemma61ShortRightMellinIntegrand D ψ s (lemma56PaperT D ^ 2) 1 v * I) -
      (∫ v : ℝ in -(lemma23PaperL D ^ 20)..(lemma23PaperL D ^ 20),
        lemma61ShortRightMellinIntegrand D ψ s (lemma56PaperT D ^ 2) 1 v * I)‖ ≤
      16 * Real.exp (-(lemma23PaperL D ^ 10) / 8) := by
  have h0 : 0 < lemma23PaperL D := by linarith
  have hi := (lemma61_short_mellin_integrable ψ s (lemma56PaperT D ^ 2) hD
    (by norm_num : (1 : ℝ) ≠ 0)).mul_const I
  have ht := lemma44_gaussian_integral_truncation
    (fun v => lemma61ShortRightMellinIntegrand D ψ s (lemma56PaperT D ^ 2) 1 v * I) hi
    (C := 2 * Real.exp (1 + 5 * lemma23PaperL D ^ 9))
    (b := 1 / (4 * lemma23PaperL D ^ 30)) (T := lemma23PaperL D ^ 20)
    (by positivity) (by positivity) (by positivity)
    (lemma61_short_right_gaussian_bound ψ (by linarith) hs)
  have hbt : (1 / (4 * lemma23PaperL D ^ 30)) * lemma23PaperL D ^ 20 =
      1 / (4 * lemma23PaperL D ^ 10) := by field_simp
  have hbe : (1 / (4 * lemma23PaperL D ^ 30)) * (lemma23PaperL D ^ 20) ^ 2 =
      lemma23PaperL D ^ 10 / 4 := by field_simp
  apply ht.trans
  calc
    _ = 16 * (lemma23PaperL D ^ 10 * Real.exp
        (1 + 5 * lemma23PaperL D ^ 9 - lemma23PaperL D ^ 10 / 4)) := by
      rw [hbt,show -(1 / (4 * lemma23PaperL D ^ 30)) *
        (lemma23PaperL D ^ 20) ^ 2 = -(lemma23PaperL D ^ 10 / 4) by linarith only [hbe]]
      rw [show 1 + 5 * lemma23PaperL D ^ 9 - lemma23PaperL D ^ 10 / 4 =
        (1 + 5 * lemma23PaperL D ^ 9) + -(lemma23PaperL D ^ 10 / 4) by ring]
      simp only [Real.exp_add]
      field_simp <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (lemma61_short_gaussian_exponent_absorption hL)
      (by norm_num)

lemma lemma61_actual_finite_short_mellin_N_bound {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (s : ℂ) (hD : 1 < D)
    (hL : 64 ≤ lemma23PaperL D) (hs : s.re ≤ 1) :
    ‖(2 * (Real.pi : ℂ) * I)⁻¹ *
      (∫ t : ℝ in -(lemma23PaperL D ^ 20)..(lemma23PaperL D ^ 20),
        lemma61ShortRightMellinIntegrand D ψ (1 - s)
          (lemma56PaperT D ^ 2) 1 t * I) - lemma61ActualN D ψ (1 - s)‖ ≤
      (16 + lemma44InverseSquareMass) * Real.exp (-(lemma23PaperL D ^ 10) / 8) := by
  let F := (2 * (Real.pi : ℂ) * I)⁻¹ *
    (∫ t : ℝ in -(lemma23PaperL D ^ 20)..(lemma23PaperL D ^ 20),
      lemma61ShortRightMellinIntegrand D ψ (1 - s) (lemma56PaperT D ^ 2) 1 t * I)
  let J := (2 * (Real.pi : ℂ) * I)⁻¹ *
    (∫ t : ℝ, lemma61ShortRightMellinIntegrand D ψ (1 - s) (lemma56PaperT D ^ 2) 1 t * I)
  have ht := lemma61_actual_short_right_truncation ψ hD hL
    (s := 1 - s) (by simpa using sub_nonneg.mpr hs)
  have hn : ‖F - J‖ ≤ 16 * Real.exp (-(lemma23PaperL D ^ 10) / 8) := by
    dsimp [F,J]
    rw [← mul_sub,norm_mul]
    exact (mul_le_mul_of_nonneg_right lemma61_mellin_normalization_norm_le_one (norm_nonneg _)).trans
      (by simpa only [one_mul,norm_sub_rev] using ht)
  have hc := lemma61_actual_full_short_mellin_N_bound ψ s hD (by linarith) hs
  have he : Real.exp (-(lemma23PaperL D ^ 10)) ≤ Real.exp (-(lemma23PaperL D ^ 10) / 8) := by
    apply Real.exp_le_exp.mpr
    have h0 : 0 ≤ lemma23PaperL D ^ 10 := pow_nonneg (by linarith) _
    linarith
  have hc' := hc.trans (mul_le_mul_of_nonneg_left he
    (show 0 ≤ lemma44InverseSquareMass from tsum_nonneg (fun _ => by positivity)))
  have ht' := norm_sub_le_norm_sub_add_norm_sub F J (lemma61ActualN D ψ (1 - s))
  change ‖F - lemma61ActualN D ψ (1 - s)‖ ≤ _
  change ‖J - lemma61ActualN D ψ (1 - s)‖ ≤ _ at hc'
  nlinarith only [ht',hn,hc']

end ZhangLS.Spec
