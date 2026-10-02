import ZhangLS.Spec.Lemma61GaussianCutoff
import ZhangLS.Spec.Lemma44GaussianVerticalTail

/-! # Actual finite single L contour inputs for Lemma 6.1

The original family and actual L, K, P4, Gaussian weights and strict region
are retained. The genuine residue is expanded into four oriented edges.
The actual finite right integral differs from K by at most
9 times inverse-square mass exp(-L^10/8), uniformly for L>=64.
The full Lemma61Target remains unproved: left dual integrals, reciprocal
tail truncation and horizontal edge budgets are still required.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Real Topology
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

lemma lemma61_single_series_norm_le_square_mass {p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) {z : ℂ} (hz : 2 ≤ z.re) :
    ‖DirichletCharacter.LFunction ψ z‖ ≤ lemma44InverseSquareMass := by
  have hs : 1 < z.re := by linarith
  rw [DirichletCharacter.LFunction_eq_LSeries ψ hs]
  let c : ℕ → ℂ := fun n => ψ (n : ZMod p)
  have hpoint (n : ℕ) : ‖LSeries.term c z n‖ ≤ ((n : ℝ) ^ 2)⁻¹ := by
    by_cases hn : n = 0
    · simp [hn]
    · have hnr : 1 ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      rw [LSeries.norm_term_eq,if_neg hn]
      apply (div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
        (Real.rpow_le_rpow_of_exponent_le hnr hz)).trans
      rw [Real.rpow_two]
      simpa using mul_le_mul_of_nonneg_right (ψ.norm_le_one _) (by positivity : 0 ≤ ((n : ℝ) ^ 2)⁻¹)
  have hsum := summable_norm_iff.mpr (DirichletCharacter.LSeriesSummable_of_one_lt_re ψ hs)
  exact (norm_tsum_le_tsum_norm hsum).trans
    (hsum.tsum_le_tsum hpoint lemma44_inverse_square_summable)

lemma lemma61_right_mellin_gaussian_bound {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hL : 3 ≤ lemma23PaperL D)
    {s : ℂ} (hs : 0 ≤ s.re) {B : ℝ} (hB : Real.log B ≤ 2 * lemma23PaperL D ^ 9)
    (v : ℝ) :
    ‖lemma61RightMellinIntegrand (D := D) ψ s B 2 v * I‖ ≤
      (lemma44InverseSquareMass * Real.exp (1 + 4 * lemma23PaperL D ^ 9)) *
        Real.exp (-(1 / (4 * lemma23PaperL D ^ 30)) * v ^ 2) := by
  let w : ℂ := 2 + (v : ℂ) * I
  have hz : 2 ≤ (s + w).re := by simp [w]; linarith only [hs]
  have hp := lemma61_single_series_norm_le_square_mass ψ hz
  have hmass : 0 ≤ lemma44InverseSquareMass := tsum_nonneg (fun _ => by positivity)
  have hn : 1 ≤ ‖w‖ := by
    have h := Complex.abs_re_le_norm w
    norm_num [w] at h
    linarith
  have hinv : ‖w‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hn
  have hscale : ‖exp (w * (Real.log B : ℂ))‖ ≤ Real.exp (4 * lemma23PaperL D ^ 9) := by
    rw [norm_exp,mul_re]
    simp only [ofReal_re,ofReal_im,mul_zero,sub_zero]
    apply Real.exp_le_exp.mpr
    norm_num [w]
    linarith only [hB]
  have homega : ‖lemma57OmegaOne D w‖ ≤
      Real.exp 1 * Real.exp (-(1 / (4 * lemma23PaperL D ^ 30)) * v ^ 2) := by
    change ‖lemma57OmegaOne D (((2 : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤ _
    rw [lemma44_Omega_norm_vertical, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hL0 : 0 < lemma23PaperL D := by linarith
    have hp30 : 1 ≤ lemma23PaperL D ^ 30 := one_le_pow₀ (by linarith : 1 ≤ lemma23PaperL D)
    field_simp
    nlinarith only [hp30]
  unfold lemma61RightMellinIntegrand
  change ‖DirichletCharacter.LFunction ψ (s + w) *
    exp (w * (Real.log B : ℂ)) * lemma57OmegaOne D w / w * I‖ ≤ _
  simp only [norm_mul,norm_inv,norm_I,mul_one,div_eq_mul_inv]
  calc
    _ ≤ lemma44InverseSquareMass * Real.exp (4 * lemma23PaperL D ^ 9) *
        (Real.exp 1 * Real.exp (-(1 / (4 * lemma23PaperL D ^ 30)) * v ^ 2)) * 1 :=
      mul_le_mul (mul_le_mul (mul_le_mul hp hscale (norm_nonneg _) hmass)
        homega (norm_nonneg _) (by positivity)) hinv
        (inv_nonneg.mpr (norm_nonneg _)) (by positivity)
    _ = _ := by rw [Real.exp_add]; ring

lemma lemma61_right_gaussian_exponent_absorption {L : ℝ} (hL : 64 ≤ L) :
    L ^ 10 * Real.exp (1 + 4 * L ^ 9 - L ^ 10 / 4) ≤
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
  have hex : 10 * L + 1 + 4 * L ^ 9 ≤ L ^ 10 / 8 := by
    linarith only [hpoly,h3,h9,hL]
  calc
    _ ≤ Real.exp (10 * L) * Real.exp (1 + 4 * L ^ 9 - L ^ 10 / 4) :=
      mul_le_mul_of_nonneg_right (Real.le_exp_of_log_le hlog) (Real.exp_nonneg _)
    _ = Real.exp (10 * L + (1 + 4 * L ^ 9 - L ^ 10 / 4)) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [hex])

lemma lemma61_actual_right_mellin_truncation {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hD : 1 < D)
    (hL : 64 ≤ lemma23PaperL D) {s : ℂ} (hs : 0 ≤ s.re)
    {B : ℝ} (hB : 0 < B) (hlogB : Real.log B ≤ 2 * lemma23PaperL D ^ 9) :
    ‖(∫ v : ℝ, lemma61RightMellinIntegrand (D := D) ψ s B 2 v * I) -
        (∫ v : ℝ in -(lemma23PaperL D ^ 20)..(lemma23PaperL D ^ 20),
          lemma61RightMellinIntegrand (D := D) ψ s B 2 v * I)‖ ≤
      8 * lemma44InverseSquareMass * Real.exp (-(lemma23PaperL D ^ 10) / 8) := by
  have hL0 : 0 < lemma23PaperL D := by linarith
  have hmass : 0 ≤ lemma44InverseSquareMass := tsum_nonneg (fun _ => by positivity)
  have hi := (lemma61_actual_right_gaussian_mellin ψ s hD hB
    (by norm_num : (0 : ℝ) < 2) (by linarith : 1 < s.re + 2)).1.mul_const I
  have ht := lemma44_gaussian_integral_truncation
    (fun v => lemma61RightMellinIntegrand (D := D) ψ s B 2 v * I) hi
    (C := lemma44InverseSquareMass * Real.exp (1 + 4 * lemma23PaperL D ^ 9))
    (b := 1 / (4 * lemma23PaperL D ^ 30)) (T := lemma23PaperL D ^ 20)
    (by positivity) (by positivity) (by positivity)
    (lemma61_right_mellin_gaussian_bound ψ (by linarith) hs hlogB)
  have hbt : (1 / (4 * lemma23PaperL D ^ 30)) * lemma23PaperL D ^ 20 =
      1 / (4 * lemma23PaperL D ^ 10) := by
    field_simp
  have hbe : (1 / (4 * lemma23PaperL D ^ 30)) * (lemma23PaperL D ^ 20) ^ 2 =
      lemma23PaperL D ^ 10 / 4 := by
    field_simp
  apply ht.trans
  calc
    _ = 8 * lemma44InverseSquareMass *
        (lemma23PaperL D ^ 10 * Real.exp
          (1 + 4 * lemma23PaperL D ^ 9 - lemma23PaperL D ^ 10 / 4)) := by
      rw [hbt,show -(1 / (4 * lemma23PaperL D ^ 30)) *
        (lemma23PaperL D ^ 20) ^ 2 = -(lemma23PaperL D ^ 10 / 4) by linarith only [hbe]]
      rw [show 1 + 4 * lemma23PaperL D ^ 9 - lemma23PaperL D ^ 10 / 4 =
        (1 + 4 * lemma23PaperL D ^ 9) + -(lemma23PaperL D ^ 10 / 4) by ring]
      simp only [Real.exp_add]
      field_simp <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (lemma61_right_gaussian_exponent_absorption hL)
      (by positivity)

lemma lemma61_mellin_normalization_norm_le_one :
    ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ ≤ 1 := by
  have hbase : 1 ≤ ‖2 * (Real.pi : ℂ) * I‖ := by
    rw [norm_mul,norm_mul,norm_I,mul_one,Complex.norm_of_nonneg Real.pi_pos.le]
    norm_num
    linarith [Real.one_le_pi_div_two]
  rw [norm_inv]
  exact inv_le_one_of_one_le₀ hbase

lemma lemma61_actual_finite_right_K_bound {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hD : 1 < D)
    (hL : 64 ≤ lemma23PaperL D) {s : ℂ} (hs : Lemma61InRegion D s) :
    ‖(2 * (Real.pi : ℂ) * I)⁻¹ *
        (∫ v : ℝ in -(lemma23PaperL D ^ 20)..(lemma23PaperL D ^ 20),
          lemma61RightMellinIntegrand (D := D) ψ s (lemma61PaperP4 D) 2 v * I) -
        lemma61ActualK D ψ s‖ ≤
      9 * lemma44InverseSquareMass * Real.exp (-(lemma23PaperL D ^ 10) / 8) := by
  have hre := (lemma61_region_real_parts (by linarith) hs).1
  have ht := lemma61_actual_right_mellin_truncation ψ hD hL hre.le
    (lemma61_P4_pos hD) (lemma61_P4_log_bound (by linarith))
  have hk := lemma61_actual_K_right_mellin_identity ψ s hD
    (by norm_num : (0 : ℝ) < 2) (by linarith : 1 < s.re + 2)
  have hc := lemma61_actual_K_cutoff_correction_bound ψ hD (by linarith) hre.le
  have he : (2 * (Real.pi : ℂ) * I)⁻¹ *
        (∫ v : ℝ in -(lemma23PaperL D ^ 20)..(lemma23PaperL D ^ 20),
          lemma61RightMellinIntegrand (D := D) ψ s (lemma61PaperP4 D) 2 v * I) - lemma61ActualK D ψ s =
      (2 * (Real.pi : ℂ) * I)⁻¹ *
        ((∫ v : ℝ in -(lemma23PaperL D ^ 20)..(lemma23PaperL D ^ 20),
          lemma61RightMellinIntegrand (D := D) ψ s (lemma61PaperP4 D) 2 v * I) -
        (∫ v : ℝ, lemma61RightMellinIntegrand (D := D) ψ s (lemma61PaperP4 D) 2 v * I)) +
        lemma61GaussianCutoffCorrection D ψ (lemma61PaperP4 D) s := by
    linear_combination hk
  rw [he]
  apply (norm_add_le _ _).trans
  have ht' := (mul_le_mul_of_nonneg_right lemma61_mellin_normalization_norm_le_one
    (norm_nonneg ((∫ v : ℝ in -(lemma23PaperL D ^ 20)..(lemma23PaperL D ^ 20),
      lemma61RightMellinIntegrand (D := D) ψ s (lemma61PaperP4 D) 2 v * I) -
      (∫ v : ℝ, lemma61RightMellinIntegrand (D := D) ψ s (lemma61PaperP4 D) 2 v * I)))).trans
    (by simpa only [one_mul,norm_sub_rev] using ht)
  rw [← norm_mul] at ht'
  have hc' : ‖lemma61GaussianCutoffCorrection D ψ (lemma61PaperP4 D) s‖ ≤
      lemma44InverseSquareMass * Real.exp (-(lemma23PaperL D ^ 10) / 8) := by
    apply hc.trans
    apply mul_le_mul_of_nonneg_left _ (tsum_nonneg (fun _ => by positivity))
    apply Real.exp_le_exp.mpr
    have hpos : 0 ≤ lemma23PaperL D ^ 10 := by positivity
    linarith
  linarith only [ht',hc']

end ZhangLS.Spec
