import ZhangLS.Spec.Lemma112GaussianFourier
/-! # An actual positive lower bound for E₂, with no artificial error floor -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Real Topology

lemma lemma112_exp_small_at_paper_scale {L : ℝ} (hL : 64 ≤ L) :
    Real.exp (-(L ^ 10) / 8) ≤ 1 / 32 := by
  have h1 : 1 ≤ L := by linarith
  have h64 : (64 : ℝ) ≤ L ^ 10 :=
    hL.trans (le_self_pow₀ h1 (by norm_num))
  have h2 : (64 : ℝ) ^ 2 ≤ L ^ 10 :=
    (pow_le_pow_left₀ (by norm_num) hL 2).trans (pow_le_pow_right₀ h1 (by norm_num))
  have he := Real.add_one_le_exp (L ^ 10 / 8)
  have he32 : 32 ≤ Real.exp (L ^ 10 / 8) := by norm_num at h2; linarith only [he, h2]
  rw [neg_div, Real.exp_neg]
  simpa only [one_div] using
    (inv_le_inv₀ (Real.exp_pos _) (by positivity : (0 : ℝ) < 32)).mpr he32

lemma lemma112_frequency_recovery_budget {L K : ℝ} (hL : 64 ≤ L)
    (hK : K ≤ 2 * Real.exp (L ^ 9)) :
    K * Real.exp (-((L ^ 15) ^ 2) / 4) ≤ 1 / 4 := by
  have h1 : 1 ≤ L := by linarith
  have h0 : 0 ≤ L := by linarith
  have h30 : L ^ 10 ≤ L ^ 30 := pow_le_pow_right₀ h1 (by norm_num)
  have h10 : 64 * L ^ 9 ≤ L ^ 10 := by
    have h := mul_le_mul_of_nonneg_right hL (pow_nonneg h0 9)
    convert h using 1 <;> ring
  have hex : L ^ 9 - (L ^ 15) ^ 2 / 4 ≤ -(L ^ 10) / 8 := by
    have hid : (L ^ 15) ^ 2 = L ^ 30 := by ring
    rw [hid]
    linarith only [h30, h10, pow_nonneg h0 9]
  calc
    _ ≤ (2 * Real.exp (L ^ 9)) * Real.exp (-((L ^ 15) ^ 2) / 4) :=
      mul_le_mul_of_nonneg_right hK (Real.exp_nonneg _)
    _ = 2 * Real.exp (L ^ 9 - (L ^ 15) ^ 2 / 4) := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    _ ≤ 2 * Real.exp (-(L ^ 10) / 8) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hex) (by norm_num)
    _ ≤ 1 / 4 := by linarith only [lemma112_exp_small_at_paper_scale hL]

lemma lemma112_gaussian_tail_recovery_budget {L K : ℝ} (hL : 64 ≤ L)
    (hK0 : 0 ≤ K) (hK : K ≤ 2 * Real.exp (L ^ 9)) :
    8 * K * (L ^ 15) ^ 2 / L ^ 20 *
      Real.exp (-((L ^ 20) ^ 2) / (4 * (L ^ 15) ^ 2)) ≤ 1 / 2 := by
  have h0 : 0 < L := by linarith
  have h1 : 1 ≤ L := by linarith
  have hid : -((L ^ 20) ^ 2) / (4 * (L ^ 15) ^ 2) = -(L ^ 10) / 4 := by
    field_simp
    <;> ring
  have hp : 8 * K * (L ^ 15) ^ 2 / L ^ 20 = 8 * K * L ^ 10 := by
    field_simp
    <;> ring
  rw [hid, hp]
  calc
    _ ≤ 16 * (L ^ 10 * Real.exp (L ^ 9 - L ^ 10 / 4)) := by
      have hm := mul_le_mul_of_nonneg_right hK
        (by positivity : 0 ≤ 8 * L ^ 10 * Real.exp (-(L ^ 10) / 4))
      rw [show L ^ 9 - L ^ 10 / 4 = L ^ 9 + -(L ^ 10) / 4 by ring, Real.exp_add]
      convert hm using 1 <;> ring
    _ ≤ 16 * (L ^ 10 * Real.exp (1 + 4 * L ^ 9 - L ^ 10 / 4)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      nlinarith only [pow_nonneg h0.le 9]
    _ ≤ 16 * Real.exp (-(L ^ 10) / 8) :=
      mul_le_mul_of_nonneg_left (lemma61_right_gaussian_exponent_absorption hL) (by norm_num)
    _ ≤ 1 / 2 := by linarith only [lemma112_exp_small_at_paper_scale hL]

lemma lemma112_P1_one_lt {D : ℕ} (hL : 3 ≤ lemma23PaperL D) :
    1 < lemma112PaperP1 D := by
  unfold lemma112PaperP1 lemma23PaperP
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  exact Real.one_lt_exp_iff.mpr (by positivity)

lemma lemma112_short_cutoff_card {D : ℕ} (hL : 3 ≤ lemma23PaperL D) :
    (((Finset.Icc 1 ⌈lemma112PaperP1 D⌉₊).filter
      (fun n : ℕ => (n : ℝ) < lemma112PaperP1 D)).card : ℝ) ≤
        2 * Real.exp (lemma23PaperL D ^ 9) := by
  classical
  have hP : 1 ≤ Real.exp (lemma23PaperL D ^ 9) := Real.one_le_exp_iff.mpr (by positivity)
  have hP1 : lemma112PaperP1 D ≤ Real.exp (lemma23PaperL D ^ 9) := by
    unfold lemma112PaperP1 lemma23PaperP
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    apply Real.exp_le_exp.mpr
    have hp : 0 ≤ lemma23PaperL D ^ 9 := by positivity
    nlinarith only [hp]
  have hc : ((Finset.Icc 1 ⌈lemma112PaperP1 D⌉₊).filter
      (fun n : ℕ => (n : ℝ) < lemma112PaperP1 D)).card ≤ ⌈lemma112PaperP1 D⌉₊ := by
    have h := Finset.card_filter_le (s := Finset.Icc 1 ⌈lemma112PaperP1 D⌉₊)
      (p := fun n : ℕ => (n : ℝ) < lemma112PaperP1 D)
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using h
  have hceil := (Nat.ceil_lt_add_one (le_trans (by norm_num : (0 : ℝ) ≤ 1)
    (lemma112_P1_one_lt hL).le)).le
  have hcast : (((Finset.Icc 1 ⌈lemma112PaperP1 D⌉₊).filter
      (fun n : ℕ => (n : ℝ) < lemma112PaperP1 D)).card : ℝ) ≤ ⌈lemma112PaperP1 D⌉₊ := by
    exact_mod_cast hc
  linarith only [hP, hP1, hceil, hcast]

/-- The original norm integral is at least L^15, uniformly in χ, ψ and height. -/
lemma lemma112_actual_error_integral_lower {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hL : 64 ≤ lemma23PaperL D) {s : ℂ} (hs : 0 ≤ s.re) :
    lemma23PaperL D ^ 15 ≤
      ∫ v in -(lemma23PaperL D ^ 20)..(lemma23PaperL D ^ 20),
        ‖lemma112ShortPolynomial χ ψ (s + I * (v : ℂ))‖ *
          Real.exp (-(v ^ 2) / (4 * lemma23PaperL D ^ 30)) := by
  classical
  let S := (Finset.Icc 1 ⌈lemma112PaperP1 D⌉₊).filter
    (fun n : ℕ => (n : ℝ) < lemma112PaperP1 D)
  have h0 : 0 < lemma23PaperL D := by linarith
  have h1 : 1 ≤ lemma23PaperL D := by linarith
  have hS : ∀ n ∈ S, 1 ≤ n := fun n hn =>
    (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
  have hP1 := lemma112_P1_one_lt (by linarith : 3 ≤ lemma23PaperL D)
  have hmem : 1 ∈ S := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨le_rfl, ?_⟩, by simpa using hP1⟩
    exact (Nat.one_le_ceil_iff).mpr (by linarith only [hP1])
  have hb := lemma112_truncated_gaussian_norm_lower S (lemma112Coefficient χ ψ) hS hmem
    (lemma112_coefficient_one χ ψ) (fun n hn => lemma112_coefficient_norm_le_one χ ψ n)
    hs (pow_pos h0 15) (pow_pos h0 20)
  have hc := lemma112_short_cutoff_card (by linarith : 3 ≤ lemma23PaperL D)
  have hf := lemma112_frequency_recovery_budget hL hc
  have ht := lemma112_gaussian_tail_recovery_budget hL (by positivity : (0 : ℝ) ≤ S.card) hc
  have hmass : 2 * lemma23PaperL D ^ 15 ≤ 2 * Real.sqrt Real.pi * lemma23PaperL D ^ 15 := by
    have hm := mul_le_mul_of_nonneg_right lemma111_sqrt_pi_ge_one (pow_nonneg h0.le 15)
    linarith only [hm]
  have ha1 : 1 ≤ lemma23PaperL D ^ 15 := one_le_pow₀ h1
  have hprod := mul_le_mul_of_nonneg_left hf
    (by positivity : 0 ≤ 2 * Real.sqrt Real.pi * lemma23PaperL D ^ 15)
  have he : (lemma23PaperL D ^ 15) ^ 2 = lemma23PaperL D ^ 30 := by ring
  change _ ≤ ∫ v in -(lemma23PaperL D ^ 20)..(lemma23PaperL D ^ 20),
    ‖lemma112ShortPolynomial χ ψ (s + I * (v : ℂ))‖ *
      Real.exp (-(v ^ 2) / (4 * (lemma23PaperL D ^ 15) ^ 2)) at hb
  rw [he] at hb ht hprod
  linarith only [hb, ht, hprod, hmass, ha1]

lemma lemma112_E2_polynomial_floor {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hL : 64 ≤ lemma23PaperL D) {s : ℂ} (hs : 0 ≤ s.re) :
    lemma23PaperL D ^ (-53 : ℤ) ≤ lemma112ActualE2 χ ψ s := by
  have h0 : 0 < lemma23PaperL D := by linarith
  have h := mul_le_mul_of_nonneg_left (lemma112_actual_error_integral_lower χ ψ hL hs)
    (zpow_nonneg h0.le (-68 : ℤ))
  have he : lemma23PaperL D ^ (-68 : ℤ) * lemma23PaperL D ^ 15 =
      lemma23PaperL D ^ (-53 : ℤ) := by
    rw [← zpow_natCast (lemma23PaperL D) 15, ← zpow_add₀ h0.ne']
    norm_num
  rw [he] at h
  exact h

end ZhangLS.Spec
