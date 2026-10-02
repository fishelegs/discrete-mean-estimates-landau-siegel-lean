import ZhangLS.Spec.Lemma61GaussianMellin

/-! # Actual Gaussian inputs for the original Lemma 6.1

The original family, strict region, actual K/N and actual E1 are retained.
Gaussian inversion and both cutoff errors are proved for the actual weights.
The full Lemma61Target remains unproved: contour and Z-difference bounds remain.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Real Topology
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

lemma lemma61_cutoff_endpoint_budget {D : ℕ} (hL : 3 ≤ lemma23PaperL D)
    {x : ℝ} (hx : 0 < x) (hlogx : Real.log x ≤ 2 * lemma23PaperL D ^ 9)
    {n : ℕ} (hn : 0 < n) (hcut : 2 * x ≤ (n : ℝ)) :
    lemma23PaperL D ^ 10 + 2 * Real.log (n : ℝ) ≤ -zhangGaussianEndpoint D (x / n) := by
  let L := lemma23PaperL D
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
  have hlogn : Real.log 2 + Real.log x ≤ Real.log (n : ℝ) := by
    simpa [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hx.ne'] using
      Real.log_le_log (by positivity : 0 < 2 * x) hcut
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have ht := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at ht ⊢
    linarith only [ht]
  have h5 : (3 : ℝ) ^ 5 ≤ L ^ 5 := pow_le_pow_left₀ (by norm_num) hL 5
  have h10 : 1 ≤ L ^ 10 := one_le_pow₀ hL1
  have h9 : L ^ 9 ≤ L ^ 10 := pow_le_pow_right₀ hL1 (by norm_num)
  have hgrowth : 12 * L ^ 10 ≤ L ^ 15 := by
    calc
      12 * L ^ 10 ≤ L ^ 5 * L ^ 10 := by norm_num at h5; nlinarith only [h5,h10]
      _ = L ^ 15 := by ring
  have hnon : 0 ≤ L ^ 15 - 2 := by linarith only [hgrowth,h10]
  have hgap := mul_nonneg hnon
    (show 0 ≤ Real.log (n : ℝ) - Real.log x - 1 / 2 by linarith only [hlogn,hlog2])
  rw [zhangGaussianEndpoint,Real.log_div hx.ne' hnr.ne']
  change L ^ 10 + 2 * Real.log (n : ℝ) ≤ -(L ^ 15 * (Real.log x - Real.log (n : ℝ)))
  nlinarith only [hgap,hgrowth,h10,h9,hlogx]

lemma lemma61_cutoff_gaussian_weight_bound {D : ℕ} (hL : 3 ≤ lemma23PaperL D)
    {x : ℝ} (hx : 0 < x) (hlogx : Real.log x ≤ 2 * lemma23PaperL D ^ 9)
    {n : ℕ} (hn : 0 < n) (hcut : 2 * x ≤ (n : ℝ)) :
    zhangGaussianWeight D (x / n) ≤
      Real.exp (-(lemma23PaperL D ^ 10)) * ((n : ℝ) ^ 2)⁻¹ := by
  have hbudget := lemma61_cutoff_endpoint_budget hL hx hlogx hn hcut
  have hL1 : 1 ≤ lemma23PaperL D := by linarith
  have hlogn : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn)
  have h10 : 1 ≤ lemma23PaperL D ^ 10 := one_le_pow₀ hL1
  calc
    _ ≤ Real.exp (zhangGaussianEndpoint D (x / n)) :=
      lemma44_gaussian_weight_le_exp_endpoint (by linarith only [hbudget,hlogn,h10])
    _ ≤ Real.exp (-(lemma23PaperL D ^ 10) - 2 * Real.log (n : ℝ)) :=
      Real.exp_le_exp.mpr (by linarith only [hbudget])
    _ = _ := by
      rw [Real.exp_sub]
      have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
      have he : Real.exp (2 * Real.log (n : ℝ)) = (n : ℝ) ^ 2 := by
        simpa [Real.exp_log hn0] using Real.exp_nat_mul (Real.log (n : ℝ)) 2
      rw [he]
      ring

lemma lemma61_cutoff_correction_term_bound {D p : ℕ}
    (ψ : DirichletCharacter ℂ p) (hD : 1 < D) (hL : 3 ≤ lemma23PaperL D)
    {x : ℝ} (hx : 0 < x) (hlogx : Real.log x ≤ 2 * lemma23PaperL D ^ 9)
    {s : ℂ} (hs : 0 ≤ s.re) (n : ℕ) :
    ‖LSeries.term (fun m => ψ (m : ZMod p)) s n *
      ((zhangGaussianWeight D (x / n) - lemma61GaussianStar D (x / n) : ℝ) : ℂ)‖ ≤
        Real.exp (-(lemma23PaperL D ^ 10)) * ((n : ℝ) ^ 2)⁻¹ := by
  by_cases hn0 : n = 0
  · simp [hn0]
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
  by_cases hy : 1 / 2 < x / n
  · simp [lemma61_gaussian_star_above_half hy]
    positivity
  have hcut : 2 * x ≤ (n : ℝ) := by
    have ht := (div_le_iff₀ hnr).mp (le_of_not_gt hy)
    linarith only [ht]
  have hg : 0 ≤ zhangGaussianWeight D (x / n) :=
    zhangGaussianWeight_nonneg hD (div_pos hx hnr)
  have ht : ‖LSeries.term (fun m => ψ (m : ZMod p)) s n‖ ≤ 1 := by
    rw [LSeries.norm_term_eq,if_neg hn0]
    exact (div_le_self (norm_nonneg _) (Real.one_le_rpow (by exact_mod_cast hn) hs)).trans
      (ψ.norm_le_one _)
  rw [lemma61_gaussian_star_below_half (le_of_not_gt hy),sub_zero,norm_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hg]
  calc
    _ ≤ 1 * (Real.exp (-(lemma23PaperL D ^ 10)) * ((n : ℝ) ^ 2)⁻¹) :=
      mul_le_mul ht (lemma61_cutoff_gaussian_weight_bound hL hx hlogx hn hcut) hg (by norm_num)
    _ = _ := one_mul _

lemma lemma61_cutoff_correction_summable_and_bound {D p : ℕ}
    (ψ : DirichletCharacter ℂ p) (hD : 1 < D) (hL : 3 ≤ lemma23PaperL D)
    {x : ℝ} (hx : 0 < x) (hlogx : Real.log x ≤ 2 * lemma23PaperL D ^ 9)
    {s : ℂ} (hs : 0 ≤ s.re) :
    Summable (fun n : ℕ => LSeries.term (fun m => ψ (m : ZMod p)) s n *
      ((zhangGaussianWeight D (x / n) - lemma61GaussianStar D (x / n) : ℝ) : ℂ)) ∧
      ‖lemma61GaussianCutoffCorrection D ψ x s‖ ≤
        lemma44InverseSquareMass * Real.exp (-(lemma23PaperL D ^ 10)) := by
  have hmajor := lemma44_inverse_square_summable.mul_left
    (Real.exp (-(lemma23PaperL D ^ 10)))
  have hnorm : Summable (fun n : ℕ => ‖LSeries.term (fun m => ψ (m : ZMod p)) s n *
      ((zhangGaussianWeight D (x / n) - lemma61GaussianStar D (x / n) : ℝ) : ℂ)‖) :=
    hmajor.of_nonneg_of_le (fun n => norm_nonneg _)
      (lemma61_cutoff_correction_term_bound ψ hD hL hx hlogx hs)
  refine ⟨hnorm.of_norm,?_⟩
  unfold lemma61GaussianCutoffCorrection
  calc
    _ ≤ ∑' n : ℕ, ‖LSeries.term (fun m => ψ (m : ZMod p)) s n *
        ((zhangGaussianWeight D (x / n) - lemma61GaussianStar D (x / n) : ℝ) : ℂ)‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, Real.exp (-(lemma23PaperL D ^ 10)) * ((n : ℝ) ^ 2)⁻¹ :=
      hnorm.tsum_le_tsum (lemma61_cutoff_correction_term_bound ψ hD hL hx hlogx hs) hmajor
    _ = _ := by rw [tsum_mul_left]; exact mul_comm _ _

lemma lemma61_P4_log_bound {D : ℕ} (hL : 3 ≤ lemma23PaperL D) :
    Real.log (lemma61PaperP4 D) ≤ 2 * lemma23PaperL D ^ 9 := by
  let L := lemma23PaperL D
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hP : 0 < lemma23PaperP D := Real.exp_pos _
  have hT : 0 < lemma56PaperT D := Real.exp_pos _
  have ht0 : 0 < lemma51PaperT0 D := pow_pos hL0 519
  have hT1 : 1 ≤ lemma56PaperT D :=
    Real.one_le_exp_iff.mpr (Real.rpow_nonneg hL0.le _)
  have hneg : lemma56PaperT D ^ (-2 : ℤ) ≤ 1 := by
    rw [zpow_neg,zpow_ofNat]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hT1)
  have hprod : lemma61PaperP4 D ≤ lemma23PaperP D * lemma51PaperT0 D := by
    unfold lemma61PaperP4
    have hh := mul_le_mul_of_nonneg_left hneg hP.le
    simpa using mul_le_mul_of_nonneg_right hh ht0.le
  have hx : 0 < lemma61PaperP4 D := by
    unfold lemma61PaperP4
    positivity
  have h8 : (3 : ℝ) ^ 8 ≤ L ^ 8 := pow_le_pow_left₀ (by norm_num) hL 8
  have h519 : 519 * L ≤ L ^ 9 := by
    calc
      519 * L ≤ L ^ 8 * L := by norm_num at h8; nlinarith only [h8,hL0]
      _ = L ^ 9 := by ring
  have hlog : 519 * Real.log L ≤ L ^ 9 := by
    have hh := Real.log_le_sub_one_of_pos hL0
    linarith only [hh,h519]
  calc
    _ ≤ Real.log (lemma23PaperP D * lemma51PaperT0 D) := Real.log_le_log hx hprod
    _ = L ^ 9 + 519 * Real.log L := by
      rw [Real.log_mul hP.ne' ht0.ne',lemma23PaperP,Real.log_exp,lemma51PaperT0,Real.log_pow]
      rfl
    _ ≤ _ := by change _ ≤ 2 * L ^ 9; linarith only [hlog]

lemma lemma61_T_squared_log_bound {D : ℕ} (hL : 3 ≤ lemma23PaperL D) :
    Real.log (lemma56PaperT D ^ 2) ≤ 2 * lemma23PaperL D ^ 9 := by
  have hb : lemma23PaperL D ^ (11 / 10 : ℝ) ≤ lemma23PaperL D ^ 9 := by
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le
      (by linarith : 1 ≤ lemma23PaperL D) (by norm_num : (11 / 10 : ℝ) ≤ (9 : ℕ))
  rw [Real.log_pow,lemma56PaperT,Real.log_exp]
  norm_num
  linarith only [hb]

lemma lemma61_actual_K_cutoff_correction_bound {D p : ℕ}
    (ψ : DirichletCharacter ℂ p) (hD : 1 < D) (hL : 3 ≤ lemma23PaperL D)
    {s : ℂ} (hs : 0 ≤ s.re) :
    ‖lemma61GaussianCutoffCorrection D ψ (lemma61PaperP4 D) s‖ ≤
      lemma44InverseSquareMass * Real.exp (-(lemma23PaperL D ^ 10)) :=
  (lemma61_cutoff_correction_summable_and_bound ψ hD hL (lemma61_P4_pos hD)
    (lemma61_P4_log_bound hL) hs).2

lemma lemma61_actual_N_cutoff_correction_bound {D p : ℕ}
    (ψ : DirichletCharacter ℂ p) (hD : 1 < D) (hL : 3 ≤ lemma23PaperL D)
    {s : ℂ} (hs : s.re ≤ 1) :
    ‖lemma61GaussianCutoffCorrection D ψ (lemma56PaperT D ^ 2) (1 - s)‖ ≤
      lemma44InverseSquareMass * Real.exp (-(lemma23PaperL D ^ 10)) :=
  (lemma61_cutoff_correction_summable_and_bound ψ hD hL (pow_pos (Real.exp_pos _) 2)
    (lemma61_T_squared_log_bound hL) (by simpa using sub_nonneg.mpr hs)).2

end ZhangLS.Spec
