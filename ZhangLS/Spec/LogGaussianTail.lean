import ZhangLS.Spec.LogGaussianWeight
import ZhangLS.Spec.Lemma171GaussianTail

/-! Scalar logarithmic Gaussian comparison on the actual short and far ranges. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex MeasureTheory Filter
open scoped Topology

lemma lemma171_log_gaussian_denominator_ge_one {D : ℕ} (hL : 1 ≤ lemma23PaperL D) :
    1 ≤ 2 * Real.sqrt Real.pi * lemma57GaussianLogScale D := by
  have hs : 1 ≤ Real.sqrt Real.pi := by
    simpa using Real.sqrt_le_sqrt (by linarith [Real.one_le_pi_div_two] : 1 ≤ Real.pi)
  have hc : 1 ≤ lemma57GaussianLogScale D := one_le_pow₀ hL
  nlinarith

lemma lemma171_log_gaussian_error_pos {D : ℕ} (hD : 1 < D) {x : ℝ} (hx : 0 < x) :
    0 ≤ lemma171LogGaussianWeight D x - max (Real.log x) 0 ∧
    lemma171LogGaussianWeight D x - max (Real.log x) 0 ≤
      Real.exp (-(zhangGaussianEndpoint D x) ^ 2) /
        (2 * Real.sqrt Real.pi * lemma57GaussianLogScale D) := by
  have h := lemma171_log_gaussian_error hD (Real.log x)
  simpa [Real.exp_log hx, lemma57GaussianLogScale, zhangGaussianEndpoint] using h

lemma lemma171_log_gaussian_weight_nonneg {D : ℕ} (hD : 1 < D) {x : ℝ} (hx : 0 < x) :
    0 ≤ lemma171LogGaussianWeight D x := by
  simpa [Real.exp_log hx] using lemma171_log_gaussian_nonneg hD (Real.log x)

lemma lemma171_log_gaussian_weight_le {D : ℕ} (hD : 1 < D)
    (hL : 1 ≤ lemma23PaperL D) {x : ℝ} (hx : 0 < x) :
    lemma171LogGaussianWeight D x ≤ max (Real.log x) 0 + 1 := by
  have h := (lemma171_log_gaussian_error_pos hD hx).2
  have he : Real.exp (-(zhangGaussianEndpoint D x) ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))
  have hd := lemma171_log_gaussian_denominator_ge_one hL
  have hh : Real.exp (-(zhangGaussianEndpoint D x) ^ 2) /
      (2 * Real.sqrt Real.pi * lemma57GaussianLogScale D) ≤ 1 :=
    (div_le_self (Real.exp_pos _).le hd).trans he
  linarith

lemma lemma171_log_gaussian_weight_le_exp_endpoint {D : ℕ} (hD : 1 < D)
    (hL : 1 ≤ lemma23PaperL D) {x : ℝ} (hx : 0 < x)
    (hy : 1 ≤ -zhangGaussianEndpoint D x) :
    lemma171LogGaussianWeight D x ≤ Real.exp (zhangGaussianEndpoint D x) := by
  have hc : 0 < lemma57GaussianLogScale D :=
    pow_pos (Real.log_pos (by exact_mod_cast hD)) 15
  have hl : Real.log x ≤ 0 := by
    have he : zhangGaussianEndpoint D x = lemma57GaussianLogScale D * Real.log x := rfl
    rw [he] at hy
    nlinarith
  have h := (lemma171_log_gaussian_error_pos hD hx).2
  rw [max_eq_right hl, sub_zero] at h
  have hsq : -zhangGaussianEndpoint D x ≤ (zhangGaussianEndpoint D x)^2 := by
    simpa only [pow_one, neg_sq] using
      pow_le_pow_right₀ hy (by norm_num : (1 : ℕ) ≤ 2)
  calc
    _ ≤ Real.exp (-(zhangGaussianEndpoint D x) ^ 2) /
        (2 * Real.sqrt Real.pi * lemma57GaussianLogScale D) := h
    _ ≤ Real.exp (-(zhangGaussianEndpoint D x) ^ 2) :=
      div_le_self (Real.exp_pos _).le (lemma171_log_gaussian_denominator_ge_one hL)
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [hsq])

lemma lemma171_log_gaussian_short_weight_error {D : ℕ}
    (hD : 1 < D) (hL : 3 ≤ lemma23PaperL D)
    (hT : 5 * lemma23PaperL D ≤ Real.log (lemma56PaperT D))
    {n : ℕ} (hn : n ∈ Finset.Icc 1 (D ^ 4)) :
    |lemma171LogGaussianWeight D (lemma56PaperT D / n) -
      Real.log (lemma56PaperT D / n)| ≤ Real.exp (-(lemma23PaperL D ^ 16)) := by
  let L := lemma23PaperL D
  let x := lemma56PaperT D / (n : ℝ)
  have hnp : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hx : 0 < x := div_pos (Real.exp_pos _) hnp
  have hlogn : Real.log (n : ℝ) ≤ 4 * L := by
    calc
      _ ≤ Real.log ((D : ℝ) ^ 4) :=
        Real.log_le_log hnp (by exact_mod_cast (Finset.mem_Icc.mp hn).2)
      _ = _ := by rw [Real.log_pow]; rfl
  have hlogx : L ≤ Real.log x := by
    rw [show x = lemma56PaperT D / (n : ℝ) from rfl,
      Real.log_div (show lemma56PaperT D ≠ 0 from (Real.exp_pos _).ne') hnp.ne']
    linarith only [hT, hlogn]
  have he : L ^ 16 ≤ zhangGaussianEndpoint D x := by
    change L ^ 16 ≤ L ^ 15 * Real.log x
    calc
      _ = L ^ 15 * L := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlogx (by positivity)
  have h16 : 1 ≤ L ^ 16 := one_le_pow₀ (by linarith)
  have hsq : zhangGaussianEndpoint D x ≤ (zhangGaussianEndpoint D x)^2 := by
    simpa only [pow_one] using
      pow_le_pow_right₀ (h16.trans he) (by norm_num : (1 : ℕ) ≤ 2)
  have herr := lemma171_log_gaussian_error_pos hD hx
  rw [max_eq_left (by linarith : 0 ≤ Real.log x)] at herr
  rw [abs_of_nonneg herr.1]
  calc
    _ ≤ Real.exp (-(zhangGaussianEndpoint D x) ^ 2) /
        (2 * Real.sqrt Real.pi * lemma57GaussianLogScale D) := herr.2
    _ ≤ Real.exp (-(zhangGaussianEndpoint D x) ^ 2) :=
      div_le_self (Real.exp_pos _).le
        (lemma171_log_gaussian_denominator_ge_one (by linarith))
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [he, hsq])

lemma lemma171_log_gaussian_tail_weight {D : ℕ}
    (hD : 1 < D) (hL : 3 ≤ lemma23PaperL D) {n : ℕ}
    (hn : ⌊lemma23PaperP D ^ 2⌋₊ < n) :
    lemma171LogGaussianWeight D (lemma56PaperT D / n) ≤
      Real.exp (-(lemma23PaperL D ^ 24) / 10) * ((n : ℝ) ^ 3)⁻¹ := by
  let L := lemma23PaperL D
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hnp : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
  have hnr : lemma23PaperP D ^ 2 < (n : ℝ) := (Nat.floor_lt (by positivity)).mp hn
  have hlogn : 2 * L ^ 9 ≤ Real.log (n : ℝ) := by
    have h := Real.log_le_log (pow_pos (Real.exp_pos _) 2 : 0 < lemma23PaperP D ^ 2) hnr.le
    simpa [Real.log_pow, lemma23PaperP, Real.log_exp, L] using h
  have hlogT : Real.log (lemma56PaperT D) ≤ (9 / 5 : ℝ) * L ^ 9 := by
    have ht := lemma171_log_T_le (D := D) hL1
    have hp : 0 ≤ L ^ 9 := by positivity
    linarith only [ht,hp]
  have hc : 60 ≤ L ^ 15 := by
    have h4 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hL 4
    have h415 : L ^ 4 ≤ L ^ 15 := pow_le_pow_right₀ hL1 (by norm_num)
    norm_num at h4
    linarith only [h4,h415]
  have hT : 0 < lemma56PaperT D := Real.exp_pos _
  have hy : L ^ 24 / 10 + 3 * Real.log (n : ℝ) ≤
      -zhangGaussianEndpoint D (lemma56PaperT D / n) := by
    rw [zhangGaussianEndpoint,Real.log_div hT.ne' hnp.ne']
    change L ^ 24 / 10 + 3 * Real.log (n : ℝ) ≤
      -(L ^ 15 * (Real.log (lemma56PaperT D) - Real.log (n : ℝ)))
    have hp := mul_nonneg (by linarith only [hc] : 0 ≤ L ^ 15 - 3)
      (sub_nonneg.mpr hlogn)
    have hq := mul_nonneg (by linarith only [hc] : 0 ≤ L ^ 15 / 10 - 6)
      (show 0 ≤ L ^ 9 by positivity)
    have hr := mul_le_mul_of_nonneg_left hlogT (show 0 ≤ L ^ 15 by positivity)
    have heq : L ^ 15 * L ^ 9 = L ^ 24 := by ring
    nlinarith only [hp,hq,hr,heq]
  have h24 := lemma44_L24_dominates_linear hL
  have hlognpos : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_of_lt hn)
  calc
    _ ≤ Real.exp (zhangGaussianEndpoint D (lemma56PaperT D / n)) :=
      lemma171_log_gaussian_weight_le_exp_endpoint hD hL1 (div_pos hT hnp) (by nlinarith only [hy,h24,hL,hlognpos])
    _ ≤ Real.exp (-(L ^ 24) / 10 - 3 * Real.log (n : ℝ)) :=
      Real.exp_le_exp.mpr (by linarith only [hy])
    _ = _ := by
      rw [Real.exp_sub]
      have h3 : Real.exp (3 * Real.log (n : ℝ)) = (n : ℝ) ^ 3 := by
        simpa [Real.exp_log hnp] using Real.exp_nat_mul (Real.log (n : ℝ)) 3
      rw [h3]
      ring

end ZhangLS.Spec
