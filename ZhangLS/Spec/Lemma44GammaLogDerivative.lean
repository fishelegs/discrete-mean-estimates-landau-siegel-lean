import ZhangLS.Spec.Lemma23BorelCaratheodory
import ZhangLS.Spec.Lemma57GammaFactorGrowth

/-!
# Effective logarithmic-derivative bounds for complex Gamma

Euler's integral, recurrence and reflection give factorial bounds for Gamma
and its reciprocal on a large disk away from the real axis. Applying the
proved Borel--Carathéodory estimate on a disk of radius comparable to its
height gives a logarithmic bound, without a complex Stirling expansion.
-/

namespace ZhangLS.Spec

open Complex MeasureTheory Set
open scoped Topology

set_option maxHeartbeats 1000000

/-- Euler's integral gives an explicit factorial bound on a right-half-plane strip. -/
theorem lemma44_norm_Gamma_le_factorial {z : ℂ} {m : ℕ}
    (hlo : 1 ≤ z.re) (hhi : z.re ≤ (m : ℝ) + 1) :
    ‖Complex.Gamma z‖ ≤ 1 + (m.factorial : ℝ) := by
  let majorant : ℝ → ℝ := fun x => Real.exp (-x) * (1 + x ^ m)
  have h₀ : IntegrableOn (fun x : ℝ => Real.exp (-x)) (Ioi 0) := by
    simpa using Real.GammaIntegral_convergent (s := (1 : ℝ)) (by norm_num)
  have h₁ : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ m) (Ioi 0) := by
    convert Real.GammaIntegral_convergent (s := (m : ℝ) + 1) (by positivity) using 1
    simp
  have hmajorant : IntegrableOn majorant (Ioi 0) := by
    simpa [majorant, mul_add] using h₀.add h₁
  have hmass : (∫ x : ℝ in Ioi 0, majorant x) = 1 + (m.factorial : ℝ) := by
    simp only [majorant, mul_add, mul_one]
    rw [integral_add h₀ h₁]
    have h₀mass : (∫ x : ℝ in Ioi 0, Real.exp (-x)) = 1 := by
      simpa using (Real.Gamma_eq_integral (s := (1 : ℝ)) (by norm_num)).symm
    have h₁mass : (∫ x : ℝ in Ioi 0, Real.exp (-x) * x ^ m) =
        (m.factorial : ℝ) := by
      have h := Real.Gamma_eq_integral (s := (m : ℝ) + 1) (by positivity)
      simpa [Real.Gamma_nat_eq_factorial] using h.symm
    rw [h₀mass, h₁mass]
  have hz : 0 < z.re := by linarith
  rw [Complex.Gamma_eq_integral hz, Complex.GammaIntegral]
  calc
    ‖∫ x : ℝ in Ioi 0, (Real.exp (-x) : ℂ) * (x : ℂ) ^ (z - 1)‖ ≤
        ∫ x : ℝ in Ioi 0, ‖(Real.exp (-x) : ℂ) * (x : ℂ) ^ (z - 1)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ in Ioi 0, majorant x := by
      apply integral_mono_ae (Complex.GammaIntegral_convergent hz).norm hmajorant
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
      rw [norm_mul, Complex.norm_of_nonneg (Real.exp_nonneg _),
        norm_cpow_eq_rpow_re_of_pos hx]
      simp only [Complex.sub_re, Complex.one_re]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      change x ^ (z.re - 1) ≤ 1 + x ^ m
      rcases le_total x 1 with hx₁ | hx₁
      · exact (Real.rpow_le_one hx.le hx₁ (by linarith)).trans
          (le_add_of_nonneg_right (pow_nonneg hx.le m))
      · have hp := Real.rpow_le_rpow_of_exponent_le hx₁ (show z.re - 1 ≤ (m : ℝ) by linarith)
        simpa using hp.trans (le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1))
    _ = _ := hmass

/-- Each recurrence step increases the modulus when the imaginary part has modulus at least one. -/
theorem lemma44_norm_Gamma_le_shift {z : ℂ} (him : 1 ≤ |z.im|) (k : ℕ) :
    ‖Complex.Gamma z‖ ≤ ‖Complex.Gamma (z + k)‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have him' : 1 ≤ |(z + (k : ℂ)).im| := by simpa using him
    have hnorm : 1 ≤ ‖z + (k : ℂ)‖ := him'.trans (Complex.abs_im_le_norm _)
    have hne : z + (k : ℂ) ≠ 0 := norm_pos_iff.mp (by linarith)
    have hstep : ‖Complex.Gamma (z + k)‖ ≤ ‖Complex.Gamma (z + k + 1)‖ := by
      rw [Complex.Gamma_add_one _ hne, norm_mul]
      nlinarith [norm_nonneg (Complex.Gamma (z + k))]
    exact ih.trans (by simpa [Nat.cast_add, add_assoc] using hstep)

/-- A computable bound on a rectangle extending into the left half-plane. -/
theorem lemma44_norm_Gamma_le_rectangle {z : ℂ} {n : ℕ}
    (hre : |z.re| ≤ 2 * (n : ℝ) + 1) (him : 1 ≤ |z.im|) :
    ‖Complex.Gamma z‖ ≤ 1 + ((4 * n + 2).factorial : ℝ) := by
  apply (lemma44_norm_Gamma_le_shift him (2 * n + 2)).trans
  apply lemma44_norm_Gamma_le_factorial
  · norm_num
    linarith [(abs_le.mp hre).1]
  · norm_num
    linarith [(abs_le.mp hre).2]

/-- Reflection controls the reciprocal Gamma factor with the same factorial budget. -/
theorem lemma44_norm_Gamma_inv_le_rectangle {z : ℂ} {n : ℕ}
    (hre : |z.re| ≤ 2 * (n : ℝ)) (him : 1 ≤ |z.im|) :
    ‖(Complex.Gamma z)⁻¹‖ ≤
      (1 + ((4 * n + 2).factorial : ℝ)) * Real.exp (Real.pi * |z.im|) := by
  have hz : z.im ≠ 0 := by intro h; rw [h, abs_zero] at him; linarith
  have hpoles (w : ℂ) (hw : w.im ≠ 0) : ∀ m : ℕ, w ≠ -(m : ℂ) := by
    intro m h; apply hw; rw [h]; simp
  have hΓ := Complex.Gamma_ne_zero (hpoles z hz)
  have hΓ' := Complex.Gamma_ne_zero (hpoles (1 - z) (by simpa using neg_ne_zero.mpr hz))
  have hsin : Complex.sin (Real.pi * z) ≠ 0 := by
    intro h
    have hreflection := Complex.Gamma_mul_Gamma_one_sub z
    rw [h, div_zero] at hreflection
    exact (mul_ne_zero hΓ hΓ') hreflection
  have hinv : (Complex.Gamma z)⁻¹ =
      Complex.Gamma (1 - z) * Complex.sin (Real.pi * z) / Real.pi := by
    apply mul_left_cancel₀ hΓ
    rw [mul_inv_cancel₀ hΓ, mul_div_assoc, ← mul_assoc, Complex.Gamma_mul_Gamma_one_sub]
    field_simp [hsin, Real.pi_ne_zero]
  have hreflectionBound : ‖Complex.Gamma (1 - z)‖ ≤
      1 + ((4 * n + 2).factorial : ℝ) := by
    apply lemma44_norm_Gamma_le_rectangle
    · simp only [Complex.sub_re, Complex.one_re]
      have h := abs_add_le 1 (-z.re)
      simp only [abs_one, abs_neg, ← sub_eq_add_neg] at h
      exact h.trans (by linarith)
    · simpa using him
  have hsinBound : ‖Complex.sin (Real.pi * z)‖ ≤ Real.exp (Real.pi * |z.im|) := by
    have h := norm_sin_le_exp_abs_im (Real.pi * z)
    simpa [Complex.mul_im, abs_mul, abs_of_pos Real.pi_pos] using h
  rw [hinv, norm_div, norm_mul, Complex.norm_of_nonneg Real.pi_pos.le]
  exact (div_le_self (by positivity) (by linarith [Real.one_le_pi_div_two])).trans
    (mul_le_mul hreflectionBound hsinBound (norm_nonneg _) (by positivity))

/-- A logarithmic derivative bound on disks with radius comparable to their height.
The finite factorial budget will be converted into a logarithm in the next theorem. -/
theorem lemma44_norm_logDeriv_Gamma_le_factorial {s : ℂ} {n : ℕ}
    (hn : 1 ≤ n) (hre : |s.re| ≤ (n : ℝ))
    (hlo : 3 * (n : ℝ) ≤ |s.im|) (hhi : |s.im| ≤ 4 * (n : ℝ)) :
    ‖logDeriv Complex.Gamma s‖ ≤
      4 * Real.log ((1 + ((4 * n + 2).factorial : ℝ)) ^ 2 *
        Real.exp (4 * Real.pi * (n : ℝ))) / (n : ℝ) := by
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  let B : ℝ := 1 + ((4 * n + 2).factorial : ℝ)
  let H : ℝ := B ^ 2 * Real.exp (4 * Real.pi * (n : ℝ))
  have hB : 1 ≤ B := by dsimp [B]; exact le_add_of_nonneg_right (by positivity)
  have hH : 1 < H := by
    have he : 1 < Real.exp (4 * Real.pi * (n : ℝ)) := Real.one_lt_exp_iff.mpr (by positivity)
    have hB2 : 1 ≤ B ^ 2 := one_le_pow₀ hB
    dsimp [H]
    nlinarith
  have hdisk {z : ℂ} (hz : z ∈ Metric.ball s (n : ℝ)) :
      |z.re| ≤ 2 * (n : ℝ) ∧ 1 ≤ |z.im| := by
    have hdist : ‖z - s‖ < (n : ℝ) := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    have hreal : |z.re - s.re| < (n : ℝ) := by
      simpa using (Complex.abs_re_le_norm (z - s)).trans_lt hdist
    have himag : |z.im - s.im| < (n : ℝ) := by
      simpa using (Complex.abs_im_le_norm (z - s)).trans_lt hdist
    constructor
    · have htriangle := abs_add_le (z.re - s.re) s.re
      simp only [sub_add_cancel] at htriangle
      linarith
    · have htriangle := abs_add_le (s.im - z.im) z.im
      simp only [sub_add_cancel, abs_sub_comm s.im z.im] at htriangle
      linarith
  apply lemma23_norm_logDeriv_le_of_norm_ratio_bound_on_ball hnpos hH
  · intro z hz
    apply Complex.differentiableAt_Gamma
    intro m h
    have hi := (hdisk hz).2
    rw [h] at hi
    norm_num at hi
  · intro z hz
    apply Complex.Gamma_ne_zero
    intro m h
    have hi := (hdisk hz).2
    rw [h] at hi
    norm_num at hi
  · intro z hz
    have hΓz : ‖Complex.Gamma z‖ ≤ B :=
      lemma44_norm_Gamma_le_rectangle (by linarith [(hdisk hz).1]) (hdisk hz).2
    have hΓs : ‖(Complex.Gamma s)⁻¹‖ ≤ B * Real.exp (Real.pi * |s.im|) :=
      lemma44_norm_Gamma_inv_le_rectangle (by linarith) (by linarith)
    have he : Real.exp (Real.pi * |s.im|) ≤ Real.exp (4 * Real.pi * (n : ℝ)) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    rw [div_eq_mul_inv, norm_mul]
    calc
      ‖Complex.Gamma z‖ * ‖(Complex.Gamma s)⁻¹‖ ≤ B * (B * Real.exp (Real.pi * |s.im|)) :=
        mul_le_mul hΓz hΓs (norm_nonneg _) (by positivity)
      _ ≤ H := by dsimp [H]; nlinarith

/-- The factorial estimate on a large disk is only logarithmic after division
by its radius. All constants here are explicit and independent of the point. -/
theorem lemma44_norm_logDeriv_Gamma_le_log_nat {s : ℂ} {n : ℕ}
    (hn : 1 ≤ n) (hre : |s.re| ≤ (n : ℝ))
    (hlo : 3 * (n : ℝ) ≤ |s.im|) (hhi : |s.im| ≤ 4 * (n : ℝ)) :
    ‖logDeriv Complex.Gamma s‖ ≤ 48 * Real.log (6 * (n : ℝ)) + 16 * Real.pi + 8 := by
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  let m : ℕ := 4 * n + 2
  have hm : (1 : ℝ) ≤ m := by dsimp [m]; push_cast; linarith
  have hmpos : (0 : ℝ) < m := by linarith
  have hp : 1 ≤ (m : ℝ) ^ m := one_le_pow₀ hm
  have hfac : (m.factorial : ℝ) ≤ (m : ℝ) ^ m := by
    exact_mod_cast Nat.factorial_le_pow m
  have hB : 0 < 1 + (m.factorial : ℝ) := by positivity
  have hlogB : Real.log (1 + (m.factorial : ℝ)) ≤
      Real.log 2 + (m : ℝ) * Real.log (m : ℝ) := by
    calc
      _ ≤ Real.log (2 * (m : ℝ) ^ m) := Real.log_le_log hB (by linarith)
      _ = _ := by rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  have hmle : (m : ℝ) ≤ 6 * (n : ℝ) := by dsimp [m]; push_cast; linarith
  have hlogm : Real.log (m : ℝ) ≤ Real.log (6 * (n : ℝ)) :=
    Real.log_le_log hmpos hmle
  have hlognonneg : 0 ≤ Real.log (6 * (n : ℝ)) := Real.log_nonneg (by linarith)
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hbudget : Real.log (1 + (m.factorial : ℝ)) ≤
      1 + 6 * (n : ℝ) * Real.log (6 * (n : ℝ)) := by
    apply hlogB.trans
    have hmul := mul_le_mul_of_nonneg_left hlogm hmpos.le
    have hmul' := mul_le_mul_of_nonneg_right hmle hlognonneg
    linarith
  have hbase := lemma44_norm_logDeriv_Gamma_le_factorial hn hre hlo hhi
  change ‖logDeriv Complex.Gamma s‖ ≤
    4 * Real.log ((1 + (m.factorial : ℝ)) ^ 2 * Real.exp (4 * Real.pi * (n : ℝ))) /
      (n : ℝ) at hbase
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_pow, Real.log_exp] at hbase
  norm_num at hbase
  apply hbase.trans
  apply (div_le_iff₀ hnpos).mpr
  nlinarith

/-- A uniform effective `O(log |Im s|)` bound, with no asymptotic Gamma input. -/
theorem lemma44_norm_logDeriv_Gamma_le_log_height {s : ℂ}
    (hheight : 12 ≤ |s.im|) (hre : |s.re| ≤ |s.im| / 4) :
    ‖logDeriv Complex.Gamma s‖ ≤ 48 * Real.log (3 * |s.im|) + 16 * Real.pi + 8 := by
  let n : ℕ := ⌈|s.im| / 4⌉₊
  have hle : |s.im| / 4 ≤ (n : ℝ) := Nat.le_ceil _
  have hlt : (n : ℝ) < |s.im| / 4 + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hnr : (1 : ℝ) ≤ n := by linarith
  have hn : 1 ≤ n := by exact_mod_cast hnr
  have hbase := lemma44_norm_logDeriv_Gamma_le_log_nat hn (hre.trans hle)
    (by linarith : 3 * (n : ℝ) ≤ |s.im|) (by linarith : |s.im| ≤ 4 * (n : ℝ))
  have hlog : Real.log (6 * (n : ℝ)) ≤ Real.log (3 * |s.im|) :=
    Real.log_le_log (by positivity) (by linarith)
  exact hbase.trans (by linarith)

end ZhangLS.Spec
