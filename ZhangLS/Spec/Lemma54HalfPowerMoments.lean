import ZhangLS.Spec.Lemma54MellinSecondMoment
import Mathlib.MeasureTheory.Integral.Gamma

/-! # Exact half-power exponential moments, including absolute convergence -/

namespace ZhangLS.Spec

open Complex MeasureTheory Set

set_option maxHeartbeats 1000000

theorem lemma54_half_power_after_square (B q : ℝ) {u : ℝ} (hu : 0 < u) :
    (|(2 : ℝ)| * u ^ ((2 : ℝ) - 1)) *
        ((u ^ (2 : ℝ)) ^ q * Real.exp (-((u ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) / B)) =
      2 * (u ^ (2 * q + 1) * Real.exp (-(1 / B) * u)) := by
  rw [← Real.rpow_mul hu.le, ← Real.rpow_mul hu.le]
  norm_num only [show |(2 : ℝ)| = 2 by norm_num, sub_self, Real.rpow_one, show (2 : ℝ) - 1 = 1 by norm_num,
    show (2 : ℝ) * (1 / 2) = 1 by norm_num]
  rw [Real.rpow_add hu, Real.rpow_one]
  have he : -u / B = -(1 / B) * u := by ring
  rw [he]
  ring

theorem lemma54_half_power_moment_integrable {B : ℝ} (hB : 0 < B)
    {q : ℝ} (hq : -1 < q) :
    IntegrableOn (fun x : ℝ => x ^ q * Real.exp (-(x ^ (1 / 2 : ℝ)) / B)) (Ioi 0) := by
  have hi : IntegrableOn (fun u : ℝ => 2 * (u ^ (2 * q + 1) * Real.exp (-(1 / B) * u)))
      (Ioi 0) :=
    (lemma53_rpow_laplace_integrable (a := 2 * q + 1) (by linarith)
      (by positivity : 0 < 1 / B)).const_mul 2
  apply (integrableOn_Ioi_comp_rpow_iff
    (fun x : ℝ => x ^ q * Real.exp (-(x ^ (1 / 2 : ℝ)) / B))
      (p := 2) (by norm_num)).mp
  apply hi.congr_fun _ measurableSet_Ioi
  intro u hu
  dsimp only
  rw [smul_eq_mul, lemma54_half_power_after_square B q hu]

theorem lemma54_half_power_moment_integral {B : ℝ} (hB : 0 < B)
    {q : ℝ} (hq : -1 < q) :
    (∫ x : ℝ in Ioi 0, x ^ q * Real.exp (-(x ^ (1 / 2 : ℝ)) / B)) =
      2 * B ^ (2 * (q + 1)) * Real.Gamma (2 * (q + 1)) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow
    (p := (1 / 2 : ℝ)) (q := q) (b := 1 / B) (by norm_num) hq (by positivity)
  have he : -(q + 1) / (1 / 2 : ℝ) = -(2 * (q + 1)) := by ring
  have hp : (1 / B) ^ (-(q + 1) / (1 / 2 : ℝ)) = B ^ (2 * (q + 1)) := by
    rw [he, one_div, Real.inv_rpow hB.le, ← Real.rpow_neg hB.le, neg_neg]
  have he' : (q + 1) / (1 / 2 : ℝ) = 2 * (q + 1) := by ring
  rw [hp, he'] at h
  norm_num only [one_div_div, div_one] at h
  have hf : (∫ x : ℝ in Ioi 0, x ^ q * Real.exp (-(x ^ (1 / 2 : ℝ)) / B)) =
      ∫ x : ℝ in Ioi 0, x ^ q * Real.exp (-(1 / B) * x ^ (1 / 2 : ℝ)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    congr 2
    ring
  rw [hf, h]
  ring

theorem lemma54_half_power_cubic_tail_integrable {B : ℝ} (hB : 0 < B) :
    IntegrableOn (fun x : ℝ => (1 + x ^ 3) * Real.exp (-(x ^ (1 / 2 : ℝ)) / B)) (Ioi 0) := by
  have h0 := lemma54_half_power_moment_integrable hB (q := 0) (by norm_num)
  have h3 := lemma54_half_power_moment_integrable hB (q := 3) (by norm_num)
  simp only [Real.rpow_zero, one_mul] at h0
  simp only [Real.rpow_ofNat] at h3
  have hh : IntegrableOn (fun x : ℝ => Real.exp (-(x ^ (1 / 2 : ℝ)) / B) +
      x ^ 3 * Real.exp (-(x ^ (1 / 2 : ℝ)) / B)) (Ioi 0) := h0.add h3
  simpa only [add_mul, one_mul] using hh

theorem lemma54_half_power_cubic_tail_integral {B : ℝ} (hB : 0 < B) :
    (∫ x : ℝ in Ioi 0, (1 + x ^ 3) * Real.exp (-(x ^ (1 / 2 : ℝ)) / B)) =
      2 * B ^ 2 + 10080 * B ^ 8 := by
  have h0 := lemma54_half_power_moment_integrable hB (q := 0) (by norm_num)
  have h3 := lemma54_half_power_moment_integrable hB (q := 3) (by norm_num)
  have h0eq := lemma54_half_power_moment_integral hB (q := 0) (by norm_num)
  have h3eq := lemma54_half_power_moment_integral hB (q := 3) (by norm_num)
  simp only [Real.rpow_zero, one_mul] at h0 h0eq
  simp only [Real.rpow_ofNat] at h3 h3eq
  simp_rw [add_mul, one_mul]
  rw [integral_add h0 h3, h0eq, h3eq]
  norm_num [Real.rpow_ofNat, Real.Gamma_ofNat_eq_factorial, Nat.factorial]
  ring

theorem lemma54_half_power_cubic_tail_integral_bound {B : ℝ} (hB : 1 ≤ B) :
    (∫ x : ℝ in Ioi 0, (1 + x ^ 3) * Real.exp (-(x ^ (1 / 2 : ℝ)) / B)) ≤ 10082 * B ^ 8 := by
  rw [lemma54_half_power_cubic_tail_integral (by linarith : 0 < B)]
  have hp : B ^ 2 ≤ B ^ 8 := pow_le_pow_right₀ hB (by norm_num)
  nlinarith only [hp]

end ZhangLS.Spec
