import ZhangLS.Spec.Lemma112Parameters
import ZhangLS.Spec.Lemma53Kernels

/-! # Fourier coefficient recovery for the original E₂ integral -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Real Topology

noncomputable def lemma112FourierGaussian (a q v : ℝ) : ℂ :=
  exp (-I * (q : ℂ) * (v : ℂ)) * (Real.exp (-(v ^ 2) / (4 * a ^ 2)) : ℂ)

lemma lemma112_fourier_gaussian_identity {a : ℝ} (ha : 0 < a) (q v : ℝ) :
    lemma112FourierGaussian a q v =
      exp ((-I * (q : ℂ)) * (v : ℂ) - ((1 / (2 * a) : ℝ) : ℂ) ^ 2 * (v : ℂ) ^ 2) := by
  unfold lemma112FourierGaussian
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  <;> ring

lemma lemma112_fourier_gaussian_integrable {a : ℝ} (ha : 0 < a) (q : ℝ) :
    Integrable (lemma112FourierGaussian a q) := by
  change Integrable (fun v : ℝ => lemma112FourierGaussian a q v)
  simp_rw [lemma112_fourier_gaussian_identity ha]
  exact lemma53_gaussian_laplace_integrable (by positivity) _

lemma lemma112_fourier_gaussian_integral {a : ℝ} (ha : 0 < a) (q : ℝ) :
    (∫ v : ℝ, lemma112FourierGaussian a q v) =
      ((2 * Real.sqrt Real.pi * a * Real.exp (-(a * q) ^ 2) : ℝ) : ℂ) := by
  simp_rw [lemma112_fourier_gaussian_identity ha]
  rw [lemma53_gaussian_laplace (by positivity)]
  have he : (-I * (q : ℂ)) ^ 2 / (4 * ((1 / (2 * a) : ℝ) : ℂ) ^ 2) =
      ((-((a * q) ^ 2) : ℝ) : ℂ) := by
    push_cast
    rw [mul_pow, neg_sq, I_sq]
    field_simp
    <;> ring
  rw [he, ← Complex.ofReal_exp]
  push_cast
  field_simp
  <;> ring

lemma lemma112_fourier_gaussian_norm (a q v : ℝ) :
    ‖lemma112FourierGaussian a q v‖ = Real.exp (-(v ^ 2) / (4 * a ^ 2)) := by
  unfold lemma112FourierGaussian
  rw [norm_mul, norm_exp, Complex.norm_of_nonneg (Real.exp_pos _).le]
  simp

/-- A generic Gaussian identity for the actual finite Dirichlet polynomial. -/
lemma lemma112_finite_polynomial_gaussian_integral (S : Finset ℕ) (c : ℕ → ℂ)
    (s : ℂ) {a : ℝ} (ha : 0 < a) :
    (∫ v : ℝ, (∑ n ∈ S, c n * exp (-(s + I * (v : ℂ)) * (Real.log (n : ℝ) : ℂ))) *
      (Real.exp (-(v ^ 2) / (4 * a ^ 2)) : ℂ)) =
    (2 * Real.sqrt Real.pi * a : ℝ) *
      ∑ n ∈ S, c n * exp (-s * (Real.log (n : ℝ) : ℂ)) *
        (Real.exp (-(a * Real.log (n : ℝ)) ^ 2) : ℂ) := by
  have he (n : ℕ) (v : ℝ) :
      c n * exp (-(s + I * (v : ℂ)) * (Real.log (n : ℝ) : ℂ)) *
          (Real.exp (-(v ^ 2) / (4 * a ^ 2)) : ℂ) =
        (c n * exp (-s * (Real.log (n : ℝ) : ℂ))) *
          lemma112FourierGaussian a (Real.log (n : ℝ)) v := by
    unfold lemma112FourierGaussian
    rw [show -(s + I * (v : ℂ)) * (Real.log (n : ℝ) : ℂ) =
      -s * (Real.log (n : ℝ) : ℂ) + -I * (Real.log (n : ℝ) : ℂ) * (v : ℂ) by ring,
      exp_add]
    ring
  simp_rw [Finset.sum_mul, he]
  rw [integral_finsetSum S (fun n hn =>
    (lemma112_fourier_gaussian_integrable ha (Real.log (n : ℝ))).const_mul
      (c n * exp (-s * (Real.log (n : ℝ) : ℂ))))]
  simp_rw [integral_const_mul, lemma112_fourier_gaussian_integral ha]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  push_cast
  ring

lemma lemma112_dirichlet_term_norm_le_one (c : ℕ → ℂ) {n : ℕ}
    (hn : 1 ≤ n) (hc : ‖c n‖ ≤ 1) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖c n * exp (-s * (Real.log (n : ℝ) : ℂ))‖ ≤ 1 := by
  rw [norm_mul, norm_exp]
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have he : (-s * (Real.log (n : ℝ) : ℂ)).re ≤ 0 := by
    simp only [mul_re, neg_re, ofReal_re, neg_im, ofReal_im, mul_zero, sub_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) hlog
  have hex : Real.exp (-s * (Real.log (n : ℝ) : ℂ)).re ≤ 1 := by
    simpa using Real.exp_le_exp.mpr he
  exact mul_le_one₀ hc (Real.exp_nonneg _) hex

lemma lemma112_finite_polynomial_norm_bound (S : Finset ℕ) (c : ℕ → ℂ)
    (hS : ∀ n ∈ S, 1 ≤ n) (hc : ∀ n ∈ S, ‖c n‖ ≤ 1)
    {s : ℂ} (hs : 0 ≤ s.re) :
    ‖∑ n ∈ S, c n * exp (-s * (Real.log (n : ℝ) : ℂ))‖ ≤ S.card := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _n ∈ S, (1 : ℝ) :=
      Finset.sum_le_sum (fun n hn => lemma112_dirichlet_term_norm_le_one c (hS n hn) (hc n hn) hs)
    _ = _ := by simp

lemma lemma112_finite_gaussian_recovery_bound (S : Finset ℕ) (c : ℕ → ℂ)
    (hS : ∀ n ∈ S, 1 ≤ n) (h1 : 1 ∈ S) (hc1 : c 1 = 1)
    (hc : ∀ n ∈ S, ‖c n‖ ≤ 1) {s : ℂ} (hs : 0 ≤ s.re)
    {a : ℝ} (ha : 0 < a) :
    ‖(∑ n ∈ S, c n * exp (-s * (Real.log (n : ℝ) : ℂ)) *
        (Real.exp (-(a * Real.log (n : ℝ)) ^ 2) : ℂ)) - 1‖ ≤
      S.card * Real.exp (-(a ^ 2) / 4) := by
  let f : ℕ → ℂ := fun n => c n * exp (-s * (Real.log (n : ℝ) : ℂ)) *
    (Real.exp (-(a * Real.log (n : ℝ)) ^ 2) : ℂ)
  have hf1 : f 1 = 1 := by simp [f, hc1]
  have he : (∑ n ∈ S, f n) - 1 = ∑ n ∈ S.erase 1, f n := by
    rw [← Finset.sum_erase_add S f h1, hf1]
    ring
  change ‖(∑ n ∈ S, f n) - 1‖ ≤ _
  rw [he]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _n ∈ S.erase 1, Real.exp (-(a ^ 2) / 4) := by
      apply Finset.sum_le_sum
      intro n hn
      have hm := (Finset.mem_erase.mp hn).2
      have hn2 : 2 ≤ n := by have := hS n hm; have := (Finset.mem_erase.mp hn).1; omega
      have hlog : (1 / 2 : ℝ) ≤ Real.log (n : ℝ) := by
        have ht : Real.log 2 ≤ Real.log (n : ℝ) :=
          Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast hn2)
        linarith [Real.log_two_gt_d9]
      have hb := lemma112_dirichlet_term_norm_le_one c (hS n hm) (hc n hm) hs
      dsimp only [f]
      rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le]
      apply (mul_le_mul_of_nonneg_right hb (Real.exp_nonneg _)).trans
      rw [one_mul]
      apply Real.exp_le_exp.mpr
      have hsq : (1 / 4 : ℝ) ≤ Real.log (n : ℝ) ^ 2 := by nlinarith only [hlog]
      have hp := mul_le_mul_of_nonneg_left hsq (sq_nonneg a)
      nlinarith only [hp]
    _ = (S.erase 1).card * Real.exp (-(a ^ 2) / 4) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_erase_le (s := S) (a := 1))
      (Real.exp_nonneg _)

lemma lemma112_finite_polynomial_gaussian_integrable (S : Finset ℕ) (c : ℕ → ℂ)
    (s : ℂ) {a : ℝ} (ha : 0 < a) :
    Integrable (fun v : ℝ =>
      (∑ n ∈ S, c n * exp (-(s + I * (v : ℂ)) * (Real.log (n : ℝ) : ℂ))) *
        (Real.exp (-(v ^ 2) / (4 * a ^ 2)) : ℂ)) := by
  have he (v : ℝ) :
      (∑ n ∈ S, c n * exp (-(s + I * (v : ℂ)) * (Real.log (n : ℝ) : ℂ))) *
          (Real.exp (-(v ^ 2) / (4 * a ^ 2)) : ℂ) =
      ∑ n ∈ S, (c n * exp (-s * (Real.log (n : ℝ) : ℂ))) *
        lemma112FourierGaussian a (Real.log (n : ℝ)) v := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n hn
    unfold lemma112FourierGaussian
    rw [show -(s + I * (v : ℂ)) * (Real.log (n : ℝ) : ℂ) =
      -s * (Real.log (n : ℝ) : ℂ) + -I * (Real.log (n : ℝ) : ℂ) * (v : ℂ) by ring,
      exp_add]
    ring
  simp_rw [he]
  exact integrable_finsetSum S fun n hn =>
    (lemma112_fourier_gaussian_integrable ha (Real.log (n : ℝ))).const_mul _

/-- Lower bound before the paper-specific elementary exponential budgets. -/
lemma lemma112_truncated_gaussian_norm_lower (S : Finset ℕ) (c : ℕ → ℂ)
    (hS : ∀ n ∈ S, 1 ≤ n) (h1 : 1 ∈ S) (hc1 : c 1 = 1)
    (hc : ∀ n ∈ S, ‖c n‖ ≤ 1) {s : ℂ} (hs : 0 ≤ s.re)
    {a T : ℝ} (ha : 0 < a) (hT : 0 < T) :
    2 * Real.sqrt Real.pi * a * (1 - S.card * Real.exp (-(a ^ 2) / 4)) -
        8 * S.card * a ^ 2 / T * Real.exp (-(T ^ 2) / (4 * a ^ 2)) ≤
      ∫ v in -T..T,
        ‖∑ n ∈ S, c n * exp (-(s + I * (v : ℂ)) * (Real.log (n : ℝ) : ℂ))‖ *
          Real.exp (-(v ^ 2) / (4 * a ^ 2)) := by
  let f : ℝ → ℂ := fun v =>
    (∑ n ∈ S, c n * exp (-(s + I * (v : ℂ)) * (Real.log (n : ℝ) : ℂ))) *
      (Real.exp (-(v ^ 2) / (4 * a ^ 2)) : ℂ)
  have hb (v : ℝ) : ‖f v‖ ≤ S.card * Real.exp (-(1 / (4 * a ^ 2)) * v ^ 2) := by
    dsimp only [f]
    rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le]
    have hn := lemma112_finite_polynomial_norm_bound S c hS hc
      (s := s + I * (v : ℂ)) (by simpa using hs)
    convert mul_le_mul_of_nonneg_right hn (Real.exp_nonneg (-(v ^ 2) / (4 * a ^ 2))) using 1 <;> congr 1 <;> ring
  have ht := lemma44_gaussian_integral_truncation f
    (lemma112_finite_polynomial_gaussian_integrable S c s ha)
    (by positivity : (0 : ℝ) ≤ S.card) (by positivity : 0 < 1 / (4 * a ^ 2)) hT hb
  have hi := lemma112_finite_polynomial_gaussian_integral S c s ha
  have hr := lemma112_finite_gaussian_recovery_bound S c hS h1 hc1 hc hs ha
  have hmass : 0 ≤ 2 * Real.sqrt Real.pi * a := by positivity
  have hdist : ‖(∫ v : ℝ, f v) - (2 * Real.sqrt Real.pi * a : ℝ)‖ ≤
      (2 * Real.sqrt Real.pi * a) * (S.card * Real.exp (-(a ^ 2) / 4)) := by
    change ‖(∫ v : ℝ, _) - _‖ ≤ _
    rw [hi, ← mul_sub_one, norm_mul, Complex.norm_of_nonneg hmass]
    exact mul_le_mul_of_nonneg_left hr hmass
  have hn : ‖((2 * Real.sqrt Real.pi * a : ℝ) : ℂ)‖ ≤
      ‖(∫ v : ℝ, f v) - (2 * Real.sqrt Real.pi * a : ℝ)‖ +
        ‖(∫ v : ℝ, f v) - (∫ v in -T..T, f v)‖ + ‖∫ v in -T..T, f v‖ := by
    calc
      _ = ‖(((2 * Real.sqrt Real.pi * a : ℝ) : ℂ) - (∫ v : ℝ, f v)) +
          ((∫ v : ℝ, f v) - (∫ v in -T..T, f v)) + (∫ v in -T..T, f v)‖ := by
        congr 1
        ring
      _ ≤ _ := by simpa only [norm_sub_rev] using
        (norm_add₃_le (a := (((2 * Real.sqrt Real.pi * a : ℝ) : ℂ) - (∫ v : ℝ, f v)))
          (b := ((∫ v : ℝ, f v) - (∫ v in -T..T, f v))) (c := (∫ v in -T..T, f v)))
  have hnorm := intervalIntegral.norm_integral_le_integral_norm (f := f) (μ := volume) (by linarith : -T ≤ T)
  have he : (∫ v in -T..T, ‖f v‖) =
      ∫ v in -T..T,
        ‖∑ n ∈ S, c n * exp (-(s + I * (v : ℂ)) * (Real.log (n : ℝ) : ℂ))‖ *
          Real.exp (-(v ^ 2) / (4 * a ^ 2)) := by
    apply intervalIntegral.integral_congr
    intro v hv
    simp only [f, norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le]
  rw [he] at hnorm
  rw [Complex.norm_of_nonneg hmass] at hn
  have htail : 2 * S.card * Real.exp (-(1 / (4 * a ^ 2)) * T ^ 2) /
      ((1 / (4 * a ^ 2)) * T) = 8 * S.card * a ^ 2 / T * Real.exp (-(T ^ 2) / (4 * a ^ 2)) := by
    rw [show -(1 / (4 * a ^ 2)) * T ^ 2 = -(T ^ 2) / (4 * a ^ 2) by ring]
    field_simp
    <;> ring
  rw [htail] at ht
  linarith only [hdist, ht, hn, hnorm]

end ZhangLS.Spec
