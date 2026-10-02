import ZhangLS.Spec.Lemma51GammaEuler
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # A quantitative digamma approximation in the right half-plane -/

namespace ZhangLS.Spec

open Complex Filter Set MeasureTheory
open scoped Topology

set_option maxHeartbeats 1000000

theorem lemma51_norm_horizontal_lower {z : ℂ} {x : ℝ}
    (hz : 0 ≤ z.re) :
    (x + |z.im|) / 2 ≤ ‖z + (x : ℂ)‖ := by
  have hr := Complex.re_le_norm (z + (x : ℂ))
  have hi := Complex.abs_im_le_norm (z + (x : ℂ))
  simp only [add_re, add_im, ofReal_re, ofReal_im, add_zero] at hr hi
  linarith

theorem lemma51_reciprocal_interval_error {z : ℂ} (hz : 0 ≤ z.re)
    (hy : 1 ≤ |z.im|) (k : ℕ) {x : ℝ} (hx : x ∈ Icc (k : ℝ) ((k : ℝ) + 1)) :
    ‖(z + (k : ℂ))⁻¹ - (z + (x : ℂ))⁻¹‖ ≤
      8 * (1 / ((k : ℝ) + |z.im|) - 1 / ((k : ℝ) + 1 + |z.im|)) := by
  let a : ℝ := (k : ℝ) + |z.im|
  have ha : 1 ≤ a := by dsimp [a]; linarith [Nat.cast_nonneg (α := ℝ) k]
  have hzne (r : ℝ) : z + (r : ℂ) ≠ 0 := by
    intro h
    have hh := congrArg Complex.im h
    simp at hh
    rw [hh, abs_zero] at hy
    norm_num at hy
  have hkn : a / 2 ≤ ‖z + (k : ℂ)‖ := by
    simpa [a] using lemma51_norm_horizontal_lower (x := (k : ℝ)) hz
  have hxn : a / 2 ≤ ‖z + (x : ℂ)‖ := by
    have ht := lemma51_norm_horizontal_lower (x := x) hz
    dsimp [a]
    linarith [hx.1]
  have hd : a ^ 2 / 4 ≤ ‖z + (k : ℂ)‖ * ‖z + (x : ℂ)‖ := by
    have hm := mul_le_mul hkn hxn (by linarith : 0 ≤ a / 2) (norm_nonneg _)
    nlinarith
  have hdp : 0 < ‖z + (k : ℂ)‖ * ‖z + (x : ℂ)‖ := by nlinarith
  have he : (z + (k : ℂ))⁻¹ - (z + (x : ℂ))⁻¹ =
      ((x - (k : ℝ) : ℝ) : ℂ) / ((z + (k : ℂ)) * (z + (x : ℂ))) := by
    push_cast
    have hkne : z + (k : ℂ) ≠ 0 := by
      simpa only [Complex.ofReal_natCast] using hzne (k : ℝ)
    field_simp [hzne x, hkne]
    ring
  rw [he, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hx.1)]
  have hb : (x - (k : ℝ)) / (‖z + (k : ℂ)‖ * ‖z + (x : ℂ)‖) ≤ 4 / a ^ 2 := by
    apply (div_le_iff₀ hdp).mpr
    have ht : 1 ≤ (4 / a ^ 2) * (‖z + (k : ℂ)‖ * ‖z + (x : ℂ)‖) := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ (by positivity : 0 < a ^ 2)).mpr
      nlinarith
    linarith [hx.2]
  apply hb.trans
  have hae : (k : ℝ) + 1 + |z.im| = a + 1 := by dsimp [a]; ring
  rw [hae]
  change 4 / a ^ 2 ≤ 8 * (1 / a - 1 / (a + 1))
  have hap : 0 < a := by linarith
  calc
    4 / a ^ 2 ≤ 8 / (a * (a + 1)) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith
    _ = 8 * (1 / a - 1 / (a + 1)) := by field_simp; ring

theorem lemma51_inverse_horizontal_integrable {z : ℂ} (hz : 0 < z.re)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun x : ℝ => (z + (x : ℂ))⁻¹) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.inv₀ (by fun_prop)
  intro x hx
  rw [uIcc_of_le hab] at hx
  intro h
  have hh := congrArg Complex.re h
  simp at hh
  linarith [hx.1]

theorem lemma51_log_horizontal_integral {z : ℂ} (hz : 0 < z.re)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ x : ℝ in a..b, (z + (x : ℂ))⁻¹) =
      Complex.log (z + (b : ℂ)) - Complex.log (z + (a : ℂ)) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _
    (lemma51_inverse_horizontal_integrable hz ha hab)
  intro x hx
  rw [uIcc_of_le hab] at hx
  have hp : z + (x : ℂ) ∈ Complex.slitPlane := by
    change 0 < (z + (x : ℂ)).re ∨ (z + (x : ℂ)).im ≠ 0
    left
    simp only [add_re, ofReal_re]
    linarith [hx.1]
  simpa [one_div] using (Complex.ofRealCLM.hasDerivAt.const_add z).clog_real hp

theorem lemma51_inverse_log_unit_error {z : ℂ} (hz : 0 < z.re)
    (hy : 1 ≤ |z.im|) (k : ℕ) :
    ‖(z + (k : ℂ))⁻¹ -
      (Complex.log (z + ((k : ℝ) + 1 : ℂ)) - Complex.log (z + (k : ℂ)))‖ ≤
      8 * (1 / ((k : ℝ) + |z.im|) - 1 / ((k : ℝ) + 1 + |z.im|)) := by
  have hab : (k : ℝ) ≤ (k : ℝ) + 1 := by linarith
  have hi := lemma51_inverse_horizontal_integrable hz (Nat.cast_nonneg (α := ℝ) k) hab
  have he : (z + (k : ℂ))⁻¹ -
      (Complex.log (z + ((k : ℝ) + 1 : ℂ)) - Complex.log (z + (k : ℂ))) =
      ∫ x : ℝ in (k : ℝ)..((k : ℝ) + 1), ((z + (k : ℂ))⁻¹ - (z + (x : ℂ))⁻¹) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hi,
      lemma51_log_horizontal_integral hz (Nat.cast_nonneg (α := ℝ) k) hab]
    simp
  rw [he]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (k : ℝ)) (b := (k : ℝ) + 1)
    (f := fun x : ℝ => (z + (k : ℂ))⁻¹ - (z + (x : ℂ))⁻¹)
    (fun x hx => lemma51_reciprocal_interval_error hz.le hy k
      (by simpa only [uIcc_of_le hab] using uIoc_subset_uIcc hx))
  simpa using hb

theorem lemma51_inverse_log_sum_error {z : ℂ} (hz : 0 < z.re)
    (hy : 1 ≤ |z.im|) (n : ℕ) :
    ‖(∑ k ∈ Finset.range n, (z + (k : ℂ))⁻¹) -
      (Complex.log (z + (n : ℂ)) - Complex.log z)‖ ≤
      8 * (1 / |z.im| - 1 / ((n : ℝ) + |z.im|)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hb := lemma51_inverse_log_unit_error hz hy n
    have he : (∑ k ∈ Finset.range (n + 1), (z + (k : ℂ))⁻¹) -
        (Complex.log (z + ((n + 1 : ℕ) : ℂ)) - Complex.log z) =
        ((∑ k ∈ Finset.range n, (z + (k : ℂ))⁻¹) -
          (Complex.log (z + (n : ℂ)) - Complex.log z)) +
        ((z + (n : ℂ))⁻¹ -
          (Complex.log (z + ((n : ℝ) + 1 : ℂ)) - Complex.log (z + (n : ℂ)))) := by
      rw [Finset.sum_range_succ]
      push_cast
      ring
    rw [he]
    apply (norm_add_le _ _).trans
    push_cast
    push_cast at hb
    linarith

theorem lemma51_log_add_nat_sub_log_tendsto {z : ℂ} (hz : 0 < z.re) :
    Tendsto (fun n : ℕ => Complex.log (z + (n : ℂ)) - (Real.log n : ℂ))
      atTop (𝓝 0) := by
  have hiR : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hiC : Tendsto (fun n : ℕ => (n : ℂ)⁻¹) atTop (𝓝 0) := by
    simpa [Function.comp_def] using Complex.continuous_ofReal.continuousAt.tendsto.comp hiR
  have hf : Tendsto (fun n : ℕ => 1 + z / (n : ℂ)) atTop (𝓝 1) := by
    simpa [div_eq_mul_inv] using tendsto_const_nhds.add (hiC.const_mul z)
  have h1 : (1 : ℂ) ∈ Complex.slitPlane := by
    change 0 < (1 : ℂ).re ∨ (1 : ℂ).im ≠ 0
    norm_num
  have hl : Tendsto (fun n : ℕ => Complex.log (1 + z / (n : ℂ))) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (Complex.hasDerivAt_log h1).continuousAt.tendsto.comp hf
  apply hl.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hzne : z + (n : ℂ) ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp at hh
    linarith
  have he : z + (n : ℂ) = (1 + z / (n : ℂ)) * (n : ℂ) := by
    field_simp
    ring
  have hpn : 1 + z / (n : ℂ) ≠ 0 := by
    intro h
    rw [he, h, zero_mul] at hzne
    exact hzne rfl
  rw [he]
  have hh := Complex.log_mul_ofReal (n : ℝ) hnR (1 + z / (n : ℂ)) hpn
  simp only [Complex.ofReal_natCast] at hh
  rw [hh]
  ring

theorem lemma51_Gamma_logDeriv_sub_log_bound {z : ℂ} (hz : 0 < z.re)
    (hy : 1 ≤ |z.im|) :
    ‖logDeriv Complex.Gamma z - Complex.log z‖ ≤ 8 / |z.im| := by
  have ht := (lemma51GammaLogDerivSeq_tendstoUniformlyOn
    (M := ‖z‖ + 2) (by positivity)).tendsto_at ⟨hz, by linarith⟩
  rw [← lemma51_Gamma_logDeriv_eq_Euler hz] at ht
  have hhR : Tendsto (fun n : ℕ =>
      (harmonic n : ℝ) - Real.log n - Real.eulerMascheroniConstant) atTop (𝓝 0) := by
    simpa using Real.tendsto_harmonic_sub_log.sub_const Real.eulerMascheroniConstant
  have hhC : Tendsto (fun n : ℕ =>
      ((((harmonic n : ℝ) - Real.log n - Real.eulerMascheroniConstant) : ℝ) : ℂ))
      atTop (𝓝 0) := by
    simpa [Function.comp_def] using Complex.continuous_ofReal.continuousAt.tendsto.comp hhR
  have hlim : Tendsto (fun n : ℕ =>
      (∑ k ∈ Finset.range n, (z + (k : ℂ))⁻¹) -
        (Complex.log (z + (n : ℂ)) - Complex.log z))
      atTop (𝓝 (-(logDeriv Complex.Gamma z - Complex.log z))) := by
    have hr := (hhC.sub (lemma51_log_add_nat_sub_log_tendsto hz)).sub ht |>.add_const
      (Complex.log z)
    convert hr using 1
    · ext n
      simp only [lemma51GammaLogDerivSeq, lemma51GammaEulerTerm, Finset.sum_sub_distrib]
      have hh : (harmonic n : ℂ) =
          ∑ k ∈ Finset.range n, ((k + 1 : ℕ) : ℂ)⁻¹ := by simp [harmonic]
      push_cast
      push_cast at hh
      rw [hh]
      ring
    · congr 1
      ring
  have hn := continuous_norm.continuousAt.tendsto.comp hlim
  have hb (n : ℕ) : ‖(∑ k ∈ Finset.range n, (z + (k : ℂ))⁻¹) -
      (Complex.log (z + (n : ℂ)) - Complex.log z)‖ ≤ 8 / |z.im| := by
    apply (lemma51_inverse_log_sum_error hz hy n).trans
    have hp : 0 ≤ 1 / ((n : ℝ) + |z.im|) := by positivity
    simpa only [one_div, div_eq_mul_inv, one_mul] using
      mul_le_mul_of_nonneg_left (sub_le_self (1 / |z.im|) hp) (by norm_num : (0 : ℝ) ≤ 8)
  have hfinal : ‖-(logDeriv Complex.Gamma z - Complex.log z)‖ ≤ 8 / |z.im| :=
    le_of_tendsto hn (Eventually.of_forall hb)
  rw [norm_neg] at hfinal
  exact hfinal

end ZhangLS.Spec
