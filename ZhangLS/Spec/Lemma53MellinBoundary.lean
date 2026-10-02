import ZhangLS.Spec.Lemma53ExponentialSubstitution
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Removing the positive real decay by dominated convergence -/

namespace ZhangLS.Spec

open Complex MeasureTheory Set Filter
open scoped Topology

set_option maxHeartbeats 1000000

theorem lemma53_omega_exponential_integrable {D : ℕ} (hD : 1 < D) (q : ℝ) :
    Integrable (fun t : ℝ => Real.exp (q * t) *
      ‖lemma53PaperOmega D (lemma53MellinLine t)‖) := by
  let B := lemma53PaperScale D
  let T := (lemma23PaperCenter D).im
  let b : ℝ := -(4 * B ^ 2)⁻¹
  let c : ℝ := q + 2 * T / (4 * B ^ 2)
  let d : ℝ := (1 - T ^ 2) / (4 * B ^ 2)
  have hB : 0 < B := lemma53_scale_pos hD
  have hb : (b : ℂ).re < 0 := by
    change -(4 * B ^ 2)⁻¹ < 0
    exact neg_lt_zero.mpr (inv_pos.mpr (by positivity))
  have hg := (integrable_cexp_quadratic' hb (c : ℂ) (d : ℂ)).norm.const_mul
    (Real.sqrt Real.pi / B)
  have he (t : ℝ) : Real.exp (q * t) *
      ‖lemma53PaperOmega D (lemma53MellinLine t)‖ =
      (Real.sqrt Real.pi / B) *
        ‖Complex.exp ((b : ℂ) * (t : ℂ) ^ 2 + (c : ℂ) * t + d)‖ := by
    have hω := lemma53_omega_norm_vertical hD (3 / 2) t
    norm_num only [ofReal_div, ofReal_ofNat] at hω
    rw [lemma53MellinLine, hω, norm_exp]
    rw [mul_left_comm, ← Real.exp_add]
    congr 2
    simp only [← ofReal_pow, mul_re, add_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    dsimp [b, c, d, B, T]
    ring
  simpa only [← he] using hg

noncomputable def lemma53BoundaryMajorant (D : ℕ) (A t : ℝ) : ℝ :=
  (2 * Real.exp (-(3 / 2 : ℝ) * Real.log A)) *
    ((Real.exp (Real.pi * t) + Real.exp (-Real.pi * t)) *
      ‖lemma53PaperOmega D (lemma53MellinLine t)‖)

theorem lemma53_boundary_majorant_integrable {D : ℕ} (hD : 1 < D) (A : ℝ) :
    Integrable (lemma53BoundaryMajorant D A) := by
  have h := ((lemma53_omega_exponential_integrable hD Real.pi).add
    (lemma53_omega_exponential_integrable hD (-Real.pi))).const_mul
      (2 * Real.exp (-(3 / 2 : ℝ) * Real.log A))
  unfold lemma53BoundaryMajorant
  simpa only [Pi.add_apply, add_mul] using h

theorem lemma53_cpow_vertical_bound {A : ℝ} (hA : 0 < A) {z : ℂ}
    (hz : A ≤ ‖z‖) (t : ℝ) :
    ‖z ^ (-lemma53MellinLine t)‖ ≤
      Real.exp (-(3 / 2 : ℝ) * Real.log A) *
        (Real.exp (Real.pi * t) + Real.exp (-Real.pi * t)) := by
  have hzne : z ≠ 0 := norm_pos_iff.mp (hA.trans_le hz)
  rw [cpow_def_of_ne_zero hzne, norm_exp]
  have hre : (Complex.log z * (-lemma53MellinLine t)).re =
      -(3 / 2 : ℝ) * Real.log ‖z‖ + t * z.arg := by
    simp [lemma53MellinLine, mul_re, log_re, log_im]
    ring
  rw [hre]
  have hlog : Real.log A ≤ Real.log ‖z‖ := Real.log_le_log hA hz
  have harg : t * z.arg ≤ Real.pi * |t| := by
    calc
      _ ≤ |t * z.arg| := le_abs_self _
      _ = |t| * |z.arg| := abs_mul _ _
      _ ≤ Real.pi * |t| := by
        simpa only [mul_comm] using
          mul_le_mul_of_nonneg_left (abs_arg_le_pi z) (abs_nonneg t)
  have he : Real.exp (-(3 / 2 : ℝ) * Real.log ‖z‖ + t * z.arg) ≤
      Real.exp (-(3 / 2 : ℝ) * Real.log A + Real.pi * |t|) := by
    apply Real.exp_le_exp.mpr
    linarith
  refine he.trans ?_
  rw [Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
    exact le_add_of_nonneg_right (Real.exp_pos _).le
  · rw [abs_of_neg (lt_of_not_ge ht), mul_neg, neg_mul]
    exact le_add_of_nonneg_left (Real.exp_pos _).le

theorem lemma53_regularized_integrand_bound {D : ℕ}
    {A : ℝ} (hA : 0 < A) {z : ℂ} (hz : A ≤ ‖z‖) (t : ℝ) :
    ‖z ^ (-lemma53MellinLine t) * Complex.Gamma (lemma53MellinLine t) *
      lemma53PaperOmega D (lemma53MellinLine t)‖ ≤ lemma53BoundaryMajorant D A t := by
  have hg : ‖Complex.Gamma (lemma53MellinLine t)‖ ≤ 2 := by
    convert
      (lemma44_norm_Gamma_le_factorial (z := lemma53MellinLine t) (m := 1)
        (by norm_num [lemma53MellinLine]) (by norm_num [lemma53MellinLine])) using 1 <;> norm_num
  rw [norm_mul, norm_mul]
  unfold lemma53BoundaryMajorant
  calc
    _ ≤ (Real.exp (-(3 / 2 : ℝ) * Real.log A) *
        (Real.exp (Real.pi * t) + Real.exp (-Real.pi * t))) * 2 *
        ‖lemma53PaperOmega D (lemma53MellinLine t)‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (lemma53_cpow_vertical_bound hA hz t) hg (norm_nonneg _)
          (by positivity)) (norm_nonneg _)
    _ = _ := by ring

theorem lemma53_regularized_integrand_continuous {D : ℕ} {z : ℂ} (hz : z ≠ 0) :
    Continuous (fun t : ℝ => z ^ (-lemma53MellinLine t) *
      Complex.Gamma (lemma53MellinLine t) * lemma53PaperOmega D (lemma53MellinLine t)) := by
  have hΓ : Continuous (fun t : ℝ => Complex.Gamma (lemma53MellinLine t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (Complex.differentiableAt_Gamma _ (by
      intro n hn
      have hh := congrArg Complex.re hn
      norm_num [lemma53MellinLine] at hh
      nlinarith)).continuousAt.comp (by unfold lemma53MellinLine; fun_prop)
  have hp : Continuous (fun t : ℝ => z ^ (-lemma53MellinLine t)) :=
    (by unfold lemma53MellinLine; fun_prop : Continuous (fun t : ℝ => -lemma53MellinLine t)).const_cpow
      (Or.inl hz)
  exact (hp.mul hΓ).mul (by unfold lemma53PaperOmega lemma53MellinLine; fun_prop)

noncomputable def lemma53DecaySequence (A : ℝ) (n : ℕ) : ℂ :=
  ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) + (A : ℂ) * I

theorem lemma53_decay_sequence_tendsto (A : ℝ) :
    Tendsto (lemma53DecaySequence A) atTop (𝓝 ((A : ℂ) * I)) := by
  have h : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝 (0 : ℂ)) :=
    continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  simpa only [lemma53DecaySequence, zero_add] using h.add_const ((A : ℂ) * I)

theorem lemma53_decay_sequence_re_pos (A : ℝ) (n : ℕ) :
    0 < (lemma53DecaySequence A n).re := by
  simp only [lemma53DecaySequence, add_re, mul_re, ofReal_re, ofReal_im,
    I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero]
  positivity

theorem lemma53_decay_sequence_norm {A : ℝ} (hA : 0 < A) (n : ℕ) :
    A ≤ ‖lemma53DecaySequence A n‖ := by
  simpa [lemma53DecaySequence, abs_of_pos hA] using abs_im_le_norm (lemma53DecaySequence A n)

theorem lemma53_mellin_boundary_limit {D : ℕ} (hD : 1 < D) {A : ℝ} (hA : 0 < A) :
    Tendsto (fun n => lemma53RegularizedMellin D (lemma53DecaySequence A n)) atTop
      (𝓝 (lemma53RegularizedMellin D ((A : ℂ) * I))) := by
  have ht := tendsto_integral_of_dominated_convergence (lemma53BoundaryMajorant D A)
    (fun n => (lemma53_regularized_integrand_continuous
      (norm_pos_iff.mp (hA.trans_le (lemma53_decay_sequence_norm hA n)))).aestronglyMeasurable)
    (lemma53_boundary_majorant_integrable hD A)
    (fun n => Eventually.of_forall (fun t =>
      lemma53_regularized_integrand_bound hA (lemma53_decay_sequence_norm hA n) t))
    (Eventually.of_forall (fun t =>
      (((lemma53_decay_sequence_tendsto A).cpow tendsto_const_nhds
        (mem_slitPlane_iff.mpr (Or.inr (by simp [hA.ne'])))).mul_const
          (Complex.Gamma (lemma53MellinLine t))).mul_const
            (lemma53PaperOmega D (lemma53MellinLine t))))
  exact ht.const_mul ((1 / (2 * Real.pi) : ℝ) : ℂ)

theorem lemma53_exponential_boundary_limit {D : ℕ} (hD : 1 < D) (A : ℝ) :
    Tendsto (fun n => ∫ u : ℝ, lemma53ExponentialKernel D (lemma53DecaySequence A n) u)
      atTop (𝓝 (∫ u : ℝ, lemma53ExponentialKernel D ((A : ℂ) * I) u)) := by
  let bound : ℝ → ℝ := fun u => Real.exp (u / 2 - lemma53PaperScale D ^ 2 * u ^ 2)
  have hb : Integrable bound := by
    have hg := (lemma53_gaussian_laplace_integrable (lemma53_scale_pos hD) (1 / 2)).norm
    convert hg using 1
    funext u
    rw [norm_exp]
    dsimp [bound]
    congr 1
    simp only [← ofReal_pow, sub_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    norm_num
    ring
  apply tendsto_integral_of_dominated_convergence bound
    (fun n => (by unfold lemma53ExponentialKernel; fun_prop :
      Continuous (lemma53ExponentialKernel D (lemma53DecaySequence A n))).aestronglyMeasurable) hb
  · intro n
    filter_upwards [] with u
    rw [lemma53_exponential_kernel_norm]
    apply Real.exp_le_exp.mpr
    have hh := mul_nonneg (lemma53_decay_sequence_re_pos A n).le (Real.exp_pos u).le
    linarith
  · filter_upwards [] with u
    have hc : Continuous (fun z : ℂ => lemma53ExponentialKernel D z u) := by
      unfold lemma53ExponentialKernel
      fun_prop
    exact hc.continuousAt.tendsto.comp (lemma53_decay_sequence_tendsto A)

theorem lemma53_boundary_mellin_exponential {D : ℕ} (hD : 1 < D) {A : ℝ} (hA : 0 < A) :
    lemma53RegularizedMellin D ((A : ℂ) * I) =
      ∫ u : ℝ, lemma53ExponentialKernel D ((A : ℂ) * I) u := by
  have hm := lemma53_mellin_boundary_limit hD hA
  have he : (fun n => lemma53RegularizedMellin D (lemma53DecaySequence A n)) =
      (fun n => ∫ u : ℝ, lemma53ExponentialKernel D (lemma53DecaySequence A n) u) :=
    funext (fun n => lemma53_regularized_mellin_exponential hD (lemma53_decay_sequence_re_pos A n))
  rw [he] at hm
  exact tendsto_nhds_unique hm (lemma53_exponential_boundary_limit hD A)

end ZhangLS.Spec
