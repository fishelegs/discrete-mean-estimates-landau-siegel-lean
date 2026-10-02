import ZhangLS.Spec.Lemma53Kernels
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # Gamma's Laplace integral for a complex decay parameter

The decay parameter ranges over the open right half-plane. Analyticity of
the actual integral follows by differentiation under an integrable local
majorant. The positive real formula then extends by the identity theorem.
-/

namespace ZhangLS.Spec

open Complex MeasureTheory Set Filter
open scoped Topology

set_option maxHeartbeats 1000000

noncomputable def lemma53GammaLaplaceKernel (s z : ℂ) (y : ℝ) : ℂ :=
  (y : ℂ) ^ (s - 1) * Complex.exp (-z * (y : ℂ))

noncomputable def lemma53GammaLaplace (s z : ℂ) : ℂ :=
  ∫ y : ℝ in Ioi 0, lemma53GammaLaplaceKernel s z y

theorem lemma53_gamma_laplace_kernel_norm (s z : ℂ) {y : ℝ} (hy : 0 < y) :
    ‖lemma53GammaLaplaceKernel s z y‖ =
      y ^ (s.re - 1) * Real.exp (-z.re * y) := by
  unfold lemma53GammaLaplaceKernel
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hy, norm_exp]
  simp [mul_re]

theorem lemma53_gamma_laplace_kernel_continuousOn (s z : ℂ) :
    ContinuousOn (lemma53GammaLaplaceKernel s z) (Ioi 0) := by
  unfold lemma53GammaLaplaceKernel
  apply ContinuousOn.mul
  · exact continuous_ofReal.continuousOn.cpow_const
      (fun y hy => ofReal_mem_slitPlane.mpr hy)
  · exact (by fun_prop : Continuous (fun y : ℝ => Complex.exp (-z * (y : ℂ)))).continuousOn

theorem lemma53_rpow_laplace_integrable {a b : ℝ} (ha : -1 < a) (hb : 0 < b) :
    IntegrableOn (fun y : ℝ => y ^ a * Real.exp (-b * y)) (Ioi 0) := by
  simpa only [Real.rpow_one] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) ha (by norm_num) hb)

theorem lemma53_gamma_laplace_integrable {s z : ℂ} (hs : 0 < s.re) (hz : 0 < z.re) :
    IntegrableOn (lemma53GammaLaplaceKernel s z) (Ioi 0) := by
  apply (lemma53_rpow_laplace_integrable (a := s.re - 1) (by linarith) hz).mono'
  · exact (lemma53_gamma_laplace_kernel_continuousOn s z).aestronglyMeasurable
      measurableSet_Ioi
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with y hy
    rw [lemma53_gamma_laplace_kernel_norm s z hy]

theorem lemma53_gamma_laplace_differentiableAt {s z : ℂ}
    (hs : 0 < s.re) (hz : 0 < z.re) :
    DifferentiableAt ℂ (lemma53GammaLaplace s) z := by
  let U : Set ℂ := {w | z.re / 2 < w.re}
  let F' : ℂ → ℝ → ℂ := fun w y => -(y : ℂ) * lemma53GammaLaplaceKernel s w y
  let bound : ℝ → ℝ := fun y => y ^ s.re * Real.exp (-(z.re / 2) * y)
  have hU : U ∈ 𝓝 z :=
    (isOpen_lt continuous_const continuous_re).mem_nhds (by dsimp [U]; linarith)
  have hmeas : ∀ᶠ w in 𝓝 z,
      AEStronglyMeasurable (lemma53GammaLaplaceKernel s w) (volume.restrict (Ioi 0)) :=
    Eventually.of_forall (fun w =>
      (lemma53_gamma_laplace_kernel_continuousOn s w).aestronglyMeasurable measurableSet_Ioi)
  have hderivmeas : AEStronglyMeasurable (F' z) (volume.restrict (Ioi 0)) := by
    exact (by fun_prop : Continuous (fun y : ℝ => -(y : ℂ))).aestronglyMeasurable.mul
      ((lemma53_gamma_laplace_kernel_continuousOn s z).aestronglyMeasurable measurableSet_Ioi)
  have hbound : ∀ᵐ y : ℝ ∂volume.restrict (Ioi 0), ∀ w ∈ U, ‖F' w y‖ ≤ bound y := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with y hy
    intro w hw
    dsimp [F', bound]
    rw [norm_mul, norm_neg, Complex.norm_of_nonneg hy.le,
      lemma53_gamma_laplace_kernel_norm s w hy]
    have hp : y * y ^ (s.re - 1) = y ^ s.re := by
      nth_rw 1 [← Real.rpow_one y]
      rw [← Real.rpow_add hy]
      congr 1
      ring
    rw [← mul_assoc, hp]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hy.le _)
    apply Real.exp_le_exp.mpr
    dsimp [U] at hw
    exact mul_le_mul_of_nonneg_right (neg_le_neg hw.le) (le_of_lt hy)
  have hdiff : ∀ᵐ y : ℝ ∂volume.restrict (Ioi 0), ∀ w ∈ U,
      HasDerivAt (fun w => lemma53GammaLaplaceKernel s w y) (F' w y) w := by
    filter_upwards [] with y
    intro w hw
    have h := (((hasDerivAt_id w).neg.mul_const (y : ℂ)).cexp).const_mul
      ((y : ℂ) ^ (s - 1))
    convert h using 1 <;> dsimp [F', lemma53GammaLaplaceKernel] <;> ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hU hmeas
    (lemma53_gamma_laplace_integrable hs hz) hderivmeas hbound
    (lemma53_rpow_laplace_integrable (a := s.re) (by linarith) (by linarith))
    hdiff).2.differentiableAt

theorem lemma53_gamma_laplace {s z : ℂ} (hs : 0 < s.re) (hz : 0 < z.re) :
    lemma53GammaLaplace s z = z ^ (-s) * Complex.Gamma s := by
  let U : Set ℂ := {w | 0 < w.re}
  let F : ℂ → ℂ := lemma53GammaLaplace s
  let G : ℂ → ℂ := fun w => w ^ (-s) * Complex.Gamma s
  have hF : AnalyticOnNhd ℂ F U := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_)
      (isOpen_lt continuous_const continuous_re)
    exact (lemma53_gamma_laplace_differentiableAt hs hw).differentiableWithinAt
  have hG : AnalyticOnNhd ℂ G U := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_)
      (isOpen_lt continuous_const continuous_re)
    exact ((differentiableAt_id.cpow_const (mem_slitPlane_iff.mpr (Or.inl hw))).mul_const
      (Complex.Gamma s)).differentiableWithinAt
  have hreal (r : ℝ) (hr : 0 < r) : F (r : ℂ) = G (r : ℂ) := by
    have h := Complex.integral_cpow_mul_exp_neg_mul_Ioi hs hr
    have hp : (1 / (r : ℂ)) ^ s = (r : ℂ) ^ (-s) := by
      rw [one_div, inv_cpow _ _ (by
        rw [arg_ofReal_of_nonneg hr.le]; exact Real.pi_ne_zero.symm), cpow_neg]
    dsimp [F, G, lemma53GammaLaplace, lemma53GammaLaplaceKernel]
    convert h.trans (congrArg (fun v : ℂ => v * Complex.Gamma s) hp) using 1
    congr 1
    funext y
    congr 2
    ring
  let seq : ℕ → ℂ := fun n => ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)
  have hseq : Tendsto seq atTop (𝓝 (1 : ℂ)) := by
    have ht : Tendsto (fun n : ℕ => 1 + 1 / ((n : ℝ) + 1)) atTop (𝓝 (1 : ℝ)) := by
      simpa using tendsto_const_nhds.add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    exact continuous_ofReal.continuousAt.tendsto.comp ht
  have hseqne : ∀ n, seq n ≠ 1 := by
    intro n hn
    have hh := congrArg Complex.re hn
    change 1 + 1 / ((n : ℝ) + 1) = 1 at hh
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have hwithin : Tendsto seq atTop (𝓝[≠] (1 : ℂ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hseq, Eventually.of_forall hseqne⟩
  have hfreq : ∃ᶠ w in 𝓝[≠] (1 : ℂ), F w = G w := by
    apply hwithin.frequently
    exact (Eventually.of_forall (fun n => hreal _ (by positivity))).frequently
  exact hF.eqOn_of_preconnected_of_frequently_eq hG
    (convex_halfSpace_re_gt 0).isPreconnected (by norm_num [U]) hfreq hz

end ZhangLS.Spec
