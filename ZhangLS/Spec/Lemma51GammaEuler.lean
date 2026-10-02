import ZhangLS.Spec.Lemma44DirichletFactorEstimates
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.PSeries

/-! # Euler logarithms for the actual complex Gamma function

Finite logarithms have uniformly convergent derivatives on bounded
right-half-plane domains. Their exponentials converge to the actual Gamma
function via its proved Euler product limit.
-/

namespace ZhangLS.Spec

open Complex Filter Set
open scoped Topology

set_option maxHeartbeats 1000000

noncomputable def lemma51GammaEulerTerm (k : ℕ) (z : ℂ) : ℂ :=
  ((k + 1 : ℕ) : ℂ)⁻¹ - (z + (k : ℂ))⁻¹

noncomputable def lemma51GammaLogSeq (n : ℕ) (z : ℂ) : ℂ :=
  (z - 1) * (((harmonic n : ℝ) - Real.eulerMascheroniConstant : ℝ) : ℂ) -
    ∑ k ∈ Finset.range n, (Complex.log (z + (k : ℂ)) - Complex.log ((k + 1 : ℕ) : ℂ))

noncomputable def lemma51GammaLogDerivSeq (n : ℕ) (z : ℂ) : ℂ :=
  -(Real.eulerMascheroniConstant : ℂ) +
    ∑ k ∈ Finset.range n, lemma51GammaEulerTerm k z

noncomputable def lemma51GammaEuler (z : ℂ) : ℂ :=
  -(Real.eulerMascheroniConstant : ℂ) + ∑' k : ℕ, lemma51GammaEulerTerm k z

theorem lemma51GammaLogSeq_hasDerivAt (n : ℕ) {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt (lemma51GammaLogSeq n) (lemma51GammaLogDerivSeq n z) z := by
  have hd₁ := ((hasDerivAt_id z).sub_const (1 : ℂ)).mul_const
    ((((harmonic n : ℝ) - Real.eulerMascheroniConstant : ℝ) : ℂ))
  have hds : HasDerivAt
      (fun z : ℂ => ∑ k ∈ Finset.range n,
        (Complex.log (z + (k : ℂ)) - Complex.log ((k + 1 : ℕ) : ℂ)))
      (∑ k ∈ Finset.range n, (z + (k : ℂ))⁻¹) z := by
    apply HasDerivAt.fun_sum
    intro k hk
    have hp : z + (k : ℂ) ∈ Complex.slitPlane := by
      change 0 < (z + (k : ℂ)).re ∨ (z + (k : ℂ)).im ≠ 0
      left
      simp only [add_re, natCast_re]
      positivity
    simpa using ((Complex.hasDerivAt_log hp).comp z
      ((hasDerivAt_id z).add_const (k : ℂ))).sub_const (Complex.log ((k + 1 : ℕ) : ℂ))
  convert hd₁.sub hds using 1
  simp only [lemma51GammaLogDerivSeq, lemma51GammaEulerTerm, Finset.sum_sub_distrib]
  have hh : (harmonic n : ℂ) =
      ∑ k ∈ Finset.range n, ((k + 1 : ℕ) : ℂ)⁻¹ := by
    simp [harmonic]
  push_cast
  push_cast at hh
  rw [hh]
  ring

theorem lemma51GammaEulerTerm_bound {M : ℝ} {z : ℂ} {k : ℕ}
    (hM : 0 ≤ M) (hz : 0 ≤ z.re) (hnorm : ‖z‖ ≤ M) (hk : 1 ≤ k) :
    ‖lemma51GammaEulerTerm k z‖ ≤ (M + 1) / (k : ℝ) ^ 2 := by
  have hkp : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hzne : z + (k : ℂ) ≠ 0 := by
    intro he
    have hh := congrArg Complex.re he
    simp at hh
    linarith
  have hkne : ((k + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have he : lemma51GammaEulerTerm k z =
      (z - 1) / (((k + 1 : ℕ) : ℂ) * (z + (k : ℂ))) := by
    unfold lemma51GammaEulerTerm
    push_cast
    field_simp
    ring
  have hd : (k : ℝ) ≤ ‖z + (k : ℂ)‖ := by
    have hh := Complex.re_le_norm (z + (k : ℂ))
    simp at hh
    linarith
  have hden : 0 < ((k : ℝ) + 1) * ‖z + (k : ℂ)‖ := by positivity
  have hn : ‖z - 1‖ ≤ M + 1 := by
    have hh := norm_sub_le z 1
    norm_num at hh
    linarith
  rw [he, norm_div, norm_mul]
  have hkn : ‖((k + 1 : ℕ) : ℂ)‖ = (k : ℝ) + 1 := by
    rw [Complex.norm_natCast]
    simp
  rw [hkn]
  calc
    ‖z - 1‖ / (((k : ℝ) + 1) * ‖z + (k : ℂ)‖) ≤
        (M + 1) / (((k : ℝ) + 1) * ‖z + (k : ℂ)‖) :=
      div_le_div_of_nonneg_right hn hden.le
    _ ≤ (M + 1) / (k : ℝ) ^ 2 := by
      apply div_le_div_of_nonneg_left (by linarith) (by positivity)
      nlinarith

theorem lemma51GammaLogDerivSeq_tendstoUniformlyOn {M : ℝ} (hM : 0 ≤ M) :
    TendstoUniformlyOn lemma51GammaLogDerivSeq lemma51GammaEuler atTop
      {z : ℂ | 0 < z.re ∧ ‖z‖ < M} := by
  have hu : Summable (fun k : ℕ => (M + 1) / (k : ℝ) ^ 2) := by
    simpa [div_eq_mul_inv] using
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))).mul_left (M + 1)
  have ht := tendstoUniformlyOn_tsum_nat_eventually (f := lemma51GammaEulerTerm)
    (s := {z : ℂ | 0 < z.re ∧ ‖z‖ < M}) hu ?_
  · have hct : Tendsto (fun _ : ℕ => -(Real.eulerMascheroniConstant : ℂ))
        atTop (𝓝 (-(Real.eulerMascheroniConstant : ℂ))) := tendsto_const_nhds
    have hc := hct.tendstoUniformlyOn_const {z : ℂ | 0 < z.re ∧ ‖z‖ < M}
    exact hc.add ht
  · filter_upwards [eventually_ge_atTop 1] with k hk z hz
    exact lemma51GammaEulerTerm_bound hM hz.1.le hz.2.le hk

noncomputable def lemma51GammaLog (z : ℂ) : ℂ :=
  limUnder atTop (fun n : ℕ => lemma51GammaLogSeq n z)

theorem lemma51GammaLogSeq_one (n : ℕ) : lemma51GammaLogSeq n 1 = 0 := by
  simp [lemma51GammaLogSeq, Nat.cast_add, add_comm]

theorem lemma51GammaLogSeq_tendsto {z : ℂ} (hz : 0 < z.re) :
    Tendsto (fun n : ℕ => lemma51GammaLogSeq n z) atTop (𝓝 (lemma51GammaLog z)) := by
  let M : ℝ := ‖z‖ + 2
  let U : Set ℂ := {w | 0 < w.re ∧ ‖w‖ < M}
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hopen : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_norm continuous_const)
  have hconn : IsPreconnected U := by
    have hc : Convex ℝ {w : ℂ | 0 < w.re} :=
      convex_halfSpace_gt (.mk Complex.add_re Complex.smul_re) 0
    have hb : Convex ℝ {w : ℂ | ‖w‖ < M} := by
      simpa [Metric.ball, dist_eq_norm] using convex_ball (0 : ℂ) M
    exact (hc.inter hb).isPreconnected
  have hunif := lemma51GammaLogDerivSeq_tendstoUniformlyOn hM
  have huc := (ContinuousLinearMap.smulRightL ℂ ℂ ℂ 1).uniformContinuous
  have hcu := huc.comp_uniformCauchySeqOn hunif.uniformCauchySeqOn
  have hzU : z ∈ U := by dsimp [U, M]; exact ⟨hz, by linarith⟩
  have h1U : (1 : ℂ) ∈ U := by
    dsimp [U, M]
    norm_num
    linarith [norm_nonneg z]
  have hc0 : Cauchy (map (fun n : ℕ => lemma51GammaLogSeq n 1) atTop) := by
    simpa only [lemma51GammaLogSeq_one] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0)).cauchy_map
  have hcz := cauchy_map_of_uniformCauchySeqOn_fderiv hopen hconn hcu
    (fun n w hw => (lemma51GammaLogSeq_hasDerivAt n hw.1).hasFDerivAt) h1U hzU hc0
  exact CauchySeq.tendsto_limUnder hcz

theorem lemma51GammaLog_hasDerivAt {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt lemma51GammaLog (lemma51GammaEuler z) z := by
  let M : ℝ := ‖z‖ + 2
  apply hasDerivAt_of_tendstoUniformlyOn
    ((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_norm continuous_const))
    (lemma51GammaLogDerivSeq_tendstoUniformlyOn (M := M) (by dsimp [M]; positivity))
    (Eventually.of_forall (fun n w hw => lemma51GammaLogSeq_hasDerivAt n hw.1))
    (fun w hw => lemma51GammaLogSeq_tendsto hw.1)
  exact ⟨hz, by dsimp [M]; linarith⟩

theorem lemma51GammaLogSeq_exp (n : ℕ) {z : ℂ} (hz : 0 < z.re) :
    Complex.exp (lemma51GammaLogSeq n z) =
      Complex.exp ((z - 1) * ((((harmonic n : ℝ) - Real.eulerMascheroniConstant) : ℝ) : ℂ)) *
        (n.factorial : ℂ) / ∏ k ∈ Finset.range n, (z + (k : ℂ)) := by
  have hprod : Complex.exp (∑ k ∈ Finset.range n,
      (Complex.log (z + (k : ℂ)) - Complex.log ((k + 1 : ℕ) : ℂ))) =
      (∏ k ∈ Finset.range n, (z + (k : ℂ))) / (n.factorial : ℂ) := by
    rw [Complex.exp_sum]
    have he : ∀ k : ℕ, Complex.exp (Complex.log (z + (k : ℂ)) -
        Complex.log ((k + 1 : ℕ) : ℂ)) = (z + (k : ℂ)) / ((k + 1 : ℕ) : ℂ) := by
      intro k
      have hzk : z + (k : ℂ) ≠ 0 := by
        intro h
        have hh := congrArg Complex.re h
        simp at hh
        have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        linarith
      rw [Complex.exp_sub, Complex.exp_log hzk, Complex.exp_log]
      exact_mod_cast Nat.succ_ne_zero k
    simp_rw [he]
    rw [Finset.prod_div_distrib]
    congr 1
    rw [← Nat.cast_prod, Finset.prod_range_add_one_eq_factorial]
  rw [lemma51GammaLogSeq, Complex.exp_sub, hprod, div_div_eq_mul_div]

theorem lemma51GammaLogSeq_exp_eq_GammaSeq {n : ℕ} (hn : n ≠ 0)
    {z : ℂ} (hz : 0 < z.re) :
    Complex.exp (lemma51GammaLogSeq n z) = Complex.GammaSeq z n *
      ((z + (n : ℂ)) / (n : ℂ)) *
      Complex.exp ((z - 1) *
        ((((harmonic n : ℝ) - Real.log n - Real.eulerMascheroniConstant) : ℝ) : ℂ)) := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hzk : ∀ k : ℕ, z + (k : ℂ) ≠ 0 := by
    intro k h
    have hh := congrArg Complex.re h
    simp at hh
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hp : (∏ k ∈ Finset.range n, (z + (k : ℂ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun k _ => hzk k)
  have he :
      Complex.exp ((z - 1) * ((((harmonic n : ℝ) - Real.eulerMascheroniConstant) : ℝ) : ℂ)) *
        (n : ℂ) = (n : ℂ) ^ z * Complex.exp ((z - 1) *
          ((((harmonic n : ℝ) - Real.log n - Real.eulerMascheroniConstant) : ℝ) : ℂ)) := by
    conv_lhs => rw [← Complex.exp_log hnC]
    rw [Complex.cpow_def_of_ne_zero hnC, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    rw [← Complex.natCast_log]
    ring
  rw [lemma51GammaLogSeq_exp n hz, Complex.GammaSeq, Finset.prod_range_succ]
  field_simp [hnC, hp, hzk n]
  have he' := congrArg (fun w : ℂ => w * (n.factorial : ℂ)) he
  linear_combination he'

theorem lemma51GammaLog_exp {z : ℂ} (hz : 0 < z.re) :
    Complex.exp (lemma51GammaLog z) = Complex.Gamma z := by
  have hiR : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hiC : Tendsto (fun n : ℕ => (n : ℂ)⁻¹) atTop (𝓝 0) := by
    simpa [Function.comp_def] using Complex.continuous_ofReal.continuousAt.tendsto.comp hiR
  have heR : Tendsto (fun n : ℕ =>
      (harmonic n : ℝ) - Real.log n - Real.eulerMascheroniConstant) atTop (𝓝 0) := by
    simpa using Real.tendsto_harmonic_sub_log.sub_const Real.eulerMascheroniConstant
  have heC : Tendsto (fun n : ℕ =>
      ((((harmonic n : ℝ) - Real.log n - Real.eulerMascheroniConstant) : ℝ) : ℂ))
      atTop (𝓝 0) := by
    simpa [Function.comp_def] using Complex.continuous_ofReal.continuousAt.tendsto.comp heR
  have hf : Tendsto (fun n : ℕ => 1 + z / (n : ℂ)) atTop (𝓝 1) := by
    simpa [div_eq_mul_inv] using tendsto_const_nhds.add (hiC.const_mul z)
  have hlim := (Complex.GammaSeq_tendsto_Gamma z).mul hf |>.mul
    (Complex.continuous_exp.continuousAt.tendsto.comp (heC.const_mul (z - 1)))
  have hlim' : Tendsto (fun n : ℕ => Complex.exp (lemma51GammaLogSeq n z))
      atTop (𝓝 (Complex.Gamma z)) := by
    have hr : Tendsto (fun n : ℕ => Complex.GammaSeq z n * (1 + z / (n : ℂ)) *
        Complex.exp ((z - 1) *
          ((((harmonic n : ℝ) - Real.log n - Real.eulerMascheroniConstant) : ℝ) : ℂ)))
        atTop (𝓝 (Complex.Gamma z)) := by simpa using hlim
    apply hr.congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    rw [lemma51GammaLogSeq_exp_eq_GammaSeq hn hz]
    congr 2
    field_simp [show (n : ℂ) ≠ 0 by exact_mod_cast hn]
    ring
  exact tendsto_nhds_unique
    (Complex.continuous_exp.continuousAt.tendsto.comp (lemma51GammaLogSeq_tendsto hz)) hlim'

theorem lemma51_Gamma_logDeriv_eq_Euler {z : ℂ} (hz : 0 < z.re) :
    logDeriv Complex.Gamma z = lemma51GammaEuler z := by
  have hd := (lemma51GammaLog_hasDerivAt hz).cexp
  have he : (fun w : ℂ => Complex.exp (lemma51GammaLog w)) =ᶠ[𝓝 z] Complex.Gamma := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz] with w hw
    exact lemma51GammaLog_exp hw
  have hdG := hd.congr_of_eventuallyEq he.symm
  change deriv Complex.Gamma z / Complex.Gamma z = lemma51GammaEuler z
  rw [hdG.deriv, lemma51GammaLog_exp hz]
  exact mul_div_cancel_left₀ _ (lemma51GammaLog_exp hz ▸ Complex.exp_ne_zero _)

end ZhangLS.Spec
