import ZhangLS.Spec.Lemma23AnalyticLogBranch
import ZhangLS.Spec.Lemma23ArithmeticCoefficients
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# A conditional logarithmic-derivative bound for Lemma 2.3

If a function is holomorphic and zero-free on a disk and its normalized modulus is bounded,
then Borel--Carathéodory followed by Cauchy's estimate bounds its logarithmic derivative at the
center.  The zero-free disk and the modulus bound are hypotheses here; obtaining them for Zhang's
actual finite Dirichlet polynomial is part of the remaining Section 4 work.
-/

namespace ZhangLS.Spec

open Set
open scoped Topology

/-- A normalized modulus bound on a zero-free disk gives a logarithmic-derivative estimate at
its center.  The constant `4` comes from applying Borel--Carathéodory on radius `R` and Cauchy's
estimate on the concentric radius `R / 2` disk. -/
theorem lemma23_norm_logDeriv_le_of_norm_ratio_bound
    {f : ℂ → ℂ} {R H : ℝ}
    (hR : 0 < R) (hH : 1 < H)
    (hfdif : ∀ z ∈ Metric.ball (0 : ℂ) R, DifferentiableAt ℂ f z)
    (hfne : ∀ z ∈ Metric.ball (0 : ℂ) R, f z ≠ 0)
    (hNorm : ∀ z ∈ Metric.ball (0 : ℂ) R, ‖f z / f 0‖ ≤ H) :
    ‖logDeriv f 0‖ ≤ 4 * Real.log H / R := by
  let U : Set ℂ := Metric.ball (0 : ℂ) R
  let q : ℂ → ℂ := fun z => f z / f 0
  have h0U : (0 : ℂ) ∈ U := by
    exact Metric.mem_ball_self hR
  have hq0 : q 0 = 1 := by
    simp [q, hfne 0 h0U]
  have hqne : ∀ z ∈ U, q z ≠ 0 := by
    intro z hz
    exact div_ne_zero (hfne z hz) (hfne 0 h0U)
  have hqdif : ∀ z ∈ U, DifferentiableAt ℂ q z := by
    intro z hz
    exact (hfdif z hz).div_const (f 0)
  have hqcont : ContinuousOn q U := by
    exact fun z hz => (hqdif z hz).continuousAt.continuousWithinAt
  have hUopen : IsOpen U := by
    exact Metric.isOpen_ball
  have hUsc : IsSimplyConnected U := by
    letI : ContractibleSpace U :=
      (convex_ball (0 : ℂ) R).contractibleSpace ⟨0, h0U⟩
    change SimplyConnectedSpace U
    exact inferInstance
  obtain ⟨ℓ₀, hℓ₀cont, hℓ₀lift, hℓ₀deriv⟩ :=
    lemma23_exists_analytic_log_branch hUsc hUopen hqcont hqne hqdif
  let ℓ : ℂ → ℂ := fun z => ℓ₀ z - ℓ₀ 0
  have hℓcont : ContinuousOn ℓ U := by
    exact hℓ₀cont.sub continuousOn_const
  have hℓlift : ∀ z ∈ U, Complex.exp (ℓ z) = q z := by
    intro z hz
    change Complex.exp (ℓ₀ z - ℓ₀ 0) = q z
    rw [Complex.exp_sub, hℓ₀lift z hz, hℓ₀lift 0 h0U, hq0]
    simp
  have hℓ0 : ℓ 0 = 0 := by
    simp [ℓ]
  have hℓdiff : DifferentiableOn ℂ ℓ U := by
    intro z hz
    exact (lemma23_hasDerivAt_of_continuous_exp_lift hUopen hz hℓcont hℓlift
      (hqdif z hz).hasDerivAt (hqne z hz)).differentiableAt.differentiableWithinAt
  have hRe : Set.MapsTo ℓ U {z : ℂ | z.re ≤ Real.log H} := by
    intro z hz
    change (ℓ z).re ≤ Real.log H
    have hexp_le : Real.exp (ℓ z).re ≤ H := by
      have hnorm : ‖q z‖ ≤ H := by simpa [q] using hNorm z hz
      rw [← hℓlift z hz, Complex.norm_exp] at hnorm
      exact hnorm
    exact (Real.le_log_iff_exp_le (by linarith : 0 < H)).2 hexp_le
  have hM : 0 < Real.log H := Real.log_pos hH
  have hBC {z : ℂ} (hz : z ∈ U) :
      ‖ℓ z‖ ≤ 2 * Real.log H * ‖z‖ / (R - ‖z‖) := by
    exact Complex.borelCaratheodory_zero hM hℓdiff hRe hR hz hℓ0
  have hr : 0 < R / 2 := by linarith
  have hrR : R / 2 < R := by linarith
  have hclosure : closure (Metric.ball (0 : ℂ) (R / 2)) ⊆ U := by
    intro z hz
    exact Metric.closedBall_subset_ball hrR (Metric.closure_ball_subset_closedBall hz)
  have hℓdcc : DiffContOnCl ℂ ℓ (Metric.ball (0 : ℂ) (R / 2)) :=
    (hℓdiff.mono hclosure).diffContOnCl
  have hbound (z : ℂ) (hz : z ∈ Metric.sphere (0 : ℂ) (R / 2)) :
      ‖ℓ z‖ ≤ 2 * Real.log H := by
    have hnorm : ‖z‖ = R / 2 := by
      simpa [Metric.mem_sphere, dist_zero_right] using hz
    have hzU : z ∈ U := by
      rw [Metric.mem_ball, dist_zero_right]
      rw [hnorm]
      exact hrR
    have hb := hBC hzU
    rw [hnorm] at hb
    calc
      ‖ℓ z‖ ≤ 2 * Real.log H * (R / 2) / (R - R / 2) := hb
      _ = 2 * Real.log H := by
        have hden : R - R / 2 = R / 2 := by ring
        rw [hden]
        field_simp
  have hCauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (c := (0 : ℂ)) (R := R / 2) (C := 2 * Real.log H) (f := ℓ)
    hr hℓdcc hbound
  have hqderiv : deriv q 0 = deriv f 0 / f 0 := by
    have h := (hfdif 0 h0U).hasDerivAt.div_const (f 0)
    have h' : HasDerivAt q (deriv f 0 / f 0) 0 := by
      simpa only [q] using h
    exact h'.deriv
  have hℓderiv : deriv ℓ 0 = deriv q 0 := by
    have h := lemma23_hasDerivAt_of_continuous_exp_lift hUopen h0U hℓcont hℓlift
      (hqdif 0 h0U).hasDerivAt (hqne 0 h0U)
    have h' : deriv ℓ 0 = deriv q 0 / q 0 := h.deriv
    simpa [hq0] using h'
  have hLogDeriv : deriv ℓ 0 = logDeriv f 0 := by
    rw [hℓderiv, hqderiv, logDeriv_apply]
  rw [← hLogDeriv]
  have hCauchy' : ‖deriv ℓ 0‖ ≤ (2 * Real.log H) / (R / 2) := by
    simpa using hCauchy
  calc
    ‖deriv ℓ 0‖ ≤ (2 * Real.log H) / (R / 2) := hCauchy'
    _ = 4 * Real.log H / R := by field_simp; norm_num

/-- Translation of the preceding estimate: the disk may be centered at any point `c`. -/
theorem lemma23_norm_logDeriv_le_of_norm_ratio_bound_on_ball
    {f : ℂ → ℂ} {c : ℂ} {R H : ℝ}
    (hR : 0 < R) (hH : 1 < H)
    (hfdif : ∀ z ∈ Metric.ball c R, DifferentiableAt ℂ f z)
    (hfne : ∀ z ∈ Metric.ball c R, f z ≠ 0)
    (hNorm : ∀ z ∈ Metric.ball c R, ‖f z / f c‖ ≤ H) :
    ‖logDeriv f c‖ ≤ 4 * Real.log H / R := by
  let g : ℂ → ℂ := fun z => f (c + z)
  have hshift (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) R) :
      c + z ∈ Metric.ball c R := by
    change dist z 0 < R at hz
    change dist (c + z) c < R
    simpa [dist_eq_norm] using hz
  have hfdif' : ∀ z ∈ Metric.ball (0 : ℂ) R, DifferentiableAt ℂ g z := by
    intro z hz
    exact (hfdif (c + z) (hshift z hz)).comp z (by fun_prop)
  have hfne' : ∀ z ∈ Metric.ball (0 : ℂ) R, g z ≠ 0 := by
    intro z hz
    exact hfne (c + z) (hshift z hz)
  have hNorm' : ∀ z ∈ Metric.ball (0 : ℂ) R, ‖g z / g 0‖ ≤ H := by
    intro z hz
    simpa [g] using hNorm (c + z) (hshift z hz)
  have hbase := lemma23_norm_logDeriv_le_of_norm_ratio_bound
    (f := g) hR hH hfdif' hfne' hNorm'
  have hderiv : deriv g 0 = deriv f c := by
    have hfc : HasDerivAt f (deriv f c) (c + 0) := by
      simpa using (hfdif c (Metric.mem_ball_self hR)).hasDerivAt
    have hg : HasDerivAt g (deriv f c) 0 := by
      simpa [g] using hfc.comp_const_add c 0
    exact hg.deriv
  have hlog : logDeriv g 0 = logDeriv f c := by
    rw [logDeriv_apply, logDeriv_apply, hderiv]
    simp [g]
  simpa [hlog] using hbase

/-- Specialization to Zhang's actual Section 4 polynomial `F(s, ψ)`.  Its analyticity is
discharged from the finite-sum definition; the zero-free disk and normalized modulus bound remain
explicit hypotheses, since proving those is the quantitative core of the paper's Section 4. -/
theorem lemma23_actualSectionFourF_logDeriv_bound
    {D : ℕ} (χ : RealPrimitiveCharacter D) (ψ : ℕ → ℂ) (c : ℂ) {R H : ℝ}
    (hR : 0 < R) (hH : 1 < H)
    (hFne : ∀ z ∈ Metric.ball c R, lemma23ActualSectionFourF χ ψ z ≠ 0)
    (hNorm : ∀ z ∈ Metric.ball c R,
      ‖lemma23ActualSectionFourF χ ψ z / lemma23ActualSectionFourF χ ψ c‖ ≤ H) :
    ‖logDeriv (lemma23ActualSectionFourF χ ψ) c‖ ≤ 4 * Real.log H / R := by
  apply lemma23_norm_logDeriv_le_of_norm_ratio_bound_on_ball hR hH
  · intro z hz
    have hF := lemma23FiniteDirichletPolynomial_analyticAt
      (D ^ 4) (fun n => lemma23NuArithmeticFunction χ n * ψ n) z
    simpa [lemma23ActualSectionFourF, lemma23SectionFourF] using hF.differentiableAt
  · exact hFne
  · exact hNorm

/-- If the paper's two-sided `𝓛^88` modulus estimate is available for the actual finite `F`,
then its logarithmic derivative is bounded by `704 log 𝓛 / R`.  The lower bound also supplies
the required zero-freeness; only the substantive two-sided estimate remains to be proved. -/
theorem lemma23_actualSectionFourF_logDeriv_bound_of_two_sided_norm
    {D : ℕ} (χ : RealPrimitiveCharacter D) (ψ : ℕ → ℂ) (c : ℂ) {R L : ℝ}
    (hR : 0 < R) (hL : 1 < L)
    (hFbound : ∀ z ∈ Metric.ball c R,
      (L ^ 88)⁻¹ ≤ ‖lemma23ActualSectionFourF χ ψ z‖ ∧
        ‖lemma23ActualSectionFourF χ ψ z‖ ≤ L ^ 88) :
    ‖logDeriv (lemma23ActualSectionFourF χ ψ) c‖ ≤ 704 * Real.log L / R := by
  have hFne : ∀ z ∈ Metric.ball c R, lemma23ActualSectionFourF χ ψ z ≠ 0 := by
    intro z hz hz0
    have hpositive : 0 < (L ^ 88)⁻¹ := by positivity
    have := hFbound z hz
    rw [hz0, norm_zero] at this
    linarith
  have hRatio : ∀ z ∈ Metric.ball c R,
      ‖lemma23ActualSectionFourF χ ψ z / lemma23ActualSectionFourF χ ψ c‖ ≤ L ^ 176 := by
    intro z hz
    have hc := hFbound c (Metric.mem_ball_self hR)
    have hcz : 0 < ‖lemma23ActualSectionFourF χ ψ c‖ := by
      have hpositive : 0 < (L ^ 88)⁻¹ := by positivity
      exact lt_of_lt_of_le hpositive hc.1
    rw [norm_div]
    apply (div_le_iff₀ hcz).2
    calc
      ‖lemma23ActualSectionFourF χ ψ z‖ ≤ L ^ 88 := (hFbound z hz).2
      _ = L ^ 176 * (L ^ 88)⁻¹ := by
        field_simp [ne_of_gt (lt_trans (by norm_num : (0 : ℝ) < 1) hL)]
      _ ≤ L ^ 176 * ‖lemma23ActualSectionFourF χ ψ c‖ := by
        exact mul_le_mul_of_nonneg_left hc.1 (by positivity)
  have hLpow : 1 < L ^ 176 := one_lt_pow₀ hL (by norm_num)
  have hbase := lemma23_actualSectionFourF_logDeriv_bound χ ψ c hR hLpow hFne hRatio
  calc
    ‖logDeriv (lemma23ActualSectionFourF χ ψ) c‖ ≤
        4 * Real.log (L ^ 176) / R := hbase
    _ = 704 * Real.log L / R := by
      rw [Real.log_pow]
      ring

end ZhangLS.Spec
