import ZhangLS.Spec.Lemma56AbelIntegralBound
import Mathlib.Analysis.MellinTransform

/-! # Actual right-half-plane growth for arbitrary nonprincipal complex characters

The actual bounded-sum Abel integral is analytic, agrees with the actual
L-function for Re s>1, and hence agrees throughout Re s>0.
-/

namespace ZhangLS.Spec
open Filter MeasureTheory Set Asymptotics Finset Complex
open scoped Real Topology
set_option maxHeartbeats 1000000

/-- The character partial sum, cut off below the range of Abel summation. -/
noncomputable def lemma56AbelPartialSum {r : ℕ} [NeZero r]
    (θ : DirichletCharacter ℂ r) (t : ℝ) : ℂ :=
  if 1 < t then ∑ n ∈ Icc 1 ⌊t⌋₊, θ (n : ZMod r) else 0

theorem lemma56AbelPartialSum_measurable
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) :
    Measurable (lemma56AbelPartialSum θ) := by
  have hsum : Measurable (fun t : ℝ => ∑ n ∈ Icc 1 ⌊t⌋₊, θ (n : ZMod r)) :=
    (measurable_of_countable
      (fun N : ℕ => ∑ n ∈ Icc 1 N, θ (n : ZMod r))).comp Nat.measurable_floor
  exact Measurable.ite (p := fun t : ℝ => 1 < t) measurableSet_Ioi hsum measurable_const

theorem lemma56_norm_abelPartialSum_le
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) (t : ℝ) :
    ‖lemma56AbelPartialSum θ t‖ ≤ (r : ℝ) := by
  by_cases ht : 1 < t
  · simp [lemma56AbelPartialSum, ht]
    exact lemma56_character_norm_sum_Icc_le_modulus θ hθ ⌊t⌋₊
  · simp [lemma56AbelPartialSum, ht]

private theorem lemma56AbelPartialSum_locallyIntegrable
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) :
    LocallyIntegrableOn (lemma56AbelPartialSum θ) (Ioi 0) := by
  rw [locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed]
  intro K hKsub hKcompact
  have hconst : IntegrableOn (fun _ : ℝ => (r : ℝ)) K :=
    integrableOn_const hKcompact.measure_ne_top
  change Integrable (fun _ : ℝ => (r : ℝ)) (volume.restrict K) at hconst
  apply Integrable.mono' hconst
  · exact (lemma56AbelPartialSum_measurable θ).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem hKcompact.measurableSet] with t ht
    exact lemma56_norm_abelPartialSum_le θ hθ t

private theorem lemma56AbelPartialSum_isBigO_atTop
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) :
    (lemma56AbelPartialSum θ) =O[atTop] (fun t : ℝ => t ^ (-(0 : ℝ))) := by
  rw [isBigO_iff]
  refine ⟨(r : ℝ), ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have hbound := lemma56_norm_abelPartialSum_le θ hθ t
  simpa using hbound

private theorem lemma56AbelPartialSum_isBigO_nhdsGT_zero
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (b : ℝ) :
    (lemma56AbelPartialSum θ) =O[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => t ^ (-b)) := by
  rw [isBigO_iff]
  refine ⟨0, ?_⟩
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
  have hnot : ¬ 1 < t := by linarith [ht.2]
  simp [lemma56AbelPartialSum, hnot]

/-- The Mellin transform of the cutoff partial sum is exactly the Abel
integral on `(1,∞)`. -/
theorem lemma56_abelIntegral_eq_mellin
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) {s : ℂ} :
    lemma56AbelIntegral θ s = mellin (lemma56AbelPartialSum θ) (-s) := by
  unfold lemma56AbelIntegral mellin
  have hwhole :
      ∫ t : ℝ in Ioi 0,
        (t : ℂ) ^ ((-s) - 1) * lemma56AbelPartialSum θ t =
      ∫ t : ℝ in Ioi 1,
        (t : ℂ) ^ ((-s) - 1) * lemma56AbelPartialSum θ t := by
    apply setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
      (by intro t ht; exact lt_trans (by norm_num : (0 : ℝ) < 1) ht)
    intro t ht
    rcases ht with ⟨_, htcut⟩
    have htcut' : ¬ 1 < t := by simpa using htcut
    have hzero : lemma56AbelPartialSum θ t = 0 := by
      simp [lemma56AbelPartialSum, htcut']
    rw [hzero]
    simp
  calc
    (∫ t : ℝ in Ioi 1,
        (∑ n ∈ Finset.Icc 1 ⌊t⌋₊, θ (n : ZMod r)) * (t : ℂ) ^ (-(s + 1))) =
      ∫ t : ℝ in Ioi 1,
        (t : ℂ) ^ ((-s) - 1) * lemma56AbelPartialSum θ t := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro t ht
          have ht' : 1 < t := ht
          rw [show -(s + 1) = (-s) - 1 by ring]
          simp [lemma56AbelPartialSum, ht', mul_comm]
    _ = ∫ t : ℝ in Ioi 0,
        (t : ℂ) ^ ((-s) - 1) * lemma56AbelPartialSum θ t := hwhole.symm
    _ = mellin (lemma56AbelPartialSum θ) (-s) := by
          rfl

/-- The Mellin expression multiplied by `s` is analytic throughout the
open right half-plane. -/
theorem lemma56AbelMellin_differentiableAt
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ
      (fun z : ℂ => z * mellin (lemma56AbelPartialSum θ) (-z)) s := by
  let b : ℝ := (-s).re - 1
  have htop := lemma56AbelPartialSum_isBigO_atTop θ hθ
  have hbot := lemma56AbelPartialSum_isBigO_nhdsGT_zero θ b
  have hs_top : (-s).re < 0 := by simp; linarith
  have hs_bot : b < (-s).re := by dsimp [b]; linarith
  have hmellin : DifferentiableAt ℂ (mellin (lemma56AbelPartialSum θ)) (-s) :=
    mellin_differentiableAt_of_isBigO_rpow
    (lemma56AbelPartialSum_locallyIntegrable θ hθ) htop hs_top hbot hs_bot
  have hneg : DifferentiableAt ℂ (fun z : ℂ => -z) s := by fun_prop
  exact differentiableAt_id.mul (hmellin.comp s hneg)

private theorem lemma56AbelMellin_analyticOnNhd
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) :
    AnalyticOnNhd ℂ
      (fun z : ℂ => z * mellin (lemma56AbelPartialSum θ) (-z))
      {z : ℂ | 0 < z.re} := by
  refine DifferentiableOn.analyticOnNhd (fun z hz => ?_)
    (isOpen_lt continuous_const continuous_re)
  exact (lemma56AbelMellin_differentiableAt θ hθ hz).differentiableWithinAt

private theorem lemma56_actual_LFunction_analytic_rightHalfPlane
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) :
    AnalyticOnNhd ℂ (DirichletCharacter.LFunction θ) {z : ℂ | 0 < z.re} := by
  refine DifferentiableOn.analyticOnNhd (fun z hz => ?_)
    (isOpen_lt continuous_const continuous_re)
  exact (DirichletCharacter.differentiable_LFunction hθ).differentiableAt.differentiableWithinAt

/-- Analytic continuation of Abel summation: throughout `re s > 0`, the
actual analytically continued L-function equals `s` times the Abel integral. -/
theorem lemma56_actual_LFunction_eq_abelIntegral_re_pos
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.LFunction θ s = s * lemma56AbelIntegral θ s := by
  let F : ℂ → ℂ := fun z => z * mellin (lemma56AbelPartialSum θ) (-z)
  let U : Set ℂ := {z : ℂ | 0 < z.re}
  have hF : AnalyticOnNhd ℂ F U := by
    simpa [F, U] using lemma56AbelMellin_analyticOnNhd θ hθ
  have hL : AnalyticOnNhd ℂ (DirichletCharacter.LFunction θ) U := by
    simpa [U] using lemma56_actual_LFunction_analytic_rightHalfPlane θ hθ
  have hpre : IsPreconnected U := by
    simpa [U] using (convex_halfSpace_re_gt 0).isPreconnected
  have htwo : (2 : ℂ) ∈ U := by norm_num [U]
  have hnear : F =ᶠ[𝓝 (2 : ℂ)] DirichletCharacter.LFunction θ := by
    have hregion : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by norm_num)
    filter_upwards [hregion] with z hz
    have habel := lemma56_actual_LFunction_eq_abelIntegral θ hθ hz
    calc
      F z = z * lemma56AbelIntegral θ z := by
        change z * mellin (lemma56AbelPartialSum θ) (-z) = _
        rw [lemma56_abelIntegral_eq_mellin θ]
      _ = DirichletCharacter.LFunction θ z := habel.symm
  have hEq := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    hF hL hpre htwo hnear
  have hpoint := hEq (show s ∈ U by exact hs)
  have hpoint' : s * lemma56AbelIntegral θ s = DirichletCharacter.LFunction θ s := by
    calc
      s * lemma56AbelIntegral θ s = s * mellin (lemma56AbelPartialSum θ) (-s) := by
        rw [lemma56_abelIntegral_eq_mellin θ]
      _ = F s := rfl
      _ = DirichletCharacter.LFunction θ s := hpoint
  exact hpoint'.symm

/-- Explicit linear growth in height on the critical line (and more generally
on every fixed positive vertical line). -/
theorem lemma56_actual_LFunction_bound_re_pos
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    ‖DirichletCharacter.LFunction θ s‖ ≤ ‖s‖ * ((r : ℝ) / s.re) := by
  rw [lemma56_actual_LFunction_eq_abelIntegral_re_pos θ hθ hs]
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (lemma56_actual_abelIntegral_norm_bound θ hθ hs) (norm_nonneg _)

theorem lemma56_actual_LFunction_bound_critical_line
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1)
    {s : ℂ} (hs : s.re = 1 / 2) :
    ‖DirichletCharacter.LFunction θ s‖ ≤ 2 * (r : ℝ) * ‖s‖ := by
  have hpos : 0 < s.re := by rw [hs]; norm_num
  have h := lemma56_actual_LFunction_bound_re_pos θ hθ hpos
  rw [hs] at h
  have hden : (r : ℝ) / (1 / 2) = 2 * (r : ℝ) := by
    field_simp
  rw [hden] at h
  nlinarith [h]

end ZhangLS.Spec
