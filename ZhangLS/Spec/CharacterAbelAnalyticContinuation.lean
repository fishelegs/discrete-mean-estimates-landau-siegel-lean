import ZhangLS.Spec.CharacterAbelIntegralBound
import Mathlib.Analysis.MellinTransform

/-!
# Analytic continuation of the character Abel integral

The bounded partial sums of a nontrivial primitive character define a
Mellin transform in the left half-plane.  The Mellin differentiability
theorem, followed by the identity theorem, extends the Abel representation
of the actual Dirichlet L-function from `re s > 1` to `re s > 0`.
-/

namespace ZhangLS.Spec

open Filter MeasureTheory Set Asymptotics Finset Complex
open scoped Real Topology

/-- The character partial sum, cut off below the range of Abel summation. -/
noncomputable def characterAbelPartialSum {D : ℕ}
    (χ : RealPrimitiveCharacter D) (t : ℝ) : ℂ :=
  if 1 < t then ∑ n ∈ Icc 1 ⌊t⌋₊, χ.evalNat n else 0

theorem RealPrimitiveCharacter.characterAbelPartialSum_measurable
    {D : ℕ} (χ : RealPrimitiveCharacter D) :
    Measurable (characterAbelPartialSum χ) := by
  have hsum : Measurable (fun t : ℝ => ∑ n ∈ Icc 1 ⌊t⌋₊, χ.evalNat n) :=
    (measurable_of_countable
      (fun N : ℕ => ∑ n ∈ Icc 1 N, χ.evalNat n)).comp Nat.measurable_floor
  exact Measurable.ite (p := fun t : ℝ => 1 < t) measurableSet_Ioi hsum measurable_const

theorem RealPrimitiveCharacter.norm_characterAbelPartialSum_le
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) (t : ℝ) :
    ‖characterAbelPartialSum χ t‖ ≤ (D : ℝ) := by
  by_cases ht : 1 < t
  · simp [characterAbelPartialSum, ht]
    exact χ.norm_sum_Icc_evalNat_le_modulus hD ⌊t⌋₊
  · simp [characterAbelPartialSum, ht]

private theorem characterAbelPartialSum_locallyIntegrable
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    LocallyIntegrableOn (characterAbelPartialSum χ) (Ioi 0) := by
  rw [locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed]
  intro K hKsub hKcompact
  have hconst : IntegrableOn (fun _ : ℝ => (D : ℝ)) K :=
    integrableOn_const hKcompact.measure_ne_top
  change Integrable (fun _ : ℝ => (D : ℝ)) (volume.restrict K) at hconst
  apply Integrable.mono' hconst
  · exact (χ.characterAbelPartialSum_measurable).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem hKcompact.measurableSet] with t ht
    exact χ.norm_characterAbelPartialSum_le hD t

private theorem characterAbelPartialSum_isBigO_atTop
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    (characterAbelPartialSum χ) =O[atTop] (fun t : ℝ => t ^ (-(0 : ℝ))) := by
  rw [isBigO_iff]
  refine ⟨(D : ℝ), ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have hbound := χ.norm_characterAbelPartialSum_le hD t
  simpa using hbound

private theorem characterAbelPartialSum_isBigO_nhdsGT_zero
    {D : ℕ} (χ : RealPrimitiveCharacter D) (b : ℝ) :
    (characterAbelPartialSum χ) =O[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => t ^ (-b)) := by
  rw [isBigO_iff]
  refine ⟨0, ?_⟩
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
  have hnot : ¬ 1 < t := by linarith [ht.2]
  simp [characterAbelPartialSum, hnot]

/-- The Mellin transform of the cutoff partial sum is exactly the Abel
integral on `(1,∞)`. -/
theorem characterAbelIntegral_eq_mellin
    {D : ℕ} (χ : RealPrimitiveCharacter D) {s : ℂ} :
    characterAbelIntegral χ s = mellin (characterAbelPartialSum χ) (-s) := by
  unfold characterAbelIntegral mellin
  have hwhole :
      ∫ t : ℝ in Ioi 0,
        (t : ℂ) ^ ((-s) - 1) * characterAbelPartialSum χ t =
      ∫ t : ℝ in Ioi 1,
        (t : ℂ) ^ ((-s) - 1) * characterAbelPartialSum χ t := by
    apply setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
      (by intro t ht; exact lt_trans (by norm_num : (0 : ℝ) < 1) ht)
    intro t ht
    rcases ht with ⟨_, htcut⟩
    have htcut' : ¬ 1 < t := by simpa using htcut
    have hzero : characterAbelPartialSum χ t = 0 := by
      simp [characterAbelPartialSum, htcut']
    rw [hzero]
    simp
  calc
    (∫ t : ℝ in Ioi 1,
        (∑ n ∈ Finset.Icc 1 ⌊t⌋₊, χ.evalNat n) * (t : ℂ) ^ (-(s + 1))) =
      ∫ t : ℝ in Ioi 1,
        (t : ℂ) ^ ((-s) - 1) * characterAbelPartialSum χ t := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro t ht
          have ht' : 1 < t := ht
          rw [show -(s + 1) = (-s) - 1 by ring]
          simp [characterAbelPartialSum, ht', mul_comm]
    _ = ∫ t : ℝ in Ioi 0,
        (t : ℂ) ^ ((-s) - 1) * characterAbelPartialSum χ t := hwhole.symm
    _ = mellin (characterAbelPartialSum χ) (-s) := by
          rfl

/-- The Mellin expression multiplied by `s` is analytic throughout the
open right half-plane. -/
theorem characterAbelMellin_differentiableAt
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ
      (fun z : ℂ => z * mellin (characterAbelPartialSum χ) (-z)) s := by
  let b : ℝ := (-s).re - 1
  have htop := characterAbelPartialSum_isBigO_atTop χ hD
  have hbot := characterAbelPartialSum_isBigO_nhdsGT_zero χ b
  have hs_top : (-s).re < 0 := by simp; linarith
  have hs_bot : b < (-s).re := by dsimp [b]; linarith
  have hmellin : DifferentiableAt ℂ (mellin (characterAbelPartialSum χ)) (-s) :=
    mellin_differentiableAt_of_isBigO_rpow
    (characterAbelPartialSum_locallyIntegrable χ hD) htop hs_top hbot hs_bot
  have hneg : DifferentiableAt ℂ (fun z : ℂ => -z) s := by fun_prop
  exact differentiableAt_id.mul (hmellin.comp s hneg)

private theorem characterAbelMellin_analyticOnNhd
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    AnalyticOnNhd ℂ
      (fun z : ℂ => z * mellin (characterAbelPartialSum χ) (-z))
      {z : ℂ | 0 < z.re} := by
  refine DifferentiableOn.analyticOnNhd (fun z hz => ?_)
    (isOpen_lt continuous_const continuous_re)
  exact (characterAbelMellin_differentiableAt χ hD hz).differentiableWithinAt

private theorem dirichletLFunction_analyticOnNhd_rightHalfPlane
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    AnalyticOnNhd ℂ (dirichletLFunction χ) {z : ℂ | 0 < z.re} := by
  refine DifferentiableOn.analyticOnNhd (fun z hz => ?_)
    (isOpen_lt continuous_const continuous_re)
  exact (differentiable_dirichletLFunction_of_one_lt_modulus χ hD).differentiableAt.differentiableWithinAt

/-- Analytic continuation of Abel summation: throughout `re s > 0`, the
actual analytically continued L-function equals `s` times the Abel integral. -/
theorem dirichletLFunction_eq_abelIntegral_of_pos_re
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    {s : ℂ} (hs : 0 < s.re) :
    dirichletLFunction χ s = s * characterAbelIntegral χ s := by
  let F : ℂ → ℂ := fun z => z * mellin (characterAbelPartialSum χ) (-z)
  let U : Set ℂ := {z : ℂ | 0 < z.re}
  have hF : AnalyticOnNhd ℂ F U := by
    simpa [F, U] using characterAbelMellin_analyticOnNhd χ hD
  have hL : AnalyticOnNhd ℂ (dirichletLFunction χ) U := by
    simpa [U] using dirichletLFunction_analyticOnNhd_rightHalfPlane χ hD
  have hpre : IsPreconnected U := by
    simpa [U] using (convex_halfSpace_re_gt 0).isPreconnected
  have htwo : (2 : ℂ) ∈ U := by norm_num [U]
  have hnear : F =ᶠ[𝓝 (2 : ℂ)] dirichletLFunction χ := by
    have hregion : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by norm_num)
    filter_upwards [hregion] with z hz
    have habel := dirichletLFunction_eq_abelIntegral χ hD hz
    calc
      F z = z * characterAbelIntegral χ z := by
        change z * mellin (characterAbelPartialSum χ) (-z) = _
        rw [characterAbelIntegral_eq_mellin χ]
      _ = dirichletLFunction χ z := habel.symm
  have hEq := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    hF hL hpre htwo hnear
  have hpoint := hEq (show s ∈ U by exact hs)
  have hpoint' : s * characterAbelIntegral χ s = dirichletLFunction χ s := by
    calc
      s * characterAbelIntegral χ s = s * mellin (characterAbelPartialSum χ) (-s) := by
        rw [characterAbelIntegral_eq_mellin χ]
      _ = F s := rfl
      _ = dirichletLFunction χ s := hpoint
  exact hpoint'.symm

/-- Explicit linear growth in height on the critical line (and more generally
on every fixed positive vertical line). -/
theorem RealPrimitiveCharacter.norm_dirichletLFunction_le_of_pos_re
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    {s : ℂ} (hs : 0 < s.re) :
    ‖dirichletLFunction χ s‖ ≤ ‖s‖ * ((D : ℝ) / s.re) := by
  rw [dirichletLFunction_eq_abelIntegral_of_pos_re χ hD hs]
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (χ.norm_characterAbelIntegral_le hD hs) (norm_nonneg _)

theorem RealPrimitiveCharacter.norm_dirichletLFunction_le_on_critical_line
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    {s : ℂ} (hs : s.re = 1 / 2) :
    ‖dirichletLFunction χ s‖ ≤ 2 * (D : ℝ) * ‖s‖ := by
  have hpos : 0 < s.re := by rw [hs]; norm_num
  have h := χ.norm_dirichletLFunction_le_of_pos_re hD hpos
  rw [hs] at h
  have hden : (D : ℝ) / (1 / 2) = 2 * (D : ℝ) := by
    field_simp
  rw [hden] at h
  nlinarith [h]

end ZhangLS.Spec
