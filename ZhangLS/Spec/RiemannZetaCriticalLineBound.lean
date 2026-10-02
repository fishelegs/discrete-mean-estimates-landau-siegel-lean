import ZhangLS.Spec.CharacterAbelAnalyticContinuation
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# An elementary critical-line bound for the Riemann zeta function

Subtracting the continuous main term from the counting function `⌊t⌋`
leaves its bounded fractional part.  Its Mellin transform is analytic for
`re s > 0`; after regularizing the pole at `s = 1`, the identity theorem
extends the resulting formula from `re s > 1` to the right half-plane.
-/

namespace ZhangLS.Spec

open Complex Filter MeasureTheory Set Asymptotics Finset
open scoped Real Topology

/-- The fractional-part correction, supported on the range of Abel summation. -/
noncomputable def zetaFractionalPart (t : ℝ) : ℂ :=
  if (1 : ℝ) < t then ((Int.fract t : ℝ) : ℂ) else 0

theorem zetaFractionalPart_measurable : Measurable zetaFractionalPart := by
  have hfloor : Measurable (fun t : ℝ => (Int.floor t : ℝ)) :=
    (measurable_of_countable (fun n : ℤ => (n : ℝ))).comp Int.measurable_floor
  have hfractReal : Measurable (fun t : ℝ => Int.fract t) := by
    change Measurable (fun t : ℝ => t - (Int.floor t : ℝ))
    exact measurable_id.sub hfloor
  have hfract : Measurable (fun t : ℝ => ((Int.fract t : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp hfractReal
  exact Measurable.ite (p := fun t : ℝ => (1 : ℝ) < t) measurableSet_Ioi hfract measurable_const

theorem norm_zetaFractionalPart_le_one (t : ℝ) :
    ‖zetaFractionalPart t‖ ≤ 1 := by
  by_cases ht : 1 < t
  · have hfract : 0 ≤ Int.fract t := Int.fract_nonneg t
    simp only [zetaFractionalPart, if_pos ht, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hfract]
    exact (Int.fract_lt_one t).le
  · simp [zetaFractionalPart, ht]

private theorem zetaFractionalPart_locallyIntegrable :
    LocallyIntegrableOn zetaFractionalPart (Ioi 0) := by
  rw [locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed]
  intro K hKsub hKcompact
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) K :=
    integrableOn_const hKcompact.measure_ne_top
  change Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict K) at hconst
  apply Integrable.mono' hconst
  · exact zetaFractionalPart_measurable.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem hKcompact.measurableSet] with t ht
    exact norm_zetaFractionalPart_le_one t

private theorem zetaFractionalPart_isBigO_atTop :
    zetaFractionalPart =O[atTop] (fun t : ℝ => t ^ (-(0 : ℝ))) := by
  rw [isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [] with t
  simpa using norm_zetaFractionalPart_le_one t

private theorem zetaFractionalPart_isBigO_nhdsGT_zero (b : ℝ) :
    zetaFractionalPart =O[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ (-b)) := by
  rw [isBigO_iff]
  refine ⟨0, ?_⟩
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
  have hnot : ¬ 1 < t := by linarith [ht.2]
  simp [zetaFractionalPart, hnot]

private theorem zetaFractionalPart_mellin_differentiableAt
    {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (fun z : ℂ => mellin zetaFractionalPart (-z)) s := by
  let b : ℝ := (-s).re - 1
  have hs_top : (-s).re < 0 := by simp; linarith
  have hs_bot : b < (-s).re := by dsimp [b]; linarith
  have hm := mellin_differentiableAt_of_isBigO_rpow
    zetaFractionalPart_locallyIntegrable zetaFractionalPart_isBigO_atTop hs_top
    (zetaFractionalPart_isBigO_nhdsGT_zero b) hs_bot
  have hneg : DifferentiableAt ℂ (fun z : ℂ => -z) s := by fun_prop
  exact hm.comp s hneg

private theorem zetaFractionalPart_mellin_analyticOnNhd :
    AnalyticOnNhd ℂ (fun z : ℂ => mellin zetaFractionalPart (-z))
      {z : ℂ | 0 < z.re} := by
  refine DifferentiableOn.analyticOnNhd (fun z hz => ?_)
    (isOpen_lt continuous_const continuous_re)
  exact (zetaFractionalPart_mellin_differentiableAt hz).differentiableWithinAt

/-- The regularization `(s - 1) ζ(s)` with its removable value filled at `1`.
The completed zeta function makes this genuinely analytic on `re s > 0`. -/
noncomputable def zetaPoleRemoved (s : ℂ) : ℂ :=
  ((s - 1) * (completedRiemannZeta₀ s - s⁻¹) + 1) * (Gammaℝ s)⁻¹

theorem zetaPoleRemoved_eq_mul_riemannZeta {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    zetaPoleRemoved s = (s - 1) * riemannZeta s := by
  rw [zetaPoleRemoved, riemannZeta_def_of_ne_zero hs0, completedRiemannZeta_eq]
  rw [div_eq_mul_inv]
  have hsden : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  field_simp [hs0, hsden]
  <;> ring

private theorem zetaPoleRemoved_differentiableAt
    {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ zetaPoleRemoved s := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  unfold zetaPoleRemoved
  have hmain : DifferentiableAt ℂ
      (fun z : ℂ => (z - 1) * (completedRiemannZeta₀ z - z⁻¹) + 1) s := by
    exact ((differentiableAt_id.sub_const 1).mul
      (differentiable_completedZeta₀.differentiableAt.sub
        (differentiableAt_inv hs0))).add_const 1
  exact hmain.mul differentiable_Gammaℝ_inv.differentiableAt

private theorem zetaPoleRemoved_analyticOnNhd :
    AnalyticOnNhd ℂ zetaPoleRemoved {z : ℂ | 0 < z.re} := by
  refine DifferentiableOn.analyticOnNhd (fun z hz => ?_)
    (isOpen_lt continuous_const continuous_re)
  exact (zetaPoleRemoved_differentiableAt hz).differentiableWithinAt

/-- The Mellin transform of the cutoff fractional part is its integral over
`(1,∞)`, since the cutoff vanishes on `(0,1]`. -/
theorem mellin_zetaFractionalPart_eq_integral
    {s : ℂ} (hs : 0 < s.re) :
    mellin zetaFractionalPart (-s) =
      ∫ t : ℝ in Ioi 1, ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  unfold mellin
  have hwhole :
      ∫ t : ℝ in Ioi 0, (t : ℂ) ^ ((-s) - 1) * zetaFractionalPart t =
      ∫ t : ℝ in Ioi 1, (t : ℂ) ^ ((-s) - 1) * zetaFractionalPart t := by
    apply setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
      (by intro t ht; exact lt_trans (by norm_num : (0 : ℝ) < 1) ht)
    intro t ht
    rcases ht with ⟨_, htcut⟩
    have htcut' : ¬ 1 < t := by simpa using htcut
    have hzero : zetaFractionalPart t = 0 := by simp [zetaFractionalPart, htcut']
    rw [hzero]
    simp
  calc
    mellin zetaFractionalPart (-s) =
        ∫ t : ℝ in Ioi 0, (t : ℂ) ^ ((-s) - 1) * zetaFractionalPart t := by
          simp [mellin, smul_eq_mul]
    _ = ∫ t : ℝ in Ioi 1, (t : ℂ) ^ ((-s) - 1) * zetaFractionalPart t := hwhole
    _ = ∫ t : ℝ in Ioi 1, ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro t ht
          have ht' : 1 < t := ht
          rw [show -(s + 1) = (-s) - 1 by ring]
          simp [zetaFractionalPart, ht', mul_comm]

private theorem sum_one_Icc (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (1 : ℂ) = (N : ℂ) := by
  simp

private theorem zeta_partial_sums_isBigO :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (1 : ℂ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (1 : ℝ)) := by
  rw [isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [] with n
  simp [sum_one_Icc]

private theorem riemannZeta_eq_fractionalPart_formula
    {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = s / (s - 1) - s * mellin zetaFractionalPart (-s) := by
  have hsum : LSeriesSummable (fun _ : ℕ => (1 : ℂ)) s :=
    LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
      (fun _ _ => by norm_num) hs
  have habel := LSeries_eq_mul_integral (fun _ : ℕ => (1 : ℂ))
    (r := 1) (by norm_num) (by linarith) hsum zeta_partial_sums_isBigO
  have hmainInt : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s)) (Ioi 1) := by
    exact integrableOn_Ioi_cpow_of_lt (by simpa using neg_lt_neg hs) one_pos
  have hfracInt : IntegrableOn
      (fun t : ℝ => ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) (Ioi 1) := by
    let g : ℝ → ℂ := fun t => ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))
    have hmaj : IntegrableOn (fun t : ℝ => t ^ (-s.re - 1)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
    apply Integrable.mono' hmaj
    · have hfloor : Measurable (fun t : ℝ => (Int.floor t : ℝ)) :=
        (measurable_of_countable (fun n : ℤ => (n : ℝ))).comp Int.measurable_floor
      have hfractReal : Measurable (fun t : ℝ => Int.fract t) := by
        change Measurable (fun t : ℝ => t - (Int.floor t : ℝ))
        exact measurable_id.sub hfloor
      have hfract : Measurable (fun t : ℝ => ((Int.fract t : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.measurable.comp hfractReal
      have hkernel : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-(s + 1))) (Ioi 1) := by
        intro t ht
        exact (Complex.continuousAt_ofReal_cpow_const t (-(s + 1))
          (Or.inr (by linarith [mem_Ioi.mp ht]))).continuousWithinAt
      exact hfract.aestronglyMeasurable.mul
        (hkernel.aestronglyMeasurable measurableSet_Ioi)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have htpos : 0 < t := by linarith [mem_Ioi.mp ht]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Int.fract_nonneg t),
        norm_cpow_eq_rpow_re_of_pos htpos]
      have hre : (-(s + 1)).re = -s.re - 1 := by simp; ring
      rw [hre]
      exact mul_le_of_le_one_left (Real.rpow_nonneg htpos.le _)
        (Int.fract_lt_one t).le
  have hpoint :
      (fun t : ℝ =>
        (∑ n ∈ Finset.Icc 1 ⌊t⌋₊, (1 : ℂ)) * (t : ℂ) ^ (-(s + 1))) =ᵐ[volume.restrict (Ioi 1)]
      (fun t => (t : ℂ) ^ (-s) -
        ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : 0 < t := by linarith [mem_Ioi.mp ht]
    have hfloorReal : (⌊t⌋₊ : ℝ) = t - Int.fract t := by
      rw [natCast_floor_eq_intCast_floor (by linarith)]
      linarith [Int.fract_add_floor t]
    have hfloorComplex : (⌊t⌋₊ : ℂ) = (t : ℂ) - ((Int.fract t : ℝ) : ℂ) := by
      exact_mod_cast hfloorReal
    have hpow : (t : ℂ) * (t : ℂ) ^ (-(s + 1)) = (t : ℂ) ^ (-s) := by
      calc
        (t : ℂ) * (t : ℂ) ^ (-(s + 1)) =
            (t : ℂ) ^ (1 : ℂ) * (t : ℂ) ^ (-(s + 1)) := by simp
        _ = (t : ℂ) ^ (1 + (-(s + 1))) := by
          rw [← cpow_add _ _ (ofReal_ne_zero.mpr htpos.ne')]
        _ = (t : ℂ) ^ (-s) := by congr 1 <;> ring
    rw [sum_one_Icc, hfloorComplex]
    calc
      ((t : ℂ) - ((Int.fract t : ℝ) : ℂ)) * (t : ℂ) ^ (-(s + 1)) =
          (t : ℂ) * (t : ℂ) ^ (-(s + 1)) -
            ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by ring
      _ = (t : ℂ) ^ (-s) -
          ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by rw [hpow]
  have hmainEval :
      ∫ t : ℝ in Ioi 1, (t : ℂ) ^ (-s) = 1 / (s - 1) := by
    calc
      ∫ t : ℝ in Ioi 1, (t : ℂ) ^ (-s) =
          -(1 : ℂ) ^ (-s + 1) / (-s + 1) :=
        integral_Ioi_cpow_of_lt (by simpa using neg_lt_neg hs) one_pos
      _ = 1 / (s - 1) := by
        simp only [one_cpow, one_div]
        have hs1 : s - 1 ≠ 0 := by
          intro h
          have hreal : 0 < (s - 1).re := by simp [Complex.sub_re]; linarith
          rw [h] at hreal
          norm_num at hreal
        rw [show -s + 1 = -(s - 1) by ring]
        field_simp [hs1]
        <;> ring
  have habel' : riemannZeta s =
      s * ∫ t : ℝ in Ioi 1,
        (∑ n ∈ Finset.Icc 1 ⌊t⌋₊, (1 : ℂ)) * (t : ℂ) ^ (-(s + 1)) := by
    rw [← LSeries_one_eq_riemannZeta hs]
    simpa [sum_one_Icc] using habel
  rw [habel']
  have hintEq :
      ∫ t : ℝ in Ioi 1,
        (∑ n ∈ Finset.Icc 1 ⌊t⌋₊, (1 : ℂ)) * (t : ℂ) ^ (-(s + 1)) =
      (∫ t : ℝ in Ioi 1, (t : ℂ) ^ (-s)) -
        ∫ t : ℝ in Ioi 1,
          ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
    calc
      _ = ∫ t : ℝ in Ioi 1,
          ((t : ℂ) ^ (-s) -
            ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) := integral_congr_ae hpoint
      _ = _ := integral_sub hmainInt hfracInt
  have hpos : 0 < s.re := by linarith
  rw [hintEq, hmainEval, mellin_zetaFractionalPart_eq_integral hpos]
  ring

private theorem zetaRegularizedAbel_analyticOnNhd :
    AnalyticOnNhd ℂ
      (fun z : ℂ => z - z * (z - 1) * mellin zetaFractionalPart (-z))
      {z : ℂ | 0 < z.re} := by
  refine DifferentiableOn.analyticOnNhd (fun z hz => ?_)
    (isOpen_lt continuous_const continuous_re)
  have hcomp := zetaFractionalPart_mellin_differentiableAt hz
  exact (differentiableAt_id.sub
    ((differentiableAt_id.mul (differentiableAt_id.sub_const 1)).mul hcomp)).differentiableWithinAt

/-- The pole-removed zeta identity on the right half-plane. -/
theorem zetaPoleRemoved_eq_regularizedAbel_of_pos_re
    {s : ℂ} (hs : 0 < s.re) :
    zetaPoleRemoved s = s - s * (s - 1) * mellin zetaFractionalPart (-s) := by
  let U : Set ℂ := {z : ℂ | 0 < z.re}
  have hZ : AnalyticOnNhd ℂ zetaPoleRemoved U := by
    simpa [U] using zetaPoleRemoved_analyticOnNhd
  have hA : AnalyticOnNhd ℂ
      (fun z : ℂ => z - z * (z - 1) * mellin zetaFractionalPart (-z)) U := by
    simpa [U] using zetaRegularizedAbel_analyticOnNhd
  have hpre : IsPreconnected U := by
    simpa [U] using (convex_halfSpace_re_gt 0).isPreconnected
  have htwo : (2 : ℂ) ∈ U := by norm_num [U]
  have hnear : zetaPoleRemoved =ᶠ[𝓝 (2 : ℂ)]
      (fun z : ℂ => z - z * (z - 1) * mellin zetaFractionalPart (-z)) := by
    have hregion : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by norm_num)
    filter_upwards [hregion] with z hz
    have hformula := riemannZeta_eq_fractionalPart_formula hz
    have hz0 : z ≠ 0 := by
      intro h
      rw [h] at hz
      norm_num at hz
    have hz1 : z ≠ 1 := by
      intro h
      rw [h] at hz
      norm_num at hz
    rw [zetaPoleRemoved_eq_mul_riemannZeta hz0 hz1, hformula]
    field_simp [sub_ne_zero.mpr hz1]
    <;> ring
  have hEq := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    hZ hA hpre htwo hnear
  exact hEq hs

/-- Away from its pole, zeta is given by the bounded fractional-part Mellin
formula throughout `re(s) > 0`. -/
theorem riemannZeta_eq_fractionalPart_formula_of_pos_re
    {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = s / (s - 1) - s * mellin zetaFractionalPart (-s) := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hregular := zetaPoleRemoved_eq_regularizedAbel_of_pos_re hs
  rw [zetaPoleRemoved_eq_mul_riemannZeta hs0 hs1] at hregular
  apply (mul_left_cancel₀ (sub_ne_zero.mpr hs1))
  calc
    (s - 1) * riemannZeta s = s - s * (s - 1) * mellin zetaFractionalPart (-s) := hregular
    _ = (s - 1) * (s / (s - 1) -
        s * mellin zetaFractionalPart (-s)) := by
      field_simp [sub_ne_zero.mpr hs1]

/-- The bounded fractional-part Mellin transform has the elementary bound
`1 / re(s)` throughout the right half-plane. -/
theorem norm_mellin_zetaFractionalPart_le
    {s : ℂ} (hs : 0 < s.re) :
    ‖mellin zetaFractionalPart (-s)‖ ≤ (1 : ℝ) / s.re := by
  rw [mellin_zetaFractionalPart_eq_integral hs]
  have hfracInt : IntegrableOn
      (fun t : ℝ => ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) (Ioi 1) := by
    have hmaj : IntegrableOn (fun t : ℝ => t ^ (-s.re - 1)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
    apply Integrable.mono' hmaj
    · have hfloor : Measurable (fun t : ℝ => (Int.floor t : ℝ)) :=
        (measurable_of_countable (fun n : ℤ => (n : ℝ))).comp Int.measurable_floor
      have hfractReal : Measurable (fun t : ℝ => Int.fract t) := by
        change Measurable (fun t : ℝ => t - (Int.floor t : ℝ))
        exact measurable_id.sub hfloor
      have hfract : Measurable (fun t : ℝ => ((Int.fract t : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.measurable.comp hfractReal
      have hkernel : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-(s + 1))) (Ioi 1) := by
        intro t ht
        exact (Complex.continuousAt_ofReal_cpow_const t (-(s + 1))
          (Or.inr (by linarith [mem_Ioi.mp ht]))).continuousWithinAt
      exact hfract.aestronglyMeasurable.mul
        (hkernel.aestronglyMeasurable measurableSet_Ioi)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have htpos : 0 < t := by linarith [mem_Ioi.mp ht]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Int.fract_nonneg t), norm_cpow_eq_rpow_re_of_pos htpos]
      have hre : (-(s + 1)).re = -s.re - 1 := by simp; ring
      rw [hre]
      exact mul_le_of_le_one_left (Real.rpow_nonneg htpos.le _)
        (Int.fract_lt_one t).le
  have hmaj : IntegrableOn (fun t : ℝ => t ^ (-s.re - 1)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  calc
    ‖∫ t : ℝ in Ioi 1,
        ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))‖ ≤
      ∫ t : ℝ in Ioi 1,
        ‖((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ in Ioi 1, t ^ (-s.re - 1) := by
      apply integral_mono_ae hfracInt.norm hmaj
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have htpos : 0 < t := by linarith [mem_Ioi.mp ht]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Int.fract_nonneg t), norm_cpow_eq_rpow_re_of_pos htpos]
      have hre : (-(s + 1)).re = -s.re - 1 := by simp; ring
      rw [hre]
      exact mul_le_of_le_one_left (Real.rpow_nonneg htpos.le _)
        (Int.fract_lt_one t).le
    _ = (1 : ℝ) / s.re := by
      rw [integral_Ioi_rpow_of_lt (by linarith) one_pos]
      simp only [Real.one_rpow]
      have hden : -s.re - 1 + 1 = -s.re := by ring
      rw [hden]
      field_simp

/-- A direct norm estimate for the zeta function away from its pole, retaining
the two denominators which will be bounded separately on a contour strip. -/
theorem norm_riemannZeta_le_fractionalPart_formula
    {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ‖riemannZeta s‖ ≤
      ‖s‖ / ‖s - 1‖ + ‖s‖ / s.re := by
  rw [riemannZeta_eq_fractionalPart_formula_of_pos_re hs hs1]
  calc
    ‖s / (s - 1) - s * mellin zetaFractionalPart (-s)‖ ≤
        ‖s / (s - 1)‖ + ‖s * mellin zetaFractionalPart (-s)‖ := norm_sub_le _ _
    _ = ‖s‖ / ‖s - 1‖ + ‖s‖ * ‖mellin zetaFractionalPart (-s)‖ := by
      simp [norm_div]
    _ ≤ ‖s‖ / ‖s - 1‖ + ‖s‖ * ((1 : ℝ) / s.re) := by
      gcongr
      exact norm_mellin_zetaFractionalPart_le hs
    _ = ‖s‖ / ‖s - 1‖ + ‖s‖ / s.re := by ring

/-- The actual Riemann zeta function grows at most linearly in height on
the critical line, with an absolute explicit constant. -/
theorem norm_riemannZeta_le_on_critical_line
    {s : ℂ} (hs : s.re = 1 / 2) :
    ‖riemannZeta s‖ ≤ 1 + 2 * ‖s‖ := by
  have hpos : 0 < s.re := by rw [hs]; norm_num
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hregular := zetaPoleRemoved_eq_regularizedAbel_of_pos_re hpos
  rw [zetaPoleRemoved_eq_mul_riemannZeta hs0 hs1] at hregular
  have hformula : riemannZeta s = s / (s - 1) - s * mellin zetaFractionalPart (-s) := by
    apply (mul_left_cancel₀ (sub_ne_zero.mpr hs1))
    calc
      (s - 1) * riemannZeta s = s - s * (s - 1) * mellin zetaFractionalPart (-s) := hregular
      _ = (s - 1) * (s / (s - 1) -
          s * mellin zetaFractionalPart (-s)) := by
        field_simp [sub_ne_zero.mpr hs1]
  have hM : ‖mellin zetaFractionalPart (-s)‖ ≤ (1 : ℝ) / s.re := by
    rw [mellin_zetaFractionalPart_eq_integral hpos]
    have hfracInt : IntegrableOn
        (fun t : ℝ => ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) (Ioi 1) := by
      have hmaj : IntegrableOn (fun t : ℝ => t ^ (-s.re - 1)) (Ioi 1) :=
        integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
      apply Integrable.mono' hmaj
      · have hfloor : Measurable (fun t : ℝ => (Int.floor t : ℝ)) :=
          (measurable_of_countable (fun n : ℤ => (n : ℝ))).comp Int.measurable_floor
        have hfractReal : Measurable (fun t : ℝ => Int.fract t) := by
          change Measurable (fun t : ℝ => t - (Int.floor t : ℝ))
          exact measurable_id.sub hfloor
        have hfract : Measurable (fun t : ℝ => ((Int.fract t : ℝ) : ℂ)) :=
          Complex.continuous_ofReal.measurable.comp hfractReal
        have hkernel : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-(s + 1))) (Ioi 1) := by
          intro t ht
          exact (Complex.continuousAt_ofReal_cpow_const t (-(s + 1))
            (Or.inr (by linarith [mem_Ioi.mp ht]))).continuousWithinAt
        exact hfract.aestronglyMeasurable.mul
          (hkernel.aestronglyMeasurable measurableSet_Ioi)
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have htpos : 0 < t := by linarith [mem_Ioi.mp ht]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Int.fract_nonneg t), norm_cpow_eq_rpow_re_of_pos htpos]
        have hre : (-(s + 1)).re = -s.re - 1 := by simp; ring
        rw [hre]
        exact mul_le_of_le_one_left (Real.rpow_nonneg htpos.le _) (Int.fract_lt_one t).le
    have hmaj : IntegrableOn (fun t : ℝ => t ^ (-s.re - 1)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
    calc
      ‖∫ t : ℝ in Ioi 1,
          ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))‖ ≤
        ∫ t : ℝ in Ioi 1,
          ‖((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t : ℝ in Ioi 1, t ^ (-s.re - 1) := by
        apply integral_mono_ae hfracInt.norm hmaj
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have htpos : 0 < t := by linarith [mem_Ioi.mp ht]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Int.fract_nonneg t), norm_cpow_eq_rpow_re_of_pos htpos]
        have hre : (-(s + 1)).re = -s.re - 1 := by simp; ring
        rw [hre]
        exact mul_le_of_le_one_left (Real.rpow_nonneg htpos.le _) (Int.fract_lt_one t).le
      _ = (1 : ℝ) / s.re := by
        rw [integral_Ioi_rpow_of_lt (by linarith) one_pos]
        simp only [Real.one_rpow]
        have hden : -s.re - 1 + 1 = -s.re := by ring
        rw [hden]
        field_simp
  calc
    ‖riemannZeta s‖ = ‖s / (s - 1) - s * mellin zetaFractionalPart (-s)‖ := by rw [hformula]
    _ ≤ ‖s / (s - 1)‖ + ‖s * mellin zetaFractionalPart (-s)‖ := norm_sub_le _ _
    _ = ‖s‖ / ‖s - 1‖ + ‖s‖ * ‖mellin zetaFractionalPart (-s)‖ := by simp [norm_div]
    _ ≤ 1 + 2 * ‖s‖ := by
      have hnormsq : Complex.normSq (s - 1) = Complex.normSq s := by
        rw [Complex.normSq_apply, Complex.normSq_apply]
        simp [Complex.sub_re, Complex.sub_im, hs]
        ring
      have hnorm : ‖s - 1‖ = ‖s‖ := by
        have hsq : ‖s - 1‖ ^ 2 = ‖s‖ ^ 2 := by
          rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
          exact hnormsq
        nlinarith [norm_nonneg (s - 1), norm_nonneg s, hsq]
      rw [hnorm]
      have hsnorm : 0 < ‖s‖ := norm_pos_iff.mpr hs0
      rw [div_self hsnorm.ne']
      have hM' : ‖mellin zetaFractionalPart (-s)‖ ≤ 2 := by
        rw [hs] at hM
        norm_num at hM ⊢
        exact hM
      have hprod := mul_le_mul_of_nonneg_left hM' (norm_nonneg s)
      nlinarith [hprod]

end ZhangLS.Spec
