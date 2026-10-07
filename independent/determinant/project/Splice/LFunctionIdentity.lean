import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
# The value at one as an ordered character sum

The `LSeries` object in mathlib is an unconditionally summed series. At one it
is not the Dirichlet L-function. This file passes from the absolutely convergent
half-plane to the Abel integral by dominated convergence and continuity of the
actual `DirichletCharacter.LFunction`.

All coefficient estimates are explicit finite-sum hypotheses. They are supplied
by periodicity and nonprincipality in `CharacterArithmetic.lean`.
-/

noncomputable section

open Finset Filter MeasureTheory Complex Asymptotics
open scoped Topology

namespace Splice

/-- The ordered partial coefficient sum, with a real cutoff. -/
def characterPartialSum {D : ℕ} (χ : DirichletCharacter ℂ D) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ k

/-- Integrand in the Abel representation on the real axis. -/
def characterAbelIntegrand {D : ℕ} (χ : DirichletCharacter ℂ D) (s t : ℝ) : ℂ :=
  characterPartialSum χ t * (t : ℂ) ^ (-((s : ℂ) + 1))

/-- A genuinely ordered finite harmonic sum, not a `tsum`. -/
def characterHarmonicSum {D : ℕ} (χ : DirichletCharacter ℂ D) (T : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 ⌊T⌋₊, χ k / (k : ℂ)

lemma measurable_characterPartialSum {D : ℕ} (χ : DirichletCharacter ℂ D) :
    Measurable (characterPartialSum χ) := by
  exact (measurable_of_countable (fun n : ℕ ↦
    ∑ k ∈ Finset.Icc 1 n, χ k)).comp Nat.measurable_floor

lemma characterAbelIntegrand_aestronglyMeasurable {D : ℕ}
    (χ : DirichletCharacter ℂ D) (s : ℝ) {a : ℝ} (ha : 0 < a) :
    AEStronglyMeasurable (characterAbelIntegrand χ s) (volume.restrict (Set.Ioi a)) := by
  refine (measurable_characterPartialSum χ).aestronglyMeasurable.mul ?_
  refine ContinuousOn.aestronglyMeasurable (fun t ht ↦ ?_) measurableSet_Ioi
  exact (continuousAt_ofReal_cpow_const _ _
    (Or.inr (ha.trans ht).ne')).continuousWithinAt

lemma norm_characterAbelIntegrand_le {D : ℕ} (χ : DirichletCharacter ℂ D)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n : ℕ, ‖∑ k ∈ Finset.Icc 1 n, χ k‖ ≤ C)
    {s t : ℝ} (hs : 1 ≤ s) (ht : 1 ≤ t) :
    ‖characterAbelIntegrand χ s t‖ ≤ C * t ^ (-2 : ℝ) := by
  rw [characterAbelIntegrand, norm_mul,
    norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le ht)]
  simp only [neg_re, add_re, ofReal_re, one_re]
  exact mul_le_mul (hbound _) (Real.rpow_le_rpow_of_exponent_le ht (by linarith))
    (Real.rpow_nonneg (zero_le_one.trans ht) _) hC

lemma characterAbelIntegrand_one_integrableOn {D : ℕ}
    (χ : DirichletCharacter ℂ D) {C a : ℝ}
    (hbound : ∀ n : ℕ, ‖∑ k ∈ Finset.Icc 1 n, χ k‖ ≤ C) (ha : 0 < a) :
    IntegrableOn (characterAbelIntegrand χ 1) (Set.Ioi a) := by
  refine ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) ha).const_mul C).mono'
    (characterAbelIntegrand_aestronglyMeasurable χ 1 ha) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht ↦ ?_)
  rw [characterAbelIntegrand, norm_mul, norm_cpow_eq_rpow_re_of_pos (ha.trans ht)]
  norm_num only [ofReal_one, neg_re, add_re, one_re]
  exact mul_le_mul_of_nonneg_right (hbound _) (Real.rpow_nonneg (ha.trans ht).le _)

/-- A nonprincipal character's actual L-function value is its Abel integral.
This uses neither nonvanishing nor a zero-free region. -/
theorem LFunction_one_eq_abelIntegral {D : ℕ} [NeZero D]
    (χ : DirichletCharacter ℂ D) (hne : χ ≠ 1)
    (hbound : ∀ n : ℕ, ‖∑ k ∈ Finset.Icc 1 n, χ k‖ ≤ (D : ℝ)) :
    χ.LFunction 1 = ∫ t in Set.Ioi (1 : ℝ), characterAbelIntegrand χ 1 t := by
  let σ : ℕ → ℝ := fun n ↦ 1 + 1 / ((n : ℝ) + 1)
  have hσgt (n : ℕ) : 1 < σ n := by
    dsimp [σ]
    exact lt_add_of_pos_right 1 (by positivity)
  have hσlim : Tendsto σ atTop (𝓝 1) := by
    simpa [σ] using (tendsto_const_nhds (x := (1 : ℝ))).add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hσlimC : Tendsto (fun n ↦ (σ n : ℂ)) atTop (𝓝 1) := by
    simpa using hσlim.ofReal
  have hO : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, χ k) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (0 : ℝ)) := by
    refine isBigO_iff.mpr ⟨(D : ℝ), Filter.Eventually.of_forall fun n ↦ ?_⟩
    simpa using hbound n
  have heq (n : ℕ) : χ.LFunction (σ n : ℂ) =
      (σ n : ℂ) * ∫ t in Set.Ioi (1 : ℝ), characterAbelIntegrand χ (σ n) t := by
    rw [χ.LFunction_eq_LSeries (by simpa using hσgt n)]
    exact LSeries_eq_mul_integral _ (r := 0) le_rfl
      (by simpa using zero_lt_one.trans (hσgt n))
      (χ.LSeriesSummable_of_one_lt_re (by simpa using hσgt n)) hO
  have hint : Tendsto (fun n ↦ ∫ t in Set.Ioi (1 : ℝ),
      characterAbelIntegrand χ (σ n) t) atTop
      (𝓝 (∫ t in Set.Ioi (1 : ℝ), characterAbelIntegrand χ 1 t)) := by
    apply tendsto_integral_of_dominated_convergence (fun t : ℝ ↦ (D : ℝ) * t ^ (-2 : ℝ))
    · exact fun n ↦ characterAbelIntegrand_aestronglyMeasurable χ (σ n) zero_lt_one
    · exact (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1)
        zero_lt_one).const_mul (D : ℝ)
    · intro n
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht ↦ ?_)
      exact norm_characterAbelIntegrand_le χ (Nat.cast_nonneg D) hbound (hσgt n).le ht.le
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht ↦ ?_)
      exact tendsto_const_nhds.mul <| (hσlimC.add_const 1).neg.const_cpow
        (Or.inl (ofReal_ne_zero.mpr (zero_lt_one.trans ht).ne'))
  have hL : Tendsto (fun n ↦ χ.LFunction (σ n : ℂ)) atTop (𝓝 (χ.LFunction 1)) :=
    (DirichletCharacter.differentiable_LFunction hne).continuous.continuousAt.tendsto.comp hσlimC
  exact tendsto_nhds_unique hL (by
    simpa only [one_mul, ← heq] using hσlimC.mul hint)

/-- Norm of the integral tail, with the sharp elementary majorant `C / T`. -/
lemma norm_characterAbelIntegral_tail_le {D : ℕ} (χ : DirichletCharacter ℂ D)
    {C T : ℝ} (hbound : ∀ n : ℕ, ‖∑ k ∈ Finset.Icc 1 n, χ k‖ ≤ C)
    (hT : 0 < T) :
    ‖∫ t in Set.Ioi T, characterAbelIntegrand χ 1 t‖ ≤ C / T := by
  calc
    _ ≤ ∫ t in Set.Ioi T, C * t ^ (-2 : ℝ) := by
      apply norm_integral_le_of_norm_le
        ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hT).const_mul C)
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht ↦ ?_)
      rw [characterAbelIntegrand, norm_mul, norm_cpow_eq_rpow_re_of_pos (hT.trans ht)]
      norm_num only [ofReal_one, neg_re, add_re, one_re]
      exact mul_le_mul_of_nonneg_right (hbound _) (Real.rpow_nonneg (hT.trans ht).le _)
    _ = C / T := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hT]
      norm_num [Real.rpow_neg_one, div_eq_mul_inv]

private lemma character_sum_zero_eq {D : ℕ} (χ : DirichletCharacter ℂ D)
    (hne : χ ≠ 1) (n : ℕ) :
    (∑ k ∈ Finset.Icc 0 n, χ k) = ∑ k ∈ Finset.Icc 1 n, χ k := by
  have hz : χ (0 : ZMod D) = 0 := χ.map_zero' (fun h ↦ hne (χ.level_one' h))
  rw [Icc_eq_cons_Ioc n.zero_le, sum_cons, ← Icc_add_one_left_eq_Ioc, zero_add]
  simpa only [Nat.cast_zero, hz, zero_add]

/-- Exact finite Abel summation, valid for every real cutoff at least one. -/
theorem characterHarmonicSum_eq_abel {D : ℕ} (χ : DirichletCharacter ℂ D)
    (hne : χ ≠ 1) {T : ℝ} (hT : 1 ≤ T) :
    characterHarmonicSum χ T = characterPartialSum χ T / (T : ℂ) +
      ∫ t in Set.Ioc (1 : ℝ) T, characterAbelIntegrand χ 1 t := by
  have hz : χ (0 : ZMod D) = 0 := χ.map_zero' (fun h ↦ hne (χ.level_one' h))
  have hdiff (t : ℝ) (ht : t ∈ Set.Icc 1 T) :
      DifferentiableAt ℝ (fun x : ℝ ↦ (x : ℂ) ^ (-1 : ℂ)) t :=
    differentiableAt_id.ofReal_cpow_const (zero_lt_one.trans_le ht.1).ne' (by norm_num)
  have hint : IntegrableOn (deriv fun x : ℝ ↦ (x : ℂ) ^ (-1 : ℂ)) (Set.Icc 1 T) := by
    exact (Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi
      (integrableOn_Ioi_deriv_ofReal_cpow zero_lt_one (by norm_num : (-1 : ℂ).re < 0))).mono_set
      Set.Icc_subset_Ici_self
  have hform := sum_mul_eq_sub_integral_mul₀ (fun n : ℕ ↦ χ n)
    (by simpa using hz) T hdiff hint
  have hsum : (∑ k ∈ Finset.Icc 0 ⌊T⌋₊, (k : ℂ) ^ (-1 : ℂ) * χ k) =
      characterHarmonicSum χ T := by
    rw [Icc_eq_cons_Ioc (Nat.zero_le _), sum_cons, ← Icc_add_one_left_eq_Ioc, zero_add]
    simp only [Nat.cast_zero, zero_cpow (by norm_num : (-1 : ℂ) ≠ 0), zero_mul, zero_add]
    exact Finset.sum_congr rfl fun k hk ↦ by
      rw [cpow_neg_one, div_eq_mul_inv, mul_comm]
  have hint_eq :
      (∫ t in Set.Ioc (1 : ℝ) T,
        deriv (fun x : ℝ ↦ (x : ℂ) ^ (-1 : ℂ)) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, χ k) =
        -(∫ t in Set.Ioc (1 : ℝ) T, characterAbelIntegrand χ 1 t) := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht ↦ ?_
    rw [deriv_ofReal_cpow_const (zero_lt_one.trans ht.1).ne' (by norm_num),
      character_sum_zero_eq χ hne]
    dsimp [characterAbelIntegrand, characterPartialSum]
    norm_num
    ring
  simp only [Complex.ofReal_natCast] at hform
  rw [hsum, hint_eq, character_sum_zero_eq χ hne, cpow_neg_one] at hform
  simpa only [characterPartialSum, div_eq_mul_inv, mul_comm, sub_neg_eq_add] using hform

/-- Exact ordered tail of the actual L-function, with a real cutoff. -/
theorem LFunction_one_sub_characterHarmonicSum {D : ℕ} [NeZero D]
    (χ : DirichletCharacter ℂ D) (hne : χ ≠ 1)
    (hbound : ∀ n : ℕ, ‖∑ k ∈ Finset.Icc 1 n, χ k‖ ≤ (D : ℝ))
    {T : ℝ} (hT : 1 ≤ T) :
    χ.LFunction 1 - characterHarmonicSum χ T =
      -(characterPartialSum χ T / (T : ℂ)) +
        ∫ t in Set.Ioi T, characterAbelIntegrand χ 1 t := by
  have hi := characterAbelIntegrand_one_integrableOn χ hbound zero_lt_one
  have hsplit := intervalIntegral.integral_interval_add_Ioi hi
    (hi.mono_set (Set.Ioi_subset_Ioi hT))
  rw [intervalIntegral.integral_of_le hT] at hsplit
  rw [LFunction_one_eq_abelIntegral χ hne hbound, characterHarmonicSum_eq_abel χ hne hT,
    ← hsplit]
  ring

/-- The elementary tail bound is for the actual L-function, not the junk-valued
unconditionally summed `LSeries` at one. -/
theorem norm_LFunction_one_sub_characterHarmonicSum_le {D : ℕ} [NeZero D]
    (χ : DirichletCharacter ℂ D) (hne : χ ≠ 1)
    (hbound : ∀ n : ℕ, ‖∑ k ∈ Finset.Icc 1 n, χ k‖ ≤ (D : ℝ))
    {T : ℝ} (hT : 0 < T) :
    ‖χ.LFunction 1 - characterHarmonicSum χ T‖ ≤ 2 * (D : ℝ) / T := by
  by_cases hT1 : 1 ≤ T
  · rw [LFunction_one_sub_characterHarmonicSum χ hne hbound hT1]
    calc
      _ ≤ ‖-(characterPartialSum χ T / (T : ℂ))‖ +
          ‖∫ t in Set.Ioi T, characterAbelIntegrand χ 1 t‖ := norm_add_le _ _
      _ ≤ (D : ℝ) / T + (D : ℝ) / T := by
        apply add_le_add
        · rw [norm_neg, norm_div, norm_real, Real.norm_of_nonneg hT.le]
          exact div_le_div_of_nonneg_right (hbound _) hT.le
        · exact norm_characterAbelIntegral_tail_le χ hbound hT
      _ = 2 * (D : ℝ) / T := by ring
  · have hsmall : T < 1 := lt_of_not_ge hT1
    have hempty : characterHarmonicSum χ T = 0 := by
      simp [characterHarmonicSum, Nat.floor_eq_zero.mpr hsmall]
    rw [hempty, sub_zero, LFunction_one_eq_abelIntegral χ hne hbound]
    calc
      _ ≤ (D : ℝ) / 1 := norm_characterAbelIntegral_tail_le χ hbound zero_lt_one
      _ ≤ 2 * (D : ℝ) / T := by
        rw [div_one, le_div_iff₀ hT]
        nlinarith [(Nat.cast_nonneg D : (0 : ℝ) ≤ (D : ℝ))]

/-- Real-part version used in the Dirichlet-hyperbola estimate. -/
theorem abs_characterHarmonicSum_re_sub_LFunction_one_le {D : ℕ} [NeZero D]
    (χ : DirichletCharacter ℂ D) (hne : χ ≠ 1)
    (hbound : ∀ n : ℕ, ‖∑ k ∈ Finset.Icc 1 n, χ k‖ ≤ (D : ℝ))
    {T : ℝ} (hT : 0 < T) :
    |(∑ k ∈ Finset.Icc 1 ⌊T⌋₊, (χ k).re / (k : ℝ)) - (χ.LFunction 1).re| ≤
      2 * (D : ℝ) / T := by
  have h := (abs_re_le_norm (χ.LFunction 1 - characterHarmonicSum χ T)).trans
    (norm_LFunction_one_sub_characterHarmonicSum_le χ hne hbound hT)
  simpa [characterHarmonicSum, map_sum, div_natCast_re, abs_sub_comm] using h

/-- Ordinary ordered partial sums converge to the analytic L-function value.
This is deliberately a `Tendsto` statement rather than `HasSum`. -/
theorem tendsto_characterHarmonicSum {D : ℕ} [NeZero D]
    (χ : DirichletCharacter ℂ D) (hne : χ ≠ 1)
    (hbound : ∀ n : ℕ, ‖∑ k ∈ Finset.Icc 1 n, χ k‖ ≤ (D : ℝ)) :
    Tendsto (characterHarmonicSum χ) atTop (𝓝 (χ.LFunction 1)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _) ?_
    ((tendsto_id : Tendsto (fun T : ℝ ↦ T) atTop atTop).const_div_atTop (2 * (D : ℝ)))
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  simpa only [norm_sub_rev, id_eq] using
    norm_LFunction_one_sub_characterHarmonicSum_le χ hne hbound hT

/-- The analytic L-function value at one is real for a real-valued character. -/
theorem LFunction_one_im_eq_zero {D : ℕ} [NeZero D]
    (χ : DirichletCharacter ℂ D) (hne : χ ≠ 1)
    (hbound : ∀ n : ℕ, ‖∑ k ∈ Finset.Icc 1 n, χ k‖ ≤ (D : ℝ))
    (hreal : ∀ x : ZMod D, (χ x).im = 0) :
    (χ.LFunction 1).im = 0 := by
  have hlim := (Complex.continuous_im.tendsto (χ.LFunction 1)).comp
    (tendsto_characterHarmonicSum χ hne hbound)
  have hz (T : ℝ) : (characterHarmonicSum χ T).im = 0 := by
    simp [characterHarmonicSum, hreal]
  simp only [Function.comp_def, hz] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

/-- Coercion form for downstream hypotheses stated with a real L-value. -/
theorem LFunction_one_eq_ofReal_re {D : ℕ} [NeZero D]
    (χ : DirichletCharacter ℂ D) (hne : χ ≠ 1)
    (hbound : ∀ n : ℕ, ‖∑ k ∈ Finset.Icc 1 n, χ k‖ ≤ (D : ℝ))
    (hreal : ∀ x : ZMod D, (χ x).im = 0) :
    χ.LFunction 1 = ((χ.LFunction 1).re : ℂ) := by
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using LFunction_one_im_eq_zero χ hne hbound hreal

end Splice
