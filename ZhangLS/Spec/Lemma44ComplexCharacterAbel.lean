import ZhangLS.Spec.CharacterAbelAnalyticContinuation

/-!
# Effective Abel bounds for nontrivial complex Dirichlet characters

The auxiliary bundle records only a genuine character, nontriviality and a
positive modulus. No growth estimate is a field. Complete-period cancellation,
Abel integrability, Mellin analytic continuation and the actual L-function
bound are proved below, reusing the real-character argument without its
unused reality or quadratic hypotheses.
-/

namespace ZhangLS.Spec

open Complex

set_option maxHeartbeats 1000000

structure Lemma44ComplexCharacter (D : ℕ) where
  chi : DirichletCharacter ℂ D
  nontrivial : chi ≠ 1
  modulus_pos : 0 < D

noncomputable def Lemma44ComplexCharacter.evalNat {D : ℕ}
    (χ : Lemma44ComplexCharacter D) (n : ℕ) : ℂ := χ.chi (n : ZMod D)

theorem Lemma44ComplexCharacter.modulus_ne_zero {D : ℕ}
    (χ : Lemma44ComplexCharacter D) : D ≠ 0 := Nat.ne_of_gt χ.modulus_pos

/-- The coefficient sequence attached to a nontrivial complex Dirichlet character. -/
noncomputable def lemma44ComplexDirichletCoeffs {D : ℕ} (χ : Lemma44ComplexCharacter D) : ℕ → ℂ :=
  fun n => χ.chi (n : ZMod D)

/-- The naive Dirichlet L-series.  It is used only in its convergence region. -/
noncomputable def lemma44ComplexDirichletLSeries {D : ℕ} (χ : Lemma44ComplexCharacter D) (s : ℂ) : ℂ :=
  LSeries (lemma44ComplexDirichletCoeffs χ) s

/-- Absolute convergence of the naive Dirichlet L-series on `re(s) > 1`. -/
theorem lemma44ComplexDirichletLSeries_summable_of_one_lt_re {D : ℕ}
    (χ : Lemma44ComplexCharacter D) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (lemma44ComplexDirichletCoeffs χ) s := by
  exact χ.chi.LSeriesSummable_of_one_lt_re hs

/-- The analytically continued Dirichlet L-function supplied by mathlib. -/
noncomputable def lemma44ComplexDirichletLFunction {D : ℕ} (χ : Lemma44ComplexCharacter D) (s : ℂ) : ℂ := by
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  exact χ.chi.LFunction s

/-- In the half-plane of absolute convergence, the analytic L-function agrees
with the naive L-series. -/
theorem lemma44ComplexDirichletLFunction_eq_series {D : ℕ} (χ : Lemma44ComplexCharacter D)
    {s : ℂ} (hs : 1 < s.re) :
    lemma44ComplexDirichletLFunction χ s = lemma44ComplexDirichletLSeries χ s := by
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  simpa [lemma44ComplexDirichletLFunction, lemma44ComplexDirichletLSeries, lemma44ComplexDirichletCoeffs] using
    (χ.chi.LFunction_eq_LSeries hs)


theorem differentiable_lemma44ComplexDirichletLFunction_of_one_lt_modulus {D : ℕ}
    (χ : Lemma44ComplexCharacter D) (_hD : 1 < D) :
    Differentiable ℂ (lemma44ComplexDirichletLFunction χ) := by
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  simpa [lemma44ComplexDirichletLFunction] using
    DirichletCharacter.differentiable_LFunction χ.nontrivial



open Finset

/-- A nontrivial complex character of modulus greater than one has zero mean
over a complete residue system. -/
theorem Lemma44ComplexCharacter.sum_one_period_eq_zero
    {D : ℕ} [NeZero D] (χ : Lemma44ComplexCharacter D) (hD : 1 < D) :
    ∑ a : ZMod D, χ.chi a = 0 := by
  exact χ.chi.sum_eq_zero_of_ne_one (χ.nontrivial)

/-- The norm of every value of a Dirichlet character is at most one. -/
theorem Lemma44ComplexCharacter.evalNat_norm_le_one
    {D : ℕ} (χ : Lemma44ComplexCharacter D) (n : ℕ) :
    ‖χ.evalNat n‖ ≤ 1 := by
  simpa [Lemma44ComplexCharacter.evalNat] using χ.chi.norm_le_one (n : ZMod D)

/-- The natural-number evaluations cancel on the first complete period. -/
theorem Lemma44ComplexCharacter.sum_evalNat_one_period_eq_zero
    {D : ℕ} [NeZero D] (χ : Lemma44ComplexCharacter D) (hD : 1 < D) :
    ∑ n ∈ range D, χ.evalNat n = 0 := by
  rw [← Fin.sum_univ_eq_sum_range]
  calc
    ∑ n : Fin D, χ.evalNat n = ∑ a : ZMod D, χ.chi a := by
      apply Fintype.sum_equiv (ZMod.finEquiv D).toEquiv
      intro n
      cases D with
      | zero => exact (NeZero.ne 0 rfl).elim
      | succ d =>
          change χ.chi ((n.val : ℕ) : ZMod (d + 1)) = χ.chi n
          exact congrArg χ.chi (Fin.cast_val_eq_self n)
    _ = 0 := χ.sum_one_period_eq_zero hD

/-- A complete period cancels regardless of where it starts, provided the
starting point is a multiple of the modulus. -/
theorem Lemma44ComplexCharacter.sum_evalNat_block_eq_zero
    {D : ℕ} [NeZero D] (χ : Lemma44ComplexCharacter D) (hD : 1 < D)
    (k : ℕ) :
    ∑ n ∈ range D, χ.evalNat (k * D + n) = 0 := by
  have hterm : ∀ n : ℕ, χ.evalNat (k * D + n) = χ.evalNat n := by
    intro n
    simp [Lemma44ComplexCharacter.evalNat, Nat.cast_add, Nat.cast_mul]
  simp_rw [hterm]
  exact χ.sum_evalNat_one_period_eq_zero hD

/-- The partial sums of a nontrivial nontrivial character are bounded by its
modulus, uniformly in the length of the sum. -/
theorem Lemma44ComplexCharacter.norm_sum_evalNat_le_modulus
    {D : ℕ} (χ : Lemma44ComplexCharacter D) (hD : 1 < D) (N : ℕ) :
    ‖∑ n ∈ range N, χ.evalNat n‖ ≤ (D : ℝ) := by
  letI : NeZero D := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt hD)⟩
  have hfull : ∀ k : ℕ, ∑ n ∈ range (k * D), χ.evalNat n = 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Nat.succ_mul, Finset.sum_range_add, ih,
          χ.sum_evalNat_block_eq_zero hD k]
        simp
  have hrem (r : ℕ) : ‖∑ n ∈ range r, χ.evalNat n‖ ≤ (r : ℝ) := by
    calc
      ‖∑ n ∈ range r, χ.evalNat n‖ ≤
          ∑ n ∈ range r, ‖χ.evalNat n‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ range r, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro n _
        exact χ.evalNat_norm_le_one n
      _ = r := by simp
  have hsplit : N = (N / D) * D + N % D := by
    simpa [Nat.mul_comm, Nat.add_comm] using (Nat.mod_add_div N D).symm
  rw [hsplit, Finset.sum_range_add, hfull, zero_add]
  have hshift : ∀ n : ℕ,
      χ.evalNat ((N / D) * D + n) = χ.evalNat n := by
    intro n
    simp [Lemma44ComplexCharacter.evalNat, Nat.cast_add, Nat.cast_mul]
  simp_rw [hshift]
  exact (hrem (N % D)).trans (by exact_mod_cast (Nat.mod_lt N χ.modulus_pos).le)



open Finset Complex MeasureTheory Asymptotics
open scoped Real

/-- The standard coefficient sums used in Abel summation have norm at most
the character modulus. -/
theorem Lemma44ComplexCharacter.norm_sum_Icc_evalNat_le_modulus
    {D : ℕ} (χ : Lemma44ComplexCharacter D) (hD : 1 < D) (N : ℕ) :
    ‖∑ n ∈ Icc 1 N, χ.evalNat n‖ ≤ (D : ℝ) := by
  letI : Fact (1 < D) := ⟨hD⟩
  have hzero : χ.evalNat 0 = 0 := by
    simp [Lemma44ComplexCharacter.evalNat, χ.chi.map_zero]
  have hsum : (∑ n ∈ Icc 1 N, χ.evalNat n) =
      ∑ n ∈ range (N + 1), χ.evalNat n := by
    rw [Nat.range_succ_eq_Icc_zero, Icc_eq_cons_Ioc (Nat.zero_le N),
      sum_cons, hzero, zero_add]
    rw [← Icc_add_one_left_eq_Ioc]
    simp
  rw [hsum]
  exact χ.norm_sum_evalNat_le_modulus hD (N + 1)

/-- Complete-period cancellation supplies the O(1) input for Abel
summation, with an explicit bound D. -/
theorem Lemma44ComplexCharacter.sum_Icc_evalNat_isBigO_one
    {D : ℕ} (χ : Lemma44ComplexCharacter D) (hD : 1 < D) :
    (fun N : ℕ => ∑ n ∈ Icc 1 N, χ.evalNat n) =O[Filter.atTop]
      (fun _N : ℕ => (1 : ℝ)) := by
  exact isBigO_one_nat_atTop_iff.mpr
    ⟨(D : ℝ), fun N => χ.norm_sum_Icc_evalNat_le_modulus hD N⟩

/-- Abel summation gives an integral representation for the actual
Dirichlet L-function where its Dirichlet series converges absolutely.
Extending the identity to the larger right half-plane requires another
analytic argument. -/
theorem lemma44ComplexDirichletLFunction_eq_abelIntegral
    {D : ℕ} (χ : Lemma44ComplexCharacter D) (hD : 1 < D)
    {s : ℂ} (hs : 1 < s.re) :
    lemma44ComplexDirichletLFunction χ s =
      s * ∫ t in Set.Ioi (1 : ℝ),
        (∑ n ∈ Icc 1 ⌊t⌋₊, χ.evalNat n) * (t : ℂ) ^ (-(s + 1)) := by
  rw [lemma44ComplexDirichletLFunction_eq_series χ hs]
  have hsum : LSeriesSummable (fun n => χ.evalNat n) s := by
    simpa [Lemma44ComplexCharacter.evalNat, lemma44ComplexDirichletCoeffs] using
      lemma44ComplexDirichletLSeries_summable_of_one_lt_re χ hs
  have hO :
      (fun n : ℕ => ∑ k ∈ Icc 1 n, χ.evalNat k) =O[Filter.atTop]
        (fun n : ℕ => (n : ℝ) ^ (0 : ℝ)) := by
    simpa using χ.sum_Icc_evalNat_isBigO_one hD
  simpa [lemma44ComplexDirichletLSeries, lemma44ComplexDirichletCoeffs, Lemma44ComplexCharacter.evalNat] using
    (LSeries_eq_mul_integral (fun n => χ.evalNat n) (r := 0)
      (by norm_num) (by linarith) hsum hO)



open Finset Complex MeasureTheory Set
open scoped Real

/-- The Abel integral of the actual character coefficients. -/
noncomputable def lemma44ComplexAbelIntegral {D : ℕ}
    (χ : Lemma44ComplexCharacter D) (s : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi 1,
    (∑ n ∈ Icc 1 ⌊t⌋₊, χ.evalNat n) * (t : ℂ) ^ (-(s + 1))

/-- For positive real part, the Abel integrand has an explicit integrable
majorant: the modulus times a decaying real power. -/
theorem Lemma44ComplexCharacter.abelIntegrand_integrable
    {D : ℕ} (χ : Lemma44ComplexCharacter D) (hD : 1 < D)
    {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ =>
      (∑ n ∈ Icc 1 ⌊t⌋₊, χ.evalNat n) * (t : ℂ) ^ (-(s + 1))) (Ioi 1) := by
  have hmeas : Measurable (fun t : ℝ =>
      ∑ n ∈ Icc 1 ⌊t⌋₊, χ.evalNat n) :=
    (measurable_of_countable
      (fun N : ℕ => ∑ n ∈ Icc 1 N, χ.evalNat n)).comp Nat.measurable_floor
  have hkernel : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-(s + 1))) (Ioi 1) := by
    intro t ht
    exact (Complex.continuousAt_ofReal_cpow_const t (-(s + 1))
      (Or.inr (by linarith [mem_Ioi.mp ht]))).continuousWithinAt
  have hmaj : IntegrableOn
      (fun t : ℝ => (D : ℝ) * t ^ (-s.re - 1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)).const_mul _
  apply Integrable.mono' hmaj
  · exact hmeas.aestronglyMeasurable.mul
      (hkernel.aestronglyMeasurable measurableSet_Ioi)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : 0 < t := by linarith [mem_Ioi.mp ht]
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos htpos]
    have hre : (-(s + 1)).re = -s.re - 1 := by simp; ring
    rw [hre]
    exact mul_le_mul_of_nonneg_right
      (χ.norm_sum_Icc_evalNat_le_modulus hD ⌊t⌋₊)
      (Real.rpow_nonneg htpos.le _)

/-- The undamped Abel integral has a conductor-linear bound on the entire
open right half-plane. The denominator is the real part of `s`. -/
theorem Lemma44ComplexCharacter.norm_lemma44ComplexAbelIntegral_le
    {D : ℕ} (χ : Lemma44ComplexCharacter D) (hD : 1 < D)
    {s : ℂ} (hs : 0 < s.re) :
    ‖lemma44ComplexAbelIntegral χ s‖ ≤ (D : ℝ) / s.re := by
  have hint := χ.abelIntegrand_integrable hD hs
  have hmaj : IntegrableOn
      (fun t : ℝ => (D : ℝ) * t ^ (-s.re - 1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)).const_mul _
  unfold lemma44ComplexAbelIntegral
  calc
    ‖∫ t : ℝ in Ioi 1,
        (∑ n ∈ Icc 1 ⌊t⌋₊, χ.evalNat n) * (t : ℂ) ^ (-(s + 1))‖ ≤
      ∫ t : ℝ in Ioi 1,
        ‖(∑ n ∈ Icc 1 ⌊t⌋₊, χ.evalNat n) *
          (t : ℂ) ^ (-(s + 1))‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ in Ioi 1, (D : ℝ) * t ^ (-s.re - 1) := by
      apply integral_mono_ae hint.norm hmaj
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have htpos : 0 < t := by linarith [mem_Ioi.mp ht]
      rw [norm_mul, norm_cpow_eq_rpow_re_of_pos htpos]
      have hre : (-(s + 1)).re = -s.re - 1 := by simp; ring
      rw [hre]
      exact mul_le_mul_of_nonneg_right
        (χ.norm_sum_Icc_evalNat_le_modulus hD ⌊t⌋₊)
        (Real.rpow_nonneg htpos.le _)
    _ = (D : ℝ) / s.re := by
      rw [MeasureTheory.integral_const_mul,
        integral_Ioi_rpow_of_lt (by linarith : -s.re - 1 < -1)
          (by norm_num : (0 : ℝ) < 1)]
      simp only [Real.one_rpow]
      have hden : -s.re - 1 + 1 = -s.re := by ring
      rw [hden]
      ring

/-- The actual Dirichlet L-function has an explicit conductor-linear,
linear-in-height bound in the initial half-plane of absolute convergence. -/
theorem Lemma44ComplexCharacter.norm_lemma44ComplexDirichletLFunction_le_of_one_lt_re
    {D : ℕ} (χ : Lemma44ComplexCharacter D) (hD : 1 < D)
    {s : ℂ} (hs : 1 < s.re) :
    ‖lemma44ComplexDirichletLFunction χ s‖ ≤ ‖s‖ * ((D : ℝ) / s.re) := by
  rw [lemma44ComplexDirichletLFunction_eq_abelIntegral χ hD hs]
  change ‖s * lemma44ComplexAbelIntegral χ s‖ ≤ ‖s‖ * ((D : ℝ) / s.re)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (χ.norm_lemma44ComplexAbelIntegral_le hD (by linarith)) (norm_nonneg _)



open Filter MeasureTheory Set Asymptotics Finset Complex
open scoped Real Topology

/-- The character partial sum, cut off below the range of Abel summation. -/
noncomputable def lemma44ComplexAbelPartialSum {D : ℕ}
    (χ : Lemma44ComplexCharacter D) (t : ℝ) : ℂ :=
  if 1 < t then ∑ n ∈ Icc 1 ⌊t⌋₊, χ.evalNat n else 0

theorem Lemma44ComplexCharacter.lemma44ComplexAbelPartialSum_measurable
    {D : ℕ} (χ : Lemma44ComplexCharacter D) :
    Measurable (lemma44ComplexAbelPartialSum χ) := by
  have hsum : Measurable (fun t : ℝ => ∑ n ∈ Icc 1 ⌊t⌋₊, χ.evalNat n) :=
    (measurable_of_countable
      (fun N : ℕ => ∑ n ∈ Icc 1 N, χ.evalNat n)).comp Nat.measurable_floor
  exact Measurable.ite (p := fun t : ℝ => 1 < t) measurableSet_Ioi hsum measurable_const

theorem Lemma44ComplexCharacter.norm_lemma44ComplexAbelPartialSum_le
    {D : ℕ} (χ : Lemma44ComplexCharacter D) (hD : 1 < D) (t : ℝ) :
    ‖lemma44ComplexAbelPartialSum χ t‖ ≤ (D : ℝ) := by
  by_cases ht : 1 < t
  · simp [lemma44ComplexAbelPartialSum, ht]
    exact χ.norm_sum_Icc_evalNat_le_modulus hD ⌊t⌋₊
  · simp [lemma44ComplexAbelPartialSum, ht]

private theorem lemma44ComplexAbelPartialSum_locallyIntegrable
    {D : ℕ} (χ : Lemma44ComplexCharacter D) (hD : 1 < D) :
    LocallyIntegrableOn (lemma44ComplexAbelPartialSum χ) (Ioi 0) := by
  rw [locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed]
  intro K hKsub hKcompact
  have hconst : IntegrableOn (fun _ : ℝ => (D : ℝ)) K :=
    integrableOn_const hKcompact.measure_ne_top
  change Integrable (fun _ : ℝ => (D : ℝ)) (volume.restrict K) at hconst
  apply Integrable.mono' hconst
  · exact (χ.lemma44ComplexAbelPartialSum_measurable).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem hKcompact.measurableSet] with t ht
    exact χ.norm_lemma44ComplexAbelPartialSum_le hD t

private theorem lemma44ComplexAbelPartialSum_isBigO_atTop
    {D : ℕ} (χ : Lemma44ComplexCharacter D) (hD : 1 < D) :
    (lemma44ComplexAbelPartialSum χ) =O[atTop] (fun t : ℝ => t ^ (-(0 : ℝ))) := by
  rw [isBigO_iff]
  refine ⟨(D : ℝ), ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have hbound := χ.norm_lemma44ComplexAbelPartialSum_le hD t
  simpa using hbound

private theorem lemma44ComplexAbelPartialSum_isBigO_nhdsGT_zero
    {D : ℕ} (χ : Lemma44ComplexCharacter D) (b : ℝ) :
    (lemma44ComplexAbelPartialSum χ) =O[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => t ^ (-b)) := by
  rw [isBigO_iff]
  refine ⟨0, ?_⟩
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
  have hnot : ¬ 1 < t := by linarith [ht.2]
  simp [lemma44ComplexAbelPartialSum, hnot]

/-- The Mellin transform of the cutoff partial sum is exactly the Abel
integral on `(1,∞)`. -/
theorem lemma44ComplexAbelIntegral_eq_mellin
    {D : ℕ} (χ : Lemma44ComplexCharacter D) {s : ℂ} :
    lemma44ComplexAbelIntegral χ s = mellin (lemma44ComplexAbelPartialSum χ) (-s) := by
  unfold lemma44ComplexAbelIntegral mellin
  have hwhole :
      ∫ t : ℝ in Ioi 0,
        (t : ℂ) ^ ((-s) - 1) * lemma44ComplexAbelPartialSum χ t =
      ∫ t : ℝ in Ioi 1,
        (t : ℂ) ^ ((-s) - 1) * lemma44ComplexAbelPartialSum χ t := by
    apply setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
      (by intro t ht; exact lt_trans (by norm_num : (0 : ℝ) < 1) ht)
    intro t ht
    rcases ht with ⟨_, htcut⟩
    have htcut' : ¬ 1 < t := by simpa using htcut
    have hzero : lemma44ComplexAbelPartialSum χ t = 0 := by
      simp [lemma44ComplexAbelPartialSum, htcut']
    rw [hzero]
    simp
  calc
    (∫ t : ℝ in Ioi 1,
        (∑ n ∈ Finset.Icc 1 ⌊t⌋₊, χ.evalNat n) * (t : ℂ) ^ (-(s + 1))) =
      ∫ t : ℝ in Ioi 1,
        (t : ℂ) ^ ((-s) - 1) * lemma44ComplexAbelPartialSum χ t := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro t ht
          have ht' : 1 < t := ht
          rw [show -(s + 1) = (-s) - 1 by ring]
          simp [lemma44ComplexAbelPartialSum, ht', mul_comm]
    _ = ∫ t : ℝ in Ioi 0,
        (t : ℂ) ^ ((-s) - 1) * lemma44ComplexAbelPartialSum χ t := hwhole.symm
    _ = mellin (lemma44ComplexAbelPartialSum χ) (-s) := by
          rfl

/-- The Mellin expression multiplied by `s` is analytic throughout the
open right half-plane. -/
theorem lemma44ComplexAbelMellin_differentiableAt
    {D : ℕ} (χ : Lemma44ComplexCharacter D) (hD : 1 < D)
    {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ
      (fun z : ℂ => z * mellin (lemma44ComplexAbelPartialSum χ) (-z)) s := by
  let b : ℝ := (-s).re - 1
  have htop := lemma44ComplexAbelPartialSum_isBigO_atTop χ hD
  have hbot := lemma44ComplexAbelPartialSum_isBigO_nhdsGT_zero χ b
  have hs_top : (-s).re < 0 := by simp; linarith
  have hs_bot : b < (-s).re := by dsimp [b]; linarith
  have hmellin : DifferentiableAt ℂ (mellin (lemma44ComplexAbelPartialSum χ)) (-s) :=
    mellin_differentiableAt_of_isBigO_rpow
    (lemma44ComplexAbelPartialSum_locallyIntegrable χ hD) htop hs_top hbot hs_bot
  have hneg : DifferentiableAt ℂ (fun z : ℂ => -z) s := by fun_prop
  exact differentiableAt_id.mul (hmellin.comp s hneg)

private theorem lemma44ComplexAbelMellin_analyticOnNhd
    {D : ℕ} (χ : Lemma44ComplexCharacter D) (hD : 1 < D) :
    AnalyticOnNhd ℂ
      (fun z : ℂ => z * mellin (lemma44ComplexAbelPartialSum χ) (-z))
      {z : ℂ | 0 < z.re} := by
  refine DifferentiableOn.analyticOnNhd (fun z hz => ?_)
    (isOpen_lt continuous_const continuous_re)
  exact (lemma44ComplexAbelMellin_differentiableAt χ hD hz).differentiableWithinAt

private theorem lemma44ComplexDirichletLFunction_analyticOnNhd_rightHalfPlane
    {D : ℕ} (χ : Lemma44ComplexCharacter D) (hD : 1 < D) :
    AnalyticOnNhd ℂ (lemma44ComplexDirichletLFunction χ) {z : ℂ | 0 < z.re} := by
  refine DifferentiableOn.analyticOnNhd (fun z hz => ?_)
    (isOpen_lt continuous_const continuous_re)
  exact (differentiable_lemma44ComplexDirichletLFunction_of_one_lt_modulus χ hD).differentiableAt.differentiableWithinAt

/-- Analytic continuation of Abel summation: throughout `re s > 0`, the
actual analytically continued L-function equals `s` times the Abel integral. -/
theorem lemma44ComplexDirichletLFunction_eq_abelIntegral_of_pos_re
    {D : ℕ} (χ : Lemma44ComplexCharacter D) (hD : 1 < D)
    {s : ℂ} (hs : 0 < s.re) :
    lemma44ComplexDirichletLFunction χ s = s * lemma44ComplexAbelIntegral χ s := by
  let F : ℂ → ℂ := fun z => z * mellin (lemma44ComplexAbelPartialSum χ) (-z)
  let U : Set ℂ := {z : ℂ | 0 < z.re}
  have hF : AnalyticOnNhd ℂ F U := by
    simpa [F, U] using lemma44ComplexAbelMellin_analyticOnNhd χ hD
  have hL : AnalyticOnNhd ℂ (lemma44ComplexDirichletLFunction χ) U := by
    simpa [U] using lemma44ComplexDirichletLFunction_analyticOnNhd_rightHalfPlane χ hD
  have hpre : IsPreconnected U := by
    simpa [U] using (convex_halfSpace_re_gt 0).isPreconnected
  have htwo : (2 : ℂ) ∈ U := by norm_num [U]
  have hnear : F =ᶠ[𝓝 (2 : ℂ)] lemma44ComplexDirichletLFunction χ := by
    have hregion : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by norm_num)
    filter_upwards [hregion] with z hz
    have habel := lemma44ComplexDirichletLFunction_eq_abelIntegral χ hD hz
    calc
      F z = z * lemma44ComplexAbelIntegral χ z := by
        change z * mellin (lemma44ComplexAbelPartialSum χ) (-z) = _
        rw [lemma44ComplexAbelIntegral_eq_mellin χ]
      _ = lemma44ComplexDirichletLFunction χ z := habel.symm
  have hEq := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    hF hL hpre htwo hnear
  have hpoint := hEq (show s ∈ U by exact hs)
  have hpoint' : s * lemma44ComplexAbelIntegral χ s = lemma44ComplexDirichletLFunction χ s := by
    calc
      s * lemma44ComplexAbelIntegral χ s = s * mellin (lemma44ComplexAbelPartialSum χ) (-s) := by
        rw [lemma44ComplexAbelIntegral_eq_mellin χ]
      _ = F s := rfl
      _ = lemma44ComplexDirichletLFunction χ s := hpoint
  exact hpoint'.symm

/-- Explicit linear growth in height on the critical line (and more generally
on every fixed positive vertical line). -/
theorem Lemma44ComplexCharacter.norm_lemma44ComplexDirichletLFunction_le_of_pos_re
    {D : ℕ} (χ : Lemma44ComplexCharacter D) (hD : 1 < D)
    {s : ℂ} (hs : 0 < s.re) :
    ‖lemma44ComplexDirichletLFunction χ s‖ ≤ ‖s‖ * ((D : ℝ) / s.re) := by
  rw [lemma44ComplexDirichletLFunction_eq_abelIntegral_of_pos_re χ hD hs]
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (χ.norm_lemma44ComplexAbelIntegral_le hD hs) (norm_nonneg _)

theorem Lemma44ComplexCharacter.norm_lemma44ComplexDirichletLFunction_le_on_critical_line
    {D : ℕ} (χ : Lemma44ComplexCharacter D) (hD : 1 < D)
    {s : ℂ} (hs : s.re = 1 / 2) :
    ‖lemma44ComplexDirichletLFunction χ s‖ ≤ 2 * (D : ℝ) * ‖s‖ := by
  have hpos : 0 < s.re := by rw [hs]; norm_num
  have h := χ.norm_lemma44ComplexDirichletLFunction_le_of_pos_re hD hpos
  rw [hs] at h
  have hden : (D : ℝ) / (1 / 2) = 2 * (D : ℝ) := by
    field_simp
  rw [hden] at h
  nlinarith [h]

/-- A conductor-linear bound for the actual L-function of every nontrivial
complex character on the open right half-plane. -/
theorem lemma44_dirichletLFunction_norm_le_of_pos_re {N : ℕ} [NeZero N]
    (ψ : DirichletCharacter ℂ N) (hψ : ψ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    ‖DirichletCharacter.LFunction ψ s‖ ≤ ‖s‖ * ((N : ℝ) / s.re) := by
  let χ : Lemma44ComplexCharacter N := ⟨ψ, hψ, Nat.pos_of_ne_zero (NeZero.ne N)⟩
  have hN : N ≠ 1 := by
    intro he
    exact hψ (DirichletCharacter.level_one' ψ he)
  have hN1 : 1 < N := by
    have hp := Nat.pos_of_ne_zero (NeZero.ne N)
    omega
  exact χ.norm_lemma44ComplexDirichletLFunction_le_of_pos_re hN1 hs

end ZhangLS.Spec
