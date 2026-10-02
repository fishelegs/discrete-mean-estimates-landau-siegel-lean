import Mathlib.Analysis.Meromorphic.FactorizedRational
import ZhangLS.Spec.Lemma23GeneralArgumentPrinciple
import ZhangLS.Spec.Lemma23ModelZeros

/-!
# Rouché count for the reference model in Lemma 2.3

On every disk whose radius is strictly between `α = π/L` and `2α`, the reference exponential
model has total zero multiplicity three.  Consequently any analytic function satisfying the
strict Rouché boundary inequality has the same multiplicity count.
-/

namespace ZhangLS.Spec

open Complex Metric Set

/-- The zero divisor of the exponential reference model has total multiplicity three on any disk
with radius strictly between its first and second nonzero zero radii. -/
theorem lemma23_exponential_gap_model_divisor_sum_eq_three
    {L R : ℝ} (hL : 0 < L)
    (hRlo : Real.pi / L < R) (hRhi : R < 2 * (Real.pi / L)) :
    let D := MeromorphicOn.divisor (lemma23ExponentialGapModel L) (closedBall 0 R)
    (∑ a ∈ (lemma23_support_finite_of_isCompact (isCompact_closedBall 0 R) D).toFinset,
      ((D a).toNat : ℂ)) = 3 := by
  classical
  dsimp only
  let K : Set ℂ := closedBall 0 R
  let f : ℂ → ℂ := lemma23ExponentialGapModel L
  let D : Function.locallyFinsuppWithin K ℤ := MeromorphicOn.divisor f K
  let α : ℝ := Real.pi / L
  let rPlus : ℂ := (α : ℂ) * Complex.I
  let rMinus : ℂ := -((α : ℂ) * Complex.I)
  let modelRoots : Finset ℂ := {0, rPlus, rMinus}
  have hα : 0 < α := div_pos Real.pi_pos hL
  have hRpos : 0 < R := lt_trans hα hRlo
  have hf : AnalyticOnNhd ℂ f K := by
    change ∀ z ∈ K,
      AnalyticAt ℂ (fun z : ℂ => 1 - Complex.exp (-2 * z * (L : ℂ))) z
    intro z hz
    fun_prop
  have hDfinite : D.support.Finite := by
    exact lemma23_support_finite_of_isCompact (isCompact_closedBall 0 R) D
  have hrootsInside : ∀ a ∈ modelRoots, a ∈ ball (0 : ℂ) R := by
    intro a ha
    simp only [modelRoots, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · simpa [Metric.mem_ball, dist_zero_right] using hRpos
    · have hnorm : ‖rPlus‖ = α := by
        simp [rPlus, norm_real, norm_I, Real.norm_of_nonneg hα.le]
      rw [Metric.mem_ball, dist_zero_right, hnorm]
      exact hRlo
    · have hnorm : ‖rMinus‖ = α := by
        simp [rMinus, norm_neg, norm_real, norm_I,
          Real.norm_of_nonneg hα.le]
      rw [Metric.mem_ball, dist_zero_right, hnorm]
      exact hRlo
  have hmodelZero : ∀ z ∈ K, f z = 0 → z ∈ modelRoots := by
    intro z hzK hzero
    have hnormLe : ‖z‖ ≤ R := by
      simpa [K, Metric.mem_closedBall, dist_zero_right] using hzK
    have hnormTwo : ‖z‖ < 2 * α := by
      dsimp [α] at *
      exact lt_of_le_of_lt hnormLe hRhi
    have hclassified := lemma23_exponential_gap_model_zero_in_two_alpha_ball hL hnormTwo hzero
    simpa [modelRoots, rPlus, rMinus, α] using hclassified
  have hsupportEq : D.support = modelRoots := by
    ext z
    constructor
    · intro hz
      have hzK : z ∈ K := D.supportWithinDomain hz
      have hDne : D z ≠ 0 := Function.mem_support.mp hz
      have hzero : f z = 0 := by
        by_contra hne
        have horder0 : analyticOrderAt f z = 0 := (hf z hzK).analyticOrderAt_eq_zero.mpr hne
        have hDzero : D z = 0 := by
          change MeromorphicOn.divisor f K z = 0
          rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hf hzK, horder0]
          simp
        exact hDne hDzero
      exact hmodelZero z hzK hzero
    · intro hz
      have hz' : z ∈ modelRoots := hz
      simp only [modelRoots, Finset.mem_insert, Finset.mem_singleton] at hz'
      rcases hz' with rfl | rfl | rfl
      · have hzero : f 0 = 0 := by
          exact (lemma23_exponential_gap_model_zero_iff hL 0).2 ⟨by simp, 0, by simp⟩
        have hzK : (0 : ℂ) ∈ K := by
          simp [K, hRpos.le]
        apply Function.mem_support.mpr
        have horder := lemma23_exponential_gap_model_order_one hL hzero
        change MeromorphicOn.divisor f K 0 ≠ 0
        rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hf hzK, horder]
        norm_num [WithTop.untop₀]
      · have hzero : f rPlus = 0 := by
          apply (lemma23_exponential_gap_model_zero_iff hL rPlus).2
          refine ⟨?_, -1, ?_⟩
          · simp [rPlus, α]
          · simp [rPlus, α]
        have hzK : rPlus ∈ K := ball_subset_closedBall
          (hrootsInside rPlus (by simp [modelRoots]))
        apply Function.mem_support.mpr
        have horder := lemma23_exponential_gap_model_order_one hL hzero
        change MeromorphicOn.divisor f K rPlus ≠ 0
        rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hf hzK, horder]
        norm_num [WithTop.untop₀]
      · have hzero : f rMinus = 0 := by
          apply (lemma23_exponential_gap_model_zero_iff hL rMinus).2
          refine ⟨?_, 1, ?_⟩
          · simp [rMinus, α]
          · simp [rMinus, α]
        have hzK : rMinus ∈ K := ball_subset_closedBall
          (hrootsInside rMinus (by simp [modelRoots]))
        apply Function.mem_support.mpr
        have horder := lemma23_exponential_gap_model_order_one hL hzero
        change MeromorphicOn.divisor f K rMinus ≠ 0
        rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hf hzK, horder]
        norm_num [WithTop.untop₀]
  have hfiniteRoots : hDfinite.toFinset = modelRoots := by
    ext z
    rw [hDfinite.mem_toFinset]
    exact Set.ext_iff.mp hsupportEq z
  have hmult : ∀ a ∈ modelRoots, D a = 1 := by
    intro a ha
    simp only [modelRoots, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · have hzK : (0 : ℂ) ∈ K := by simp [K, hRpos.le]
      have hzero : f 0 = 0 := by
        exact (lemma23_exponential_gap_model_zero_iff hL 0).2 ⟨by simp, 0, by simp⟩
      change MeromorphicOn.divisor f K 0 = 1
      rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hf hzK,
        lemma23_exponential_gap_model_order_one hL hzero]
      norm_num [WithTop.untop₀]
    · have hzK : rPlus ∈ K := ball_subset_closedBall
        (hrootsInside rPlus (by simp [modelRoots]))
      have hzero : f rPlus = 0 := by
        apply (lemma23_exponential_gap_model_zero_iff hL rPlus).2
        refine ⟨by simp [rPlus, α], -1, by simp [rPlus, α]⟩
      change MeromorphicOn.divisor f K rPlus = 1
      rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hf hzK,
        lemma23_exponential_gap_model_order_one hL hzero]
      norm_num [WithTop.untop₀]
    · have hzK : rMinus ∈ K := ball_subset_closedBall
        (hrootsInside rMinus (by simp [modelRoots]))
      have hzero : f rMinus = 0 := by
        apply (lemma23_exponential_gap_model_zero_iff hL rMinus).2
        refine ⟨by simp [rMinus, α], 1, by simp [rMinus, α]⟩
      change MeromorphicOn.divisor f K rMinus = 1
      rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hf hzK,
        lemma23_exponential_gap_model_order_one hL hzero]
      norm_num [WithTop.untop₀]
  rw [hfiniteRoots]
  calc
    (∑ a ∈ modelRoots, ((D a).toNat : ℂ)) = ∑ a ∈ modelRoots, (1 : ℂ) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [hmult a ha]
      simp
    _ = 3 := by
      have hplusNeZero : rPlus ≠ 0 := by
        intro hz
        have him := congrArg Complex.im hz
        simp [rPlus] at him
        exact hα.ne' him
      have hminusNeZero : rMinus ≠ 0 := by
        intro hz
        have him := congrArg Complex.im hz
        simp [rMinus] at him
        exact hα.ne' (by linarith)
      have hplusNeMinus : rPlus ≠ rMinus := by
        intro hz
        have him := congrArg Complex.im hz
        simp [rPlus, rMinus] at him
        linarith
      simp [modelRoots, hplusNeZero, hminusNeZero, hplusNeMinus, ne_comm]

/-- Localized Rouché transfer for the reference model: a function analytic on the closed disk and
strictly closer to the model than the model's boundary modulus has exactly three zeros there,
counting multiplicity.  The boundary estimate is deliberately an explicit hypothesis; proving it
for Zhang's actual Dirichlet product is the remaining analytic estimate from Section 4. -/
theorem lemma23_rouche_model_divisor_sum_eq_three
    {L R : ℝ} (hL : 0 < L)
    (hRlo : Real.pi / L < R) (hRhi : R < 2 * (Real.pi / L))
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hclose : ∀ z ∈ sphere (0 : ℂ) R,
      ‖f z - lemma23ExponentialGapModel L z‖ <
        ‖lemma23ExponentialGapModel L z‖) :
    let D := MeromorphicOn.divisor f (closedBall 0 R)
    (∑ a ∈ (lemma23_support_finite_of_isCompact (isCompact_closedBall 0 R) D).toFinset,
      ((D a).toNat : ℂ)) = 3 := by
  classical
  dsimp only
  let K : Set ℂ := closedBall 0 R
  let Df : Function.locallyFinsuppWithin K ℤ := MeromorphicOn.divisor f K
  let g : ℂ → ℂ := lemma23ExponentialGapModel L
  have hR : 0 < R := lt_trans (div_pos Real.pi_pos hL) hRlo
  have hg : AnalyticOnNhd ℂ g K := by
    intro z hz
    change AnalyticAt ℂ (fun z : ℂ => 1 - Complex.exp (-2 * z * (L : ℂ))) z
    fun_prop
  have hDfFinite : Df.support.Finite :=
    lemma23_support_finite_of_isCompact (isCompact_closedBall 0 R) Df
  let Dg : Function.locallyFinsuppWithin K ℤ := MeromorphicOn.divisor g K
  have hDgFinite : Dg.support.Finite :=
    lemma23_support_finite_of_isCompact (isCompact_closedBall 0 R) Dg
  have hcounts := lemma23_rouche_zero_multiplicity_sum hR f g hf hg hclose
    hDfFinite hDgFinite
  have hmodelCount := lemma23_exponential_gap_model_divisor_sum_eq_three
    hL hRlo hRhi
  simpa [Df, g, Dg, K] using hcounts.trans hmodelCount

/-- On a disk of radius strictly smaller than `α = π/L`, the reference model has exactly one
zero, at the origin, and that zero is simple. -/
theorem lemma23_exponential_gap_model_divisor_sum_eq_one
    {L R : ℝ} (hL : 0 < L)
    (hRpos : 0 < R) (hRsmall : R < Real.pi / L) :
    let D := MeromorphicOn.divisor (lemma23ExponentialGapModel L) (closedBall 0 R)
    (∑ a ∈ (lemma23_support_finite_of_isCompact (isCompact_closedBall 0 R) D).toFinset,
      ((D a).toNat : ℂ)) = 1 := by
  classical
  dsimp only
  let K : Set ℂ := closedBall 0 R
  let f : ℂ → ℂ := lemma23ExponentialGapModel L
  let D : Function.locallyFinsuppWithin K ℤ := MeromorphicOn.divisor f K
  let α : ℝ := Real.pi / L
  let modelRoots : Finset ℂ := {0}
  have hα : 0 < α := div_pos Real.pi_pos hL
  have hRsmall' : R < α := by simpa [α] using hRsmall
  have hRtwo : R < 2 * α := by linarith
  have hf : AnalyticOnNhd ℂ f K := by
    change ∀ z ∈ K,
      AnalyticAt ℂ (fun z : ℂ => 1 - Complex.exp (-2 * z * (L : ℂ))) z
    intro z hz
    fun_prop
  have hDfinite : D.support.Finite :=
    lemma23_support_finite_of_isCompact (isCompact_closedBall 0 R) D
  have hmodelZero : ∀ z ∈ K, f z = 0 → z ∈ modelRoots := by
    intro z hzK hzero
    have hnormLe : ‖z‖ ≤ R := by
      simpa [K, Metric.mem_closedBall, dist_zero_right] using hzK
    have hnormTwo : ‖z‖ < 2 * α := lt_of_le_of_lt hnormLe hRtwo
    have hclassified := lemma23_exponential_gap_model_zero_in_two_alpha_ball
      hL hnormTwo hzero
    rcases hclassified with hz | hz | hz
    · simpa [modelRoots] using hz
    · have hnormAlpha : ‖((α : ℝ) : ℂ) * Complex.I‖ = α := by
        simp [norm_real, norm_I, Real.norm_of_nonneg hα.le]
      have hle : α ≤ R := by
        rw [hz, hnormAlpha] at hnormLe
        exact hnormLe
      exact False.elim ((not_le_of_gt hRsmall') hle)
    · have hnormAlpha : ‖-((α : ℝ) : ℂ) * Complex.I‖ = α := by
        simp [norm_neg, norm_real, norm_I, Real.norm_of_nonneg hα.le]
      have hle : α ≤ R := by
        rw [hz, hnormAlpha] at hnormLe
        exact hnormLe
      exact False.elim ((not_le_of_gt hRsmall') hle)
  have hsupportEq : D.support = modelRoots := by
    ext z
    constructor
    · intro hz
      have hzK : z ∈ K := D.supportWithinDomain hz
      have hDne : D z ≠ 0 := Function.mem_support.mp hz
      have hzero : f z = 0 := by
        by_contra hne
        have horder0 : analyticOrderAt f z = 0 := (hf z hzK).analyticOrderAt_eq_zero.mpr hne
        have hDzero : D z = 0 := by
          change MeromorphicOn.divisor f K z = 0
          rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hf hzK, horder0]
          simp
        exact hDne hDzero
      exact hmodelZero z hzK hzero
    · intro hz
      have hz' : z ∈ modelRoots := hz
      simp only [modelRoots, Finset.mem_singleton] at hz'
      subst z
      have hzero : f 0 = 0 := by
        exact (lemma23_exponential_gap_model_zero_iff hL 0).2 ⟨by simp, 0, by simp⟩
      have hzK : (0 : ℂ) ∈ K := by simp [K, hRpos.le]
      apply Function.mem_support.mpr
      change MeromorphicOn.divisor f K 0 ≠ 0
      rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hf hzK,
        lemma23_exponential_gap_model_order_one hL hzero]
      norm_num [WithTop.untop₀]
  have hfiniteRoots : hDfinite.toFinset = modelRoots := by
    ext z
    rw [hDfinite.mem_toFinset]
    exact Set.ext_iff.mp hsupportEq z
  have hmult : D 0 = 1 := by
    have hzK : (0 : ℂ) ∈ K := by simp [K, hRpos.le]
    have hzero : f 0 = 0 := by
      exact (lemma23_exponential_gap_model_zero_iff hL 0).2 ⟨by simp, 0, by simp⟩
    change MeromorphicOn.divisor f K 0 = 1
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hf hzK,
      lemma23_exponential_gap_model_order_one hL hzero]
    norm_num [WithTop.untop₀]
  rw [hfiniteRoots]
  simp only [modelRoots, Finset.sum_singleton]
  change ((D 0).toNat : ℂ) = 1
  rw [hmult]
  norm_num

/-- The inner-disk Rouché specialization used by Lemma 4.6: under strict boundary comparison with
the model, a function has exactly one zero in a disk of radius less than `π/L`, counted with
multiplicity. -/
theorem lemma23_rouche_model_divisor_sum_eq_one
    {L R : ℝ} (hL : 0 < L)
    (hRpos : 0 < R) (hRsmall : R < Real.pi / L)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hclose : ∀ z ∈ sphere (0 : ℂ) R,
      ‖f z - lemma23ExponentialGapModel L z‖ <
        ‖lemma23ExponentialGapModel L z‖) :
    let D := MeromorphicOn.divisor f (closedBall 0 R)
    (∑ a ∈ (lemma23_support_finite_of_isCompact (isCompact_closedBall 0 R) D).toFinset,
      ((D a).toNat : ℂ)) = 1 := by
  classical
  dsimp only
  let K : Set ℂ := closedBall 0 R
  let Df : Function.locallyFinsuppWithin K ℤ := MeromorphicOn.divisor f K
  let g : ℂ → ℂ := lemma23ExponentialGapModel L
  let Dg : Function.locallyFinsuppWithin K ℤ := MeromorphicOn.divisor g K
  have hR : 0 < R := hRpos
  have hg : AnalyticOnNhd ℂ g K := by
    change ∀ z ∈ K,
      AnalyticAt ℂ (fun z : ℂ => 1 - Complex.exp (-2 * z * (L : ℂ))) z
    intro z hz
    fun_prop
  have hDfFinite : Df.support.Finite :=
    lemma23_support_finite_of_isCompact (isCompact_closedBall 0 R) Df
  have hDgFinite : Dg.support.Finite :=
    lemma23_support_finite_of_isCompact (isCompact_closedBall 0 R) Dg
  have hcounts := lemma23_rouche_zero_multiplicity_sum hR f g hf hg hclose
    hDfFinite hDgFinite
  have hmodelCount := lemma23_exponential_gap_model_divisor_sum_eq_one
    hL hRpos hRsmall
  simpa [Df, Dg, g, K] using hcounts.trans hmodelCount

end ZhangLS.Spec
