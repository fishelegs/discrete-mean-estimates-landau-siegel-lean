import ZhangLS.Spec.Lemma56MixedLogDetection

/-! # Uniform degree budget with independent normalization and growth scales

Actual L-functions and their actual zeros and analytic orders are retained.
The original finite prime-window target remains a separate unproved obligation.
-/

namespace ZhangLS.Spec
open Complex Metric Set Finset Filter
open scoped Real Topology
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

noncomputable def lemma56GeneralRepulsionDegree (U : ℝ) : ℕ := ⌈2000000 * U⌉₊

lemma lemma56_general_repulsion_degree_bounds {U : ℝ} (hU : 2000 ≤ U) :
    2000000 * U ≤ (lemma56GeneralRepulsionDegree U : ℝ) ∧
      (lemma56GeneralRepulsionDegree U : ℝ) ≤ 2000001 * U ∧
      (lemma56GeneralRepulsionDegree U : ℝ) + 1 ≤ 2000002 * U := by
  have hlo : 2000000 * U ≤ (lemma56GeneralRepulsionDegree U : ℝ) := Nat.le_ceil _
  have hup : (lemma56GeneralRepulsionDegree U : ℝ) < 2000000 * U + 1 :=
    Nat.ceil_lt_add_one (by linarith only [hU] : 0 ≤ 2000000 * U)
  exact ⟨hlo, by linarith only [hup, hU], by linarith only [hup, hU]⟩

lemma lemma56_general_repulsion_exponential_cost {U : ℝ} (hU : 2000 ≤ U) :
    Real.exp (4 * (lemma56GeneralRepulsionDegree U : ℝ) / U) ≤ Real.exp 8000004 := by
  have hUp : 0 < U := by linarith only [hU]
  apply Real.exp_le_exp.mpr
  apply (div_le_iff₀ hUp).mpr
  linarith only [(lemma56_general_repulsion_degree_bounds hU).2.1]

lemma lemma56_general_repulsion_exceptional_cost_bound {L U δ : ℝ}
    (hL : 2000 ≤ L) (hC : lemma56RepulsionErrorConstant ≤ L)
    (hU : 2000 ≤ U) (hUL : U ≤ L ^ 5) (_hδ : 0 ≤ δ)
    (hclose : δ ≤ 64 * L ^ (-2022 : ℤ)) :
    2 * δ * (lemma56GeneralRepulsionDegree U : ℝ) * ((lemma56GeneralRepulsionDegree U : ℝ) + 1) *
      Real.exp (4 * (lemma56GeneralRepulsionDegree U : ℝ) / U) ≤ 1 := by
  have hLp : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hj := lemma56_general_repulsion_degree_bounds hU
  have he := lemma56_general_repulsion_exponential_cost hU
  have hcancel : L ^ (-2022 : ℤ) * L ^ 10 = L ^ (-2012 : ℤ) := by
    rw [← zpow_natCast, ← zpow_add₀ hLp.ne']
    norm_num
  calc
    _ ≤ 2 * (64 * L ^ (-2022 : ℤ)) * (2000001 * L ^ 5) * (2000002 * L ^ 5) * Real.exp 8000004 := by
      gcongr
      · exact hj.2.1.trans (mul_le_mul_of_nonneg_left hUL (by norm_num))
      · exact hj.2.2.trans (mul_le_mul_of_nonneg_left hUL (by norm_num))
    _ = lemma56RepulsionErrorConstant * (L ^ (-2022 : ℤ) * L ^ 10) := by
      unfold lemma56RepulsionErrorConstant
      ring
    _ = lemma56RepulsionErrorConstant * L ^ (-2012 : ℤ) := by rw [hcancel]
    _ ≤ lemma56RepulsionErrorConstant * L ^ (-1 : ℤ) :=
      mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ hL1 (by norm_num))
        lemma56_repulsion_error_constant_pos.le
    _ ≤ 1 := by
      rw [zpow_neg_one, ← div_eq_mul_inv]
      exact (div_le_one hLp).mpr hC

lemma lemma56_general_repulsion_strict_budget {L U δ : ℝ}
    (hL : 2000 ≤ L) (hC : lemma56RepulsionErrorConstant ≤ L)
    (hU : 2000 ≤ U) (hUL : U ≤ L ^ 5) (hδ : 0 ≤ δ)
    (hclose : δ ≤ 64 * L ^ (-2022 : ℤ)) :
    475200 * U + 2 * δ * (lemma56GeneralRepulsionDegree U : ℝ) *
      ((lemma56GeneralRepulsionDegree U : ℝ) + 1) *
        Real.exp (4 * (lemma56GeneralRepulsionDegree U : ℝ) / U) <
      (lemma56GeneralRepulsionDegree U : ℝ) / 4 - 79 * U := by
  have hb := lemma56_general_repulsion_exceptional_cost_bound hL hC hU hUL hδ hclose
  have hj := (lemma56_general_repulsion_degree_bounds hU).1
  linarith only [hb, hj, hU]

end ZhangLS.Spec
