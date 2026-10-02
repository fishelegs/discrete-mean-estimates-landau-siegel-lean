import ZhangLS.Spec.Lemma55CombinedPowerUpperBound
import Mathlib.Algebra.Order.Floor.Semiring

/-! # Uniform degree and modulus budget for zero exclusion

A degree depending only on log D makes the actual detection lower bound
larger than the proved arithmetic upper bound. The exceptional distance
64(log D)^−2022 absorbs the fixed exponential normalization cost at one
uniform sufficiently-large modulus threshold.
-/

namespace ZhangLS.Spec
open Filter
open scoped Topology

noncomputable def lemma55RepulsionDegree (L : ℝ) : ℕ := ⌈2000000 * L⌉₊

noncomputable def lemma55RepulsionErrorConstant : ℝ :=
  256 * 2000001 * 2000002 * Real.exp 8000004

lemma lemma55_repulsion_error_constant_pos : 0 < lemma55RepulsionErrorConstant := by
  unfold lemma55RepulsionErrorConstant
  positivity

lemma lemma55_repulsion_degree_bounds {L : ℝ} (hL : 2000 ≤ L) :
    2000000 * L ≤ (lemma55RepulsionDegree L : ℝ) ∧
      (lemma55RepulsionDegree L : ℝ) ≤ 2000001 * L ∧
      (lemma55RepulsionDegree L : ℝ) + 1 ≤ 2000002 * L := by
  have hlo : 2000000 * L ≤ (lemma55RepulsionDegree L : ℝ) := Nat.le_ceil _
  have hup : (lemma55RepulsionDegree L : ℝ) < 2000000 * L + 1 :=
    Nat.ceil_lt_add_one (by linarith only [hL] : 0 ≤ 2000000 * L)
  exact ⟨hlo, by linarith only [hup, hL], by linarith only [hup, hL]⟩

lemma lemma55_repulsion_exponential_cost {L : ℝ} (hL : 2000 ≤ L) :
    Real.exp (4 * (lemma55RepulsionDegree L : ℝ) / L) ≤ Real.exp 8000004 := by
  have hLp : 0 < L := by linarith only [hL]
  apply Real.exp_le_exp.mpr
  apply (div_le_iff₀ hLp).mpr
  linarith only [(lemma55_repulsion_degree_bounds hL).2.1]

lemma lemma55_repulsion_exceptional_cost_bound {L δ : ℝ} (hL : 2000 ≤ L)
    (hC : lemma55RepulsionErrorConstant ≤ L) (_hδ : 0 ≤ δ)
    (hclose : δ ≤ 64 * L ^ (-2022 : ℤ)) :
    4 * δ * (lemma55RepulsionDegree L : ℝ) * ((lemma55RepulsionDegree L : ℝ) + 1) *
      Real.exp (4 * (lemma55RepulsionDegree L : ℝ) / L) ≤ 1 := by
  have hLp : 0 < L := by linarith only [hL]
  have hL1 : 1 ≤ L := by linarith only [hL]
  have hj := lemma55_repulsion_degree_bounds hL
  have he := lemma55_repulsion_exponential_cost hL
  have hcancel : L ^ (-2022 : ℤ) * L ^ 2 = L ^ (-2020 : ℤ) := by
    rw [← zpow_natCast, ← zpow_add₀ hLp.ne']
    norm_num
  calc
    _ ≤ 4 * (64 * L ^ (-2022 : ℤ)) * (2000001 * L) * (2000002 * L) * Real.exp 8000004 := by
      gcongr
      · exact hj.2.1
      · exact hj.2.2
    _ = lemma55RepulsionErrorConstant * (L ^ (-2022 : ℤ) * L ^ 2) := by
      unfold lemma55RepulsionErrorConstant
      ring
    _ = lemma55RepulsionErrorConstant * L ^ (-2020 : ℤ) := by rw [hcancel]
    _ ≤ lemma55RepulsionErrorConstant * L ^ (-1 : ℤ) :=
      mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ hL1 (by norm_num))
        lemma55_repulsion_error_constant_pos.le
    _ ≤ 1 := by
      rw [zpow_neg_one, ← div_eq_mul_inv]
      exact (div_le_one hLp).mpr hC

lemma lemma55_repulsion_strict_budget {L δ : ℝ} (hL : 2000 ≤ L)
    (hC : lemma55RepulsionErrorConstant ≤ L) (hδ : 0 ≤ δ)
    (hclose : δ ≤ 64 * L ^ (-2022 : ℤ)) :
    374400 * L + 8 +
      4 * δ * (lemma55RepulsionDegree L : ℝ) * ((lemma55RepulsionDegree L : ℝ) + 1) *
        Real.exp (4 * (lemma55RepulsionDegree L : ℝ) / L) <
      (lemma55RepulsionDegree L : ℝ) / 4 - 62 * L := by
  have hb := lemma55_repulsion_exceptional_cost_bound hL hC hδ hclose
  have hj := (lemma55_repulsion_degree_bounds hL).1
  linarith only [hb, hj, hL]

lemma lemma55_uniform_repulsion_modulus_threshold :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
      2000 ≤ Real.log (D : ℝ) ∧ lemma55RepulsionErrorConstant ≤ Real.log (D : ℝ) := by
  have ht : Tendsto (fun D : ℕ => Real.log (D : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have he : ∀ᶠ D : ℕ in atTop,
      max 2000 lemma55RepulsionErrorConstant ≤ Real.log (D : ℝ) :=
    ht.eventually (eventually_ge_atTop _)
  obtain ⟨D₀, hD₀⟩ := eventually_atTop.mp he
  exact ⟨D₀, fun D hD => ⟨(le_max_left _ _).trans (hD₀ D hD),
    (le_max_right _ _).trans (hD₀ D hD)⟩⟩

end ZhangLS.Spec
