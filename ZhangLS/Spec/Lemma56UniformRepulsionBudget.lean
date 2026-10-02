import ZhangLS.Spec.Lemma56MixedPowerUpperBound
import Mathlib.Algebra.Order.Floor.Semiring

/-! # Uniform degree and exceptional-zero budget for mixed zero repulsion

The degree is proportional to L^1.1, while normalization uses L^4.
One absolute constant controls all moduli, characters and heights.
-/

namespace ZhangLS.Spec
open Filter
open scoped Topology Real

noncomputable def lemma56RepulsionDegree (L : ℝ) : ℕ := ⌈2000000 * L ^ (11 / 10 : ℝ)⌉₊

noncomputable def lemma56RepulsionErrorConstant : ℝ :=
  128 * 2000001 * 2000002 * Real.exp 8000004

lemma lemma56_repulsion_error_constant_pos : 0 < lemma56RepulsionErrorConstant := by
  unfold lemma56RepulsionErrorConstant
  positivity

lemma lemma56_repulsion_scale_bounds {L : ℝ} (hL : 2000 ≤ L) :
    1 ≤ L ^ (11 / 10 : ℝ) ∧ L ^ (11 / 10 : ℝ) ≤ L ^ 2 ∧ L ≤ L ^ 4 := by
  have hL1 : 1 ≤ L := by linarith
  have h1 : L ≤ L ^ (11 / 10 : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hL1 (show (1 : ℝ) ≤ 11 / 10 by norm_num)
  have h2 : L ^ (11 / 10 : ℝ) ≤ L ^ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le hL1 (show (11 / 10 : ℝ) ≤ 2 by norm_num)
  exact ⟨hL1.trans h1, h2, by simpa using pow_le_pow_right₀ hL1 (show 1 ≤ 4 by norm_num)⟩

lemma lemma56_repulsion_degree_bounds {L : ℝ} (hL : 2000 ≤ L) :
    2000000 * L ^ (11 / 10 : ℝ) ≤ (lemma56RepulsionDegree L : ℝ) ∧
      (lemma56RepulsionDegree L : ℝ) ≤ 2000001 * L ^ 2 ∧
      (lemma56RepulsionDegree L : ℝ) + 1 ≤ 2000002 * L ^ 2 := by
  have hs := lemma56_repulsion_scale_bounds hL
  have hlo : 2000000 * L ^ (11 / 10 : ℝ) ≤ (lemma56RepulsionDegree L : ℝ) := Nat.le_ceil _
  have hup : (lemma56RepulsionDegree L : ℝ) < 2000000 * L ^ (11 / 10 : ℝ) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  exact ⟨hlo, by nlinarith only [hup, hs.1, hs.2.1], by nlinarith only [hup, hs.1, hs.2.1]⟩

lemma lemma56_repulsion_exponential_cost {L : ℝ} (hL : 2000 ≤ L) :
    Real.exp (4 * (lemma56RepulsionDegree L : ℝ) / L ^ 4) ≤ Real.exp 8000004 := by
  have hLp : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have h24 : L ^ 2 ≤ L ^ 4 := pow_le_pow_right₀ hL1 (by norm_num)
  apply Real.exp_le_exp.mpr
  apply (div_le_iff₀ (pow_pos hLp 4)).mpr
  have hj := (lemma56_repulsion_degree_bounds hL).2.1
  nlinarith only [hj, h24]

lemma lemma56_repulsion_exceptional_cost_bound {L δ : ℝ} (hL : 2000 ≤ L)
    (hC : lemma56RepulsionErrorConstant ≤ L) (_hδ : 0 ≤ δ)
    (hclose : δ ≤ 64 * L ^ (-2022 : ℤ)) :
    2 * δ * (lemma56RepulsionDegree L : ℝ) * ((lemma56RepulsionDegree L : ℝ) + 1) *
      Real.exp (4 * (lemma56RepulsionDegree L : ℝ) / L ^ 4) ≤ 1 := by
  have hLp : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hj := lemma56_repulsion_degree_bounds hL
  have he := lemma56_repulsion_exponential_cost hL
  have hcancel : L ^ (-2022 : ℤ) * L ^ 4 = L ^ (-2018 : ℤ) := by
    rw [← zpow_natCast, ← zpow_add₀ hLp.ne']
    norm_num
  calc
    _ ≤ 2 * (64 * L ^ (-2022 : ℤ)) * (2000001 * L ^ 2) * (2000002 * L ^ 2) * Real.exp 8000004 := by
      gcongr
      · exact hj.2.1
      · exact hj.2.2
    _ = lemma56RepulsionErrorConstant * (L ^ (-2022 : ℤ) * L ^ 4) := by
      unfold lemma56RepulsionErrorConstant
      ring
    _ = lemma56RepulsionErrorConstant * L ^ (-2018 : ℤ) := by rw [hcancel]
    _ ≤ lemma56RepulsionErrorConstant * L ^ (-1 : ℤ) :=
      mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ hL1 (by norm_num))
        lemma56_repulsion_error_constant_pos.le
    _ ≤ 1 := by
      rw [zpow_neg_one, ← div_eq_mul_inv]
      exact (div_le_one hLp).mpr hC

lemma lemma56_repulsion_strict_budget {L δ : ℝ} (hL : 2000 ≤ L)
    (hC : lemma56RepulsionErrorConstant ≤ L) (hδ : 0 ≤ δ)
    (hclose : δ ≤ 64 * L ^ (-2022 : ℤ)) :
    475200 * L ^ (11 / 10 : ℝ) +
      2 * δ * (lemma56RepulsionDegree L : ℝ) * ((lemma56RepulsionDegree L : ℝ) + 1) *
        Real.exp (4 * (lemma56RepulsionDegree L : ℝ) / L ^ 4) <
      (lemma56RepulsionDegree L : ℝ) / 4 - 79 * L ^ (11 / 10 : ℝ) := by
  have hb := lemma56_repulsion_exceptional_cost_bound hL hC hδ hclose
  have hj := (lemma56_repulsion_degree_bounds hL).1
  have hs := (lemma56_repulsion_scale_bounds hL).1
  linarith only [hb, hj, hs]

lemma lemma56_uniform_repulsion_modulus_threshold :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
      2000 ≤ Real.log (D : ℝ) ∧ lemma56RepulsionErrorConstant ≤ Real.log (D : ℝ) := by
  have ht : Tendsto (fun D : ℕ => Real.log (D : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have he : ∀ᶠ D : ℕ in atTop,
      max 2000 lemma56RepulsionErrorConstant ≤ Real.log (D : ℝ) :=
    ht.eventually (eventually_ge_atTop _)
  obtain ⟨D₀, hD₀⟩ := eventually_atTop.mp he
  exact ⟨D₀, fun D hD => ⟨(le_max_left _ _).trans (hD₀ D hD),
    (le_max_right _ _).trans (hD₀ D hD)⟩⟩

end ZhangLS.Spec
