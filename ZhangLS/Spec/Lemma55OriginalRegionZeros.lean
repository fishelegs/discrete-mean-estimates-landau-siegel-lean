import ZhangLS.Spec.Lemma55OriginalRegionCover
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# A finite set containing exactly the actual zeros in the full original region

The entire original region is covered by 8D+1 closed local disks. Actual
nonvanishing for Re s≥1 excludes the unbounded right part of that region.
The resulting finite set equals the full original zero set and has at most
13(8D+1)log D distinct zeros. This is not a claim that only the exceptional
zero exists; eliminating the other candidates remains the repulsion step.
-/

namespace ZhangLS.Spec

open Complex Metric Set
open scoped Real

noncomputable def lemma55RegionZeroCandidates {D : ℕ}
    (χ : RealPrimitiveCharacter D) : Finset ℂ := by
  classical
  exact (Finset.range (8 * D + 1)).biUnion
    (fun j => lemma55LocalZeroFinset χ (lemma55ZeroGridHeight D j))

noncomputable def lemma55RegionZeroFinset {D : ℕ}
    (χ : RealPrimitiveCharacter D) : Finset ℂ := by
  classical
  exact (lemma55RegionZeroCandidates χ).filter (Lemma55InZeroRegion D)

theorem lemma55_actual_zero_re_lt_one
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) {ρ : ℂ}
    (hρ : dirichletLFunction χ ρ = 0) : ρ.re < 1 := by
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  by_contra hnot
  have hre : 1 ≤ ρ.re := le_of_not_gt hnot
  have hne : dirichletLFunction χ ρ ≠ 0 := by
    simpa [dirichletLFunction] using DirichletCharacter.LFunction_ne_zero_of_one_le_re
      χ.chi (.inl (χ.nontrivial_of_one_lt_modulus hD)) hre
  exact hne hρ

theorem lemma55_mem_original_region_zero_finset
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) (ρ : ℂ) :
    ρ ∈ lemma55RegionZeroFinset χ ↔
      Lemma55InZeroRegion D ρ ∧ dirichletLFunction χ ρ = 0 := by
  classical
  simp only [lemma55RegionZeroFinset, Finset.mem_filter]
  constructor
  · rintro ⟨hc, hregion⟩
    rw [lemma55RegionZeroCandidates, Finset.mem_biUnion] at hc
    obtain ⟨j, _hj, hρ⟩ := hc
    exact ⟨hregion, ((lemma55_mem_actual_local_zero_finset χ hD _ ρ).mp hρ).2⟩
  · rintro ⟨hregion, hzero⟩
    obtain ⟨j, hj, _ht, hball⟩ := lemma55_original_region_disk_cover hL hregion
      (lemma55_actual_zero_re_lt_one χ hD hzero).le
    refine ⟨?_, hregion⟩
    rw [lemma55RegionZeroCandidates, Finset.mem_biUnion]
    refine ⟨j, Finset.mem_range.mpr (by omega), ?_⟩
    exact (lemma55_mem_actual_local_zero_finset χ hD _ ρ).mpr ⟨hball, hzero⟩

theorem lemma55_original_region_actual_zeros_finite
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) :
    {ρ : ℂ | Lemma55InZeroRegion D ρ ∧ dirichletLFunction χ ρ = 0}.Finite := by
  have heq : {ρ : ℂ | Lemma55InZeroRegion D ρ ∧ dirichletLFunction χ ρ = 0} =
      (lemma55RegionZeroFinset χ : Set ℂ) := by
    ext ρ
    exact (lemma55_mem_original_region_zero_finset χ hD hL ρ).symm
  rw [heq]
  exact (lemma55RegionZeroFinset χ).finite_toSet

theorem lemma55_original_region_zero_card_bound
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) :
    ((lemma55RegionZeroFinset χ).card : ℝ) ≤
      13 * (8 * (D : ℝ) + 1) * Real.log (D : ℝ) := by
  classical
  have hfilter : (lemma55RegionZeroFinset χ).card ≤ (lemma55RegionZeroCandidates χ).card :=
    Finset.card_filter_le _ _
  have hunion : (lemma55RegionZeroCandidates χ).card ≤
      ∑ j ∈ Finset.range (8 * D + 1),
        (lemma55LocalZeroFinset χ (lemma55ZeroGridHeight D j)).card :=
    Finset.card_biUnion_le
  have hcast : ((lemma55RegionZeroFinset χ).card : ℝ) ≤
      ∑ j ∈ Finset.range (8 * D + 1),
        ((lemma55LocalZeroFinset χ (lemma55ZeroGridHeight D j)).card : ℝ) := by
    exact_mod_cast hfilter.trans hunion
  calc
    _ ≤ ∑ j ∈ Finset.range (8 * D + 1),
        ((lemma55LocalZeroFinset χ (lemma55ZeroGridHeight D j)).card : ℝ) := hcast
    _ ≤ ∑ _j ∈ Finset.range (8 * D + 1), 13 * Real.log (D : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      apply lemma55_actual_local_zero_card_bound χ hD hL
      exact lemma55_zero_grid_height_bound (by have h := Finset.mem_range.mp hj; omega)
    _ = 13 * (8 * (D : ℝ) + 1) * Real.log (D : ℝ) := by
      simp
      ring

theorem lemma55_original_region_maximal_zero
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) {ρ : ℂ}
    (hregion : Lemma55InZeroRegion D ρ) (hzero : dirichletLFunction χ ρ = 0) :
    ∃ ρₘ : ℂ, Lemma55InZeroRegion D ρₘ ∧ dirichletLFunction χ ρₘ = 0 ∧
      ρ.re ≤ ρₘ.re ∧ ∀ z : ℂ, Lemma55InZeroRegion D z →
        dirichletLFunction χ z = 0 → z.re ≤ ρₘ.re := by
  have hρ : ρ ∈ lemma55RegionZeroFinset χ :=
    (lemma55_mem_original_region_zero_finset χ hD hL ρ).mpr ⟨hregion, hzero⟩
  obtain ⟨ρₘ, hm, hmax⟩ :=
    (lemma55RegionZeroFinset χ).exists_max_image Complex.re ⟨ρ, hρ⟩
  have hm' := (lemma55_mem_original_region_zero_finset χ hD hL ρₘ).mp hm
  refine ⟨ρₘ, hm'.1, hm'.2, hmax ρ hρ, ?_⟩
  intro z hz hLz
  exact hmax z ((lemma55_mem_original_region_zero_finset χ hD hL z).mpr ⟨hz, hLz⟩)

theorem lemma55_original_region_contains_exceptional_zero
    {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hDN : lemma57ExplicitModulusThreshold ≤ D) (hA : NormalizedAssumptionA χ) :
    ∃ ρ : ℝ, (ρ : ℂ) ∈ lemma55RegionZeroFinset χ ∧
      0 < 1 - ρ ∧ 1 - ρ ≤ 64 * Real.log (D : ℝ) ^ (-2022 : ℤ) ∧
      deriv (dirichletLFunction χ) (ρ : ℂ) ≠ 0 := by
  have hD := lemma57_one_lt_of_explicit_threshold hDN
  have hL : 2000 ≤ Real.log (D : ℝ) := by
    linarith only [lemma57_log_ge_ten_million hDN]
  have hLp : 0 < Real.log (D : ℝ) := by linarith only [hL]
  obtain ⟨ρ, hp, hw, hzero, hsimple⟩ := lemma55_actual_simple_real_zero χ hDN hA
  have hb := lemma55_local_zero_budget hDN
  have hsmall : 1 - ρ ≤ 1 / (4 * Real.log (D : ℝ)) :=
    (show 1 - ρ ≤ lemma55RealZeroWidth D from hw).trans hb.2.1
  have hgap : 1 / (4 * Real.log (D : ℝ)) < 2 / Real.log (D : ℝ) := by
    apply (div_lt_div_iff₀ (by positivity) hLp).mpr
    linarith only [hLp]
  have hregion : Lemma55InZeroRegion D (ρ : ℂ) := by
    constructor
    · change 1 - 2 / Real.log (D : ℝ) < ρ
      linarith only [hsmall, hgap]
    · simp only [Complex.ofReal_im, abs_zero]
      positivity
  exact ⟨ρ, (lemma55_mem_original_region_zero_finset χ hD hL _).mpr ⟨hregion, hzero⟩,
    hp, hw, hsimple⟩

theorem lemma55_original_region_rightmost_zero_under_A
    {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hDN : lemma57ExplicitModulusThreshold ≤ D) (hA : NormalizedAssumptionA χ) :
    ∃ ρₘ : ℂ, Lemma55InZeroRegion D ρₘ ∧ dirichletLFunction χ ρₘ = 0 ∧
      ∀ z : ℂ, Lemma55InZeroRegion D z → dirichletLFunction χ z = 0 → z.re ≤ ρₘ.re := by
  have hD := lemma57_one_lt_of_explicit_threshold hDN
  have hL : 2000 ≤ Real.log (D : ℝ) := by
    linarith only [lemma57_log_ge_ten_million hDN]
  obtain ⟨ρ, hρ, _hp, _hw, _hsimple⟩ := lemma55_original_region_contains_exceptional_zero χ hDN hA
  have hρ' := (lemma55_mem_original_region_zero_finset χ hD hL _).mp hρ
  obtain ⟨ρₘ, hm, hzero, _hle, hmax⟩ := lemma55_original_region_maximal_zero χ hD hL hρ'.1 hρ'.2
  exact ⟨ρₘ, hm, hzero, hmax⟩

end ZhangLS.Spec
