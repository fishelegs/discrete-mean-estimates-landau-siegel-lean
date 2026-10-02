import ZhangLS.Spec.Lemma81ZetaLocalRealPart
import Mathlib.Topology.MetricSpace.Thickening

/-! # An unconditional classical thin zero-free strip for actual zeta

The explicit high-height width is 1/(10^7 log D). The bounded-height
collar is obtained from compactness and actual nonvanishing on Re s=1.
No Assumption (A) or quantitative prime-number theorem is used.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Metric Set Filter
open scoped Topology
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

lemma lemma81_zeta_high_thin_strip {D : ℕ}
    (hD : 1 < D) (hL : 2000 ≤ Real.log (D : ℝ)) {ρ : ℂ}
    (hre : 1 - 1 / (10000000 * Real.log (D : ℝ)) < ρ.re)
    (hheight : |ρ.im| ≤ D) (hlow : 1 ≤ |ρ.im|) : zetaPoleRemoved ρ ≠ 0 := by
  intro hRzero
  let L := Real.log (D : ℝ)
  let δ := 1 / (10000000 * L)
  let σ := 1 + 4 * δ
  have hLp : 0 < L := by dsimp [L]; linarith only [hL]
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδsmall : δ ≤ (1 / 100 : ℝ) := by
    dsimp [δ]
    apply (div_le_div_iff₀ (by positivity : 0 < 10000000 * L) (by norm_num)).mpr
    dsimp [L]
    linarith only [hL]
  have hρpos : 0 < ρ.re := by
    change 1 - δ < ρ.re at hre
    linarith only [hre, hδsmall]
  have hzero := (lemma55_actual_zeta_pole_removed_zero_iff hρpos).mp hRzero
  have hρ1 : ρ.re < 1 := lemma55_actual_zeta_pole_removed_zero_re_lt_one hRzero
  have hρmem : ρ ∈ lemma55ZetaLocalZeroFinset ρ.im := by
    apply (lemma55_mem_actual_zeta_local_zero_finset ρ.im ρ).mpr
    refine ⟨?_, hzero⟩
    rw [mem_closedBall_iff_norm, norm_sub_rev, lemma55_jensen_center_at_zero_height,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith only [hρ1] : 0 ≤ 2 - ρ.re)]
    change 1 - δ < ρ.re at hre
    linarith only [hre, hδsmall]
  have hσ : 1 < σ := by dsimp [σ]; linarith only [hδ]
  have hσ2 : σ ≤ 2 := by dsimp [σ]; linarith only [hδsmall]
  have hbound := lemma81_zeta_three_four_one_zero_inequality hD hL hσ hσ2 hρmem hheight hlow
  have hden : 0 < σ - ρ.re := by linarith only [hσ, hρ1]
  have hden_le : σ - ρ.re ≤ 5 * δ := by
    change 1 - δ < ρ.re at hre
    dsimp [σ]
    linarith only [hre]
  have hinv : 4 / (5 * δ) ≤ 4 / (σ - ρ.re) :=
    div_le_div_of_nonneg_left (by norm_num) hden hden_le
  have he1 : 4 / (5 * δ) = 8000000 * L := by
    dsimp [δ]
    field_simp [hLp.ne']
    ring
  have he2 : 3 / (σ - 1) = 7500000 * L := by
    dsimp [σ, δ]
    field_simp [hLp.ne']
    ring
  rw [he1] at hinv
  rw [he2] at hbound
  change 2000 ≤ L at hL
  change 4 / (σ - ρ.re) ≤ 7500000 * L + 172800 * L + 5 at hbound
  linarith only [hbound, hinv, hL]

/-- The actual analytic pole-removed factor is nonzero on Re s >= 1.
At the pole this uses its genuine analytic continuation value, equal to one. -/
lemma lemma81_zeta_removed_ne_zero_of_one_le_re {z : ℂ} (hz : 1 ≤ z.re) :
    zetaPoleRemoved z ≠ 0 := by
  by_cases h1 : z = 1
  · subst z
    rw [lemma55_actual_zeta_pole_removed_at_one]
    exact one_ne_zero
  · intro hzero
    exact (riemannZeta_ne_zero_of_one_le_re hz)
      ((lemma55_actual_zeta_pole_removed_zero_iff (by linarith only [hz])).mp hzero)

/-- A fixed collar for the entire compact low-height line segment, including
its pole height. The open set is defined using the analytic pole-removed factor. -/
lemma lemma81_zeta_low_height_collar :
    ∃ η : ℝ, 0 < η ∧ ∀ z : ℂ, 1 - η ≤ z.re → |z.im| ≤ 1 → zetaPoleRemoved z ≠ 0 := by
  let S : Set ℂ := (fun t : ℝ => 1 + (t : ℂ) * I) '' Set.Icc (-1 : ℝ) 1
  let U : Set ℂ := {z | 0 < z.re ∧ zetaPoleRemoved z ≠ 0}
  have hS : IsCompact S := isCompact_Icc.image (by fun_prop)
  have hU : IsOpen U := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    have hpos : ∀ᶠ w : ℂ in 𝓝 z, 0 < w.re :=
      (isOpen_lt continuous_const continuous_re).mem_nhds hz.1
    have hne : ∀ᶠ w : ℂ in 𝓝 z, zetaPoleRemoved w ≠ 0 :=
      (lemma55_actual_zeta_pole_removed_analyticAt hz.1).continuousAt.eventually_ne hz.2
    exact hpos.and hne
  have hSU : S ⊆ U := by
    rintro z ⟨t, _ht, rfl⟩
    exact ⟨by simp, lemma81_zeta_removed_ne_zero_of_one_le_re (by simp)⟩
  obtain ⟨η, hη, hthick⟩ := hS.exists_cthickening_subset_open hU hSU
  refine ⟨η, hη, ?_⟩
  intro z hz ht
  by_cases hre : 1 ≤ z.re
  · exact lemma81_zeta_removed_ne_zero_of_one_le_re hre
  have hre1 : z.re ≤ 1 := (lt_of_not_ge hre).le
  have hw : 1 + (z.im : ℂ) * I ∈ S := ⟨z.im, abs_le.mp ht, rfl⟩
  have hd : dist z (1 + (z.im : ℂ) * I) ≤ η := by
    have he : z - (1 + (z.im : ℂ) * I) = ((z.re - 1 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [dist_eq_norm, he, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith only [hre1] : z.re - 1 ≤ 0)]
    linarith only [hz]
  exact (hthick (Metric.mem_cthickening_of_dist_le z (1 + (z.im : ℂ) * I) η S hw hd)).2

/-- Uniform unconditional thin-strip nonvanishing for the actual analytic
pole-removed factor. This is the primary statement used by Perron contours. -/
theorem lemma81_uniform_zeta_pole_removed_thin_strip :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
      1 < D ∧ 2000 ≤ Real.log (D : ℝ) ∧
      ∀ ρ : ℂ, 1 - 1 / (10000000 * Real.log (D : ℝ)) < ρ.re →
        |ρ.im| ≤ D → zetaPoleRemoved ρ ≠ 0 := by
  obtain ⟨η, hη, hlow⟩ := lemma81_zeta_low_height_collar
  have htend : Tendsto (fun D : ℕ => Real.log (D : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have he : ∀ᶠ D : ℕ in atTop,
      max 2000 (1 / (10000000 * η)) ≤ Real.log (D : ℝ) :=
    htend.eventually (eventually_ge_atTop _)
  obtain ⟨D₁, hD₁⟩ := eventually_atTop.mp he
  refine ⟨max 2 D₁, ?_⟩
  intro D hDN
  have hD : 1 < D := lt_of_lt_of_le (by norm_num : (1 : ℕ) < 2)
    ((le_max_left _ _).trans hDN)
  have hlarge := hD₁ D ((le_max_right _ _).trans hDN)
  have hL : 2000 ≤ Real.log (D : ℝ) := (le_max_left _ _).trans hlarge
  have hLp : 0 < Real.log (D : ℝ) := by linarith only [hL]
  have hηL := (le_max_right _ _).trans hlarge
  have hδ : 1 / (10000000 * Real.log (D : ℝ)) ≤ η := by
    apply (div_le_iff₀ (by positivity : 0 < 10000000 * Real.log (D : ℝ))).mpr
    have hh := (div_le_iff₀ (by positivity : 0 < 10000000 * η)).mp hηL
    nlinarith only [hh]
  refine ⟨hD, hL, ?_⟩
  intro ρ hre hheight
  by_cases ht : |ρ.im| ≤ 1
  · exact hlow ρ (by linarith only [hre, hδ]) ht
  · exact lemma81_zeta_high_thin_strip hD hL hre hheight (le_of_not_ge ht)

/-- Ordinary zeta formulation explicitly excludes its pole. -/
theorem lemma81_uniform_zeta_thin_strip :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
      1 < D ∧ 2000 ≤ Real.log (D : ℝ) ∧
      ∀ ρ : ℂ, ρ ≠ 1 → 1 - 1 / (10000000 * Real.log (D : ℝ)) < ρ.re →
        |ρ.im| ≤ D → riemannZeta ρ ≠ 0 := by
  obtain ⟨D₀, hD₀⟩ := lemma81_uniform_zeta_pole_removed_thin_strip
  refine ⟨D₀, ?_⟩
  intro D hDN
  obtain ⟨hD, hL, hfree⟩ := hD₀ D hDN
  refine ⟨hD, hL, ?_⟩
  intro ρ _hρne hre ht hzero
  have hLp : 0 < Real.log (D : ℝ) := by linarith only [hL]
  have hsmall : 1 / (10000000 * Real.log (D : ℝ)) ≤ (1 / 2 : ℝ) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 10000000 * Real.log (D : ℝ))
      (by norm_num)).mpr
    linarith only [hL]
  have hρpos : 0 < ρ.re := by linarith only [hre, hsmall]
  exact hfree ρ hre ht ((lemma55_actual_zeta_pole_removed_zero_iff hρpos).mpr hzero)

end ZhangLS.Spec
