import ZhangLS.Spec.Lemma55JensenZeroCount

/-!
# Finite sets of actual local zeros and their actual multiplicities

The divisor support is proved to be exactly the actual L-function zero
set in the closed disk. Global analytic continuation and a nonzero value
at two rule out infinite analytic order everywhere. Consequently the
Jensen divisor sum equals the sum of the actual natural-number orders.
-/

namespace ZhangLS.Spec

open Complex Metric Set MeromorphicOn
open scoped Real

noncomputable def lemma55LocalZeroFinset {D : ℕ}
    (χ : RealPrimitiveCharacter D) (t : ℝ) : Finset ℂ :=
  ((divisor (dirichletLFunction χ)
    (closedBall (lemma55JensenCenter t) (5 / 4 : ℝ))).finiteSupport
      (isCompact_closedBall _ _)).toFinset

theorem lemma55_actual_analytic_order_finite
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) (ρ : ℂ) :
    analyticOrderAt (dirichletLFunction χ) ρ ≠ ⊤ := by
  have ha := lemma55_actual_L_analyticOnNhd χ hD
  have htwo : analyticOrderAt (dirichletLFunction χ) (lemma55JensenCenter 0) = 0 :=
    (ha _ (mem_univ _)).analyticOrderAt_eq_zero.mpr
      (lemma55_actual_jensen_center_ne_zero χ 0)
  exact ha.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (mem_univ _) (mem_univ _) (by rw [htwo]; simp)

theorem lemma55_actual_local_divisor_eq_order
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    {t : ℝ} {ρ : ℂ} (hρ : ρ ∈ closedBall (lemma55JensenCenter t) (5 / 4 : ℝ)) :
    divisor (dirichletLFunction χ) (closedBall (lemma55JensenCenter t) (5 / 4 : ℝ)) ρ =
      (analyticOrderNatAt (dirichletLFunction χ) ρ : ℤ) := by
  have ha := (lemma55_actual_L_analyticOnNhd χ hD).mono
    (subset_univ (closedBall (lemma55JensenCenter t) (5 / 4 : ℝ)))
  rw [ha.divisor_apply hρ, ← Nat.cast_analyticOrderNatAt
    (lemma55_actual_analytic_order_finite χ hD ρ)]
  simp

theorem lemma55_mem_actual_local_zero_finset
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) (t : ℝ) (ρ : ℂ) :
    ρ ∈ lemma55LocalZeroFinset χ t ↔
      ρ ∈ closedBall (lemma55JensenCenter t) (5 / 4 : ℝ) ∧ dirichletLFunction χ ρ = 0 := by
  classical
  let d := divisor (dirichletLFunction χ) (closedBall (lemma55JensenCenter t) (5 / 4 : ℝ))
  have hmem : ρ ∈ lemma55LocalZeroFinset χ t ↔ ρ ∈ Function.support d := by
    simp [lemma55LocalZeroFinset, d]
  rw [hmem]
  constructor
  · intro hsupp
    have hρ : ρ ∈ closedBall (lemma55JensenCenter t) (5 / 4 : ℝ) :=
      d.supportWithinDomain hsupp
    have hNZ : analyticOrderNatAt (dirichletLFunction χ) ρ ≠ 0 := by
      intro hzero
      have hd := lemma55_actual_local_divisor_eq_order χ hD hρ
      rw [hzero, Nat.cast_zero] at hd
      exact hsupp hd
    exact ⟨hρ, apply_eq_zero_of_analyticOrderNatAt_ne_zero hNZ⟩
  · rintro ⟨hρ, hzero⟩
    change d ρ ≠ 0
    dsimp [d]
    rw [lemma55_actual_local_divisor_eq_order χ hD hρ]
    have hNZ : analyticOrderNatAt (dirichletLFunction χ) ρ ≠ 0 := by
      intro hnat
      have ho : analyticOrderAt (dirichletLFunction χ) ρ = 0 := by
        rw [← Nat.cast_analyticOrderNatAt (lemma55_actual_analytic_order_finite χ hD ρ), hnat]
        rfl
      have haρ := lemma55_actual_L_analyticOnNhd χ hD ρ (mem_univ ρ)
      exact (haρ.analyticOrderAt_eq_zero.mp ho) hzero
    exact_mod_cast hNZ

theorem lemma55_actual_local_zero_order_pos
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) {t : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ lemma55LocalZeroFinset χ t) :
    1 ≤ analyticOrderNatAt (dirichletLFunction χ) ρ := by
  have hzero := (lemma55_mem_actual_local_zero_finset χ hD t ρ).mp hρ
  apply Nat.one_le_iff_ne_zero.mpr
  intro hnat
  have ho : analyticOrderAt (dirichletLFunction χ) ρ = 0 := by
    rw [← Nat.cast_analyticOrderNatAt (lemma55_actual_analytic_order_finite χ hD ρ), hnat]
    rfl
  have haρ := lemma55_actual_L_analyticOnNhd χ hD ρ (mem_univ ρ)
  exact (haρ.analyticOrderAt_eq_zero.mp ho) hzero.2

theorem lemma55_actual_multiplicity_count_eq_sum_orders
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) (t : ℝ) :
    lemma55JensenMultiplicityCount χ t =
      ∑ ρ ∈ lemma55LocalZeroFinset χ t, (analyticOrderNatAt (dirichletLFunction χ) ρ : ℤ) := by
  classical
  let d := divisor (dirichletLFunction χ) (closedBall (lemma55JensenCenter t) (5 / 4 : ℝ))
  have heq : lemma55JensenMultiplicityCount χ t = ∑ ρ ∈ lemma55LocalZeroFinset χ t, d ρ := by
    exact finsum_eq_sum d (d.finiteSupport (isCompact_closedBall _ _))
  rw [heq]
  apply Finset.sum_congr rfl
  intro ρ hρ
  exact lemma55_actual_local_divisor_eq_order χ hD
    ((lemma55_mem_actual_local_zero_finset χ hD t ρ).mp hρ).1

theorem lemma55_actual_local_zero_card_bound
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ)) :
    ((lemma55LocalZeroFinset χ t).card : ℝ) ≤ 13 * Real.log (D : ℝ) := by
  have hsum : ∑ ρ ∈ lemma55LocalZeroFinset χ t, (1 : ℤ) ≤
      ∑ ρ ∈ lemma55LocalZeroFinset χ t, (analyticOrderNatAt (dirichletLFunction χ) ρ : ℤ) := by
    apply Finset.sum_le_sum
    intro ρ hρ
    exact_mod_cast lemma55_actual_local_zero_order_pos χ hD hρ
  rw [← lemma55_actual_multiplicity_count_eq_sum_orders χ hD t] at hsum
  have hcard : ((lemma55LocalZeroFinset χ t).card : ℝ) ≤
      (lemma55JensenMultiplicityCount χ t : ℝ) := by
    have hi : ((lemma55LocalZeroFinset χ t).card : ℤ) ≤ lemma55JensenMultiplicityCount χ t := by
      simpa using hsum
    exact_mod_cast hi
  exact hcard.trans (lemma55_actual_jensen_multiplicity_bound χ hD hL ht)

end ZhangLS.Spec
