import ZhangLS.Spec.Lemma56JensenBounds

/-! # Actual finite zero sets and natural analytic multiplicities

Actual Dirichlet L-functions and their actual analytic orders are retained.
These auxiliary results do not assert the complete Lemma 5.6 prime-window estimate.
-/

namespace ZhangLS.Spec
open Complex Metric Set Filter MeromorphicOn Finset
open scoped Topology Real
set_option maxHeartbeats 1000000

noncomputable def lemma56LocalZeroFinset {r : ℕ} [NeZero r]
    (θ : DirichletCharacter ℂ r) (t : ℝ) : Finset ℂ :=
  ((divisor (DirichletCharacter.LFunction θ)
    (closedBall (lemma55JensenCenter t) (5 / 4 : ℝ))).finiteSupport
      (isCompact_closedBall _ _)).toFinset

theorem lemma56_actual_analytic_order_finite
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) (ρ : ℂ) :
    analyticOrderAt (DirichletCharacter.LFunction θ) ρ ≠ ⊤ := by
  have ha := lemma56_actual_L_analyticOnNhd θ hθ
  have htwo : analyticOrderAt (DirichletCharacter.LFunction θ) (lemma55JensenCenter 0) = 0 :=
    (ha _ (mem_univ _)).analyticOrderAt_eq_zero.mpr
      (lemma56_actual_jensen_center_ne_zero θ 0)
  exact ha.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (mem_univ _) (mem_univ _) (by rw [htwo]; simp)

theorem lemma56_actual_local_divisor_eq_order
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1)
    {t : ℝ} {ρ : ℂ} (hρ : ρ ∈ closedBall (lemma55JensenCenter t) (5 / 4 : ℝ)) :
    divisor (DirichletCharacter.LFunction θ) (closedBall (lemma55JensenCenter t) (5 / 4 : ℝ)) ρ =
      (analyticOrderNatAt (DirichletCharacter.LFunction θ) ρ : ℤ) := by
  have ha := (lemma56_actual_L_analyticOnNhd θ hθ).mono
    (subset_univ (closedBall (lemma55JensenCenter t) (5 / 4 : ℝ)))
  rw [ha.divisor_apply hρ, ← Nat.cast_analyticOrderNatAt
    (lemma56_actual_analytic_order_finite θ hθ ρ)]
  simp

theorem lemma56_mem_actual_local_zero_finset
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) (t : ℝ) (ρ : ℂ) :
    ρ ∈ lemma56LocalZeroFinset θ t ↔
      ρ ∈ closedBall (lemma55JensenCenter t) (5 / 4 : ℝ) ∧ DirichletCharacter.LFunction θ ρ = 0 := by
  classical
  let d := divisor (DirichletCharacter.LFunction θ) (closedBall (lemma55JensenCenter t) (5 / 4 : ℝ))
  have hmem : ρ ∈ lemma56LocalZeroFinset θ t ↔ ρ ∈ Function.support d := by
    simp [lemma56LocalZeroFinset, d]
  rw [hmem]
  constructor
  · intro hsupp
    have hρ : ρ ∈ closedBall (lemma55JensenCenter t) (5 / 4 : ℝ) :=
      d.supportWithinDomain hsupp
    have hNZ : analyticOrderNatAt (DirichletCharacter.LFunction θ) ρ ≠ 0 := by
      intro hzero
      have hd := lemma56_actual_local_divisor_eq_order θ hθ hρ
      rw [hzero, Nat.cast_zero] at hd
      exact hsupp hd
    exact ⟨hρ, apply_eq_zero_of_analyticOrderNatAt_ne_zero hNZ⟩
  · rintro ⟨hρ, hzero⟩
    change d ρ ≠ 0
    dsimp [d]
    rw [lemma56_actual_local_divisor_eq_order θ hθ hρ]
    have hNZ : analyticOrderNatAt (DirichletCharacter.LFunction θ) ρ ≠ 0 := by
      intro hnat
      have ho : analyticOrderAt (DirichletCharacter.LFunction θ) ρ = 0 := by
        rw [← Nat.cast_analyticOrderNatAt (lemma56_actual_analytic_order_finite θ hθ ρ), hnat]
        rfl
      have haρ := lemma56_actual_L_analyticOnNhd θ hθ ρ (mem_univ ρ)
      exact (haρ.analyticOrderAt_eq_zero.mp ho) hzero
    exact_mod_cast hNZ

theorem lemma56_actual_local_zero_order_pos
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) {t : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ lemma56LocalZeroFinset θ t) :
    1 ≤ analyticOrderNatAt (DirichletCharacter.LFunction θ) ρ := by
  have hzero := (lemma56_mem_actual_local_zero_finset θ hθ t ρ).mp hρ
  apply Nat.one_le_iff_ne_zero.mpr
  intro hnat
  have ho : analyticOrderAt (DirichletCharacter.LFunction θ) ρ = 0 := by
    rw [← Nat.cast_analyticOrderNatAt (lemma56_actual_analytic_order_finite θ hθ ρ), hnat]
    rfl
  have haρ := lemma56_actual_L_analyticOnNhd θ hθ ρ (mem_univ ρ)
  exact (haρ.analyticOrderAt_eq_zero.mp ho) hzero.2

theorem lemma56_actual_multiplicity_count_eq_sum_orders
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) (t : ℝ) :
    lemma56JensenMultiplicityCount θ t =
      ∑ ρ ∈ lemma56LocalZeroFinset θ t, (analyticOrderNatAt (DirichletCharacter.LFunction θ) ρ : ℤ) := by
  classical
  let d := divisor (DirichletCharacter.LFunction θ) (closedBall (lemma55JensenCenter t) (5 / 4 : ℝ))
  have heq : lemma56JensenMultiplicityCount θ t = ∑ ρ ∈ lemma56LocalZeroFinset θ t, d ρ := by
    exact finsum_eq_sum d (d.finiteSupport (isCompact_closedBall _ _))
  rw [heq]
  apply Finset.sum_congr rfl
  intro ρ hρ
  exact lemma56_actual_local_divisor_eq_order θ hθ
    ((lemma56_mem_actual_local_zero_finset θ hθ t ρ).mp hρ).1

theorem lemma56_actual_local_zero_card_bound
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) (t : ℝ) :
    ((lemma56LocalZeroFinset θ t).card : ℝ) ≤
      6 * Real.log (8 * (r : ℝ) * (7 / 2 + |t|)) := by
  have hsum : ∑ ρ ∈ lemma56LocalZeroFinset θ t, (1 : ℤ) ≤
      ∑ ρ ∈ lemma56LocalZeroFinset θ t, (analyticOrderNatAt (DirichletCharacter.LFunction θ) ρ : ℤ) := by
    apply Finset.sum_le_sum
    intro ρ hρ
    exact_mod_cast lemma56_actual_local_zero_order_pos θ hθ hρ
  rw [← lemma56_actual_multiplicity_count_eq_sum_orders θ hθ t] at hsum
  have hcard : ((lemma56LocalZeroFinset θ t).card : ℝ) ≤
      (lemma56JensenMultiplicityCount θ t : ℝ) := by
    have hi : ((lemma56LocalZeroFinset θ t).card : ℤ) ≤ lemma56JensenMultiplicityCount θ t := by
      simpa using hsum
    exact_mod_cast hi
  exact hcard.trans (lemma56_actual_jensen_multiplicity_bound θ hθ t)

end ZhangLS.Spec
