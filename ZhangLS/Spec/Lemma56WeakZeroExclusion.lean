import ZhangLS.Spec.Lemma56FourZeroDetection
import ZhangLS.Spec.Lemma56UniformRepulsionBudget

/-! # Actual weak zero exclusion for distinct nonprincipal primitive characters

This auxiliary excludes actual zeros in Re s>1-2/(log D)^4,
including both height endpoints |Im s|=2D, at one uniform modulus
threshold. It does not assert the original finite prime-window estimate
and does not restrict the modulus-one case in Lemma56Target.
-/

namespace ZhangLS.Spec
open Complex Metric Set
open scoped Real
set_option maxHeartbeats 1000000

def Lemma56WeakZeroRegion (D : ℕ) (s : ℂ) : Prop :=
  1 - 2 / (lemma23PaperL D) ^ 4 < s.re ∧ |s.im| ≤ 2 * (D : ℝ)

lemma lemma56_actual_mixed_paper_upper_bound {D q : ℕ} [NeZero q]
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ q)
    (hD : 1 < D) (hL : 2000 ≤ lemma23PaperL D) (hq : (q : ℝ) < lemma56PaperT D)
    (hθ : θ ≠ 1) (htwist : lemma44CharacterTwist χ θ ≠ 1)
    {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ)) {β R : ℝ}
    (hβ : β ≤ 1) (hzero : dirichletLFunction χ (β : ℂ) = 0)
    (hderiv : deriv (dirichletLFunction χ) (β : ℂ) ≠ 0)
    (hmem : (β : ℂ) ∈ lemma55LocalZeroFinset χ 0) (hR : 0 < R)
    (hlower : ((1 + 2 / lemma23PaperL D)⁻¹) ^ 2 ≤ R)
    (hUlower : ((1 + 2 / (lemma23PaperL D) ^ 4)⁻¹) ^ 2 ≤ R)
    {v : ℂ} (hv : ‖v‖ ≤ 1) (J : ℕ) :
    (lemma56MixedRemainingPower χ θ t R (β : ℂ) v J).re ≤
      475200 * lemma23PaperL D ^ (11 / 10 : ℝ) +
        2 * (1 - β) * (J : ℝ) * ((J : ℝ) + 1) * Real.exp (4 * (J : ℝ) / (lemma23PaperL D) ^ 4) := by
  letI : NeZero (D * q) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne q)⟩
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD.le
  have hqp : (q : ℝ) ≤ (D : ℝ) * lemma56PaperT D := by
    nlinarith [hq.le, lemma56_paper_T_pos D]
  have hDqp : ((D * q : ℕ) : ℝ) ≤ (D : ℝ) * lemma56PaperT D := by
    rw [Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left hq.le (Nat.cast_nonneg _)
  have hθB := lemma56_actual_jensen_log_paper_budget θ hD hL hqp ht
  have htwB := lemma56_actual_jensen_log_paper_budget (lemma44CharacterTwist χ θ) hD hL hDqp ht
  have hL1 : 1 ≤ lemma23PaperL D := by linarith
  have hpower : lemma23PaperL D ≤ lemma23PaperL D ^ (11 / 10 : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hL1 (show (1 : ℝ) ≤ 11 / 10 by norm_num)
  have hLp : 0 < lemma23PaperL D := by linarith
  have hup := lemma56_actual_mixed_remaining_real_upper_bound χ θ hθ htwist hD hL t
    hβ hzero hderiv hmem hR hlower (pow_pos hLp 4) hUlower hv J
  dsimp only [lemma23PaperL] at hθB htwB hpower hup ⊢
  linarith only [hup, hθB, htwB, hpower]

lemma lemma56_weak_region_geometry {L : ℝ} (hL : 2000 ≤ L) :
    0 ≤ 2 / L ^ 4 ∧ 2 / L ^ 4 ≤ 1 / 4 ∧
      ((1 + 2 / L)⁻¹) ^ 2 ≤ ((1 + 2 / L ^ 4)⁻¹) ^ 2 := by
  have hLp : 0 < L := by linarith
  have hL4 := (lemma56_repulsion_scale_bounds hL).2.2
  have hL4p := pow_pos hLp 4
  have hdiv : 2 / L ^ 4 ≤ 2 / L := div_le_div_of_nonneg_left (by norm_num) hLp hL4
  have hi : (1 + 2 / L)⁻¹ ≤ (1 + 2 / L ^ 4)⁻¹ :=
    (inv_le_inv₀ (by positivity) (by positivity)).mpr (by linarith)
  refine ⟨by positivity, ?_, pow_le_pow_left₀ (by positivity) hi 2⟩
  apply (div_le_iff₀ hL4p).mpr
  linarith only [hL4, hL]

theorem lemma56_actual_weak_zero_exclusion {D q : ℕ} [NeZero q]
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ q)
    (hD : 1 < D) (hL : 2000 ≤ lemma23PaperL D)
    (hC : lemma56RepulsionErrorConstant ≤ lemma23PaperL D)
    (hq : (q : ℝ) < lemma56PaperT D) (hθ : θ ≠ 1)
    (htwist : lemma44CharacterTwist χ θ ≠ 1) {β : ℝ}
    (hβ : 0 < 1 - β) (hclose : 1 - β ≤ 64 * lemma23PaperL D ^ (-2022 : ℤ))
    (hzero : dirichletLFunction χ (β : ℂ) = 0)
    (hderiv : deriv (dirichletLFunction χ) (β : ℂ) ≠ 0)
    (hmem : (β : ℂ) ∈ lemma55LocalZeroFinset χ 0) :
    ∀ ρ : ℂ, Lemma56WeakZeroRegion D ρ → DirichletCharacter.LFunction θ ρ ≠ 0 := by
  intro ρ hregion hρzero
  have hg := lemma56_weak_region_geometry hL
  obtain ⟨a₀, _ha₀, hr, _hr1, hUlower, hdet⟩ :=
    lemma56_actual_near_one_zero_four_detected χ θ hD hL hq hθ htwist
      hg.1 hg.2.1 hregion.1 hregion.2 hρzero (β := (β : ℂ))
  let R := ‖lemma56TaggedInverseSquare ρ.im a₀‖
  let v := (lemma56TaggedInverseSquare ρ.im a₀ / (R : ℂ))⁻¹
  have hv : ‖v‖ ≤ 1 := by
    dsimp [v, R]
    rw [norm_inv, norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hr, div_self hr.ne']
    norm_num
  let J := lemma56RepulsionDegree (lemma23PaperL D)
  have hlo := hdet J
  have hup := lemma56_actual_mixed_paper_upper_bound χ θ hD hL hq hθ htwist hregion.2
    (by linarith only [hβ] : β ≤ 1) hzero hderiv hmem hr (hg.2.2.trans hUlower) hUlower hv J
  have hbudget := lemma56_repulsion_strict_budget hL hC hβ.le hclose
  exact (not_lt_of_ge hlo) (hup.trans_lt hbudget)

lemma lemma56_actual_exceptional_zero_local {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hDN : lemma57ExplicitModulusThreshold ≤ D) {β : ℝ}
    (hβ : 0 < 1 - β) (hclose : 1 - β ≤ 64 * lemma23PaperL D ^ (-2022 : ℤ))
    (hzero : dirichletLFunction χ (β : ℂ) = 0) :
    (β : ℂ) ∈ lemma55LocalZeroFinset χ 0 := by
  have hD := lemma57_one_lt_of_explicit_threshold hDN
  have hL := lemma57_log_ge_ten_million hDN
  have hw := (lemma55_local_zero_budget hDN).2.1
  have hdiv : 1 / (4 * Real.log (D : ℝ)) ≤ (1 : ℝ) / 4 := by
    apply (div_le_div_iff₀ (by positivity : 0 < 4 * Real.log (D : ℝ)) (by norm_num)).mpr
    linarith
  have hdist : 1 - β ≤ (1 : ℝ) / 4 :=
    hclose.trans (hw.trans hdiv)
  apply (lemma55_mem_actual_local_zero_finset χ hD 0 (β : ℂ)).mpr
  refine ⟨?_, hzero⟩
  rw [mem_closedBall_iff_norm, norm_sub_rev]
  have hc : lemma55JensenCenter 0 - (β : ℂ) = ((2 - β : ℝ) : ℂ) := by
    simp [lemma55JensenCenter]
  rw [hc, norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < 2 - β)]
  linarith only [hdist]

/-- A uniform actual nonprincipal-character consequence of the original (A).
The complete prime-window target continues to retain the principal case. -/
theorem lemma56_uniform_primitive_weak_zero_exclusion :
    ∃ D₀ : ℕ, ∀ {D q : ℕ} [NeZero q] (χ : RealPrimitiveCharacter D)
      (θ : DirichletCharacter ℂ q), D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
      θ.IsPrimitive → 1 < q → (q : ℝ) < lemma56PaperT D →
      (fun n : ℕ => θ (n : ZMod q)) ≠ (fun n : ℕ => χ.chi (n : ZMod D)) →
      ∀ ρ : ℂ, Lemma56WeakZeroRegion D ρ → DirichletCharacter.LFunction θ ρ ≠ 0 := by
  obtain ⟨Drep, hrep⟩ := lemma56_uniform_repulsion_modulus_threshold
  refine ⟨max Drep lemma57ExplicitModulusThreshold, ?_⟩
  intro D q _ χ θ hDN hD hA hθ hq1 hqT hne
  have hDN57 : lemma57ExplicitModulusThreshold ≤ D := (le_max_right _ _).trans hDN
  have hLM := hrep D ((le_max_left _ _).trans hDN)
  obtain ⟨β, hβ, hclose, hzero, hderiv⟩ := lemma55_actual_simple_real_zero χ hDN57 hA
  exact lemma56_actual_weak_zero_exclusion χ θ hD hLM.1 hLM.2 hqT
    (lemma56_primitive_positive_level_nonprincipal θ hθ hq1)
    (lemma56_distinct_primitive_twist_nonprincipal χ θ hθ hne) hβ hclose hzero hderiv
    (lemma56_actual_exceptional_zero_local χ hDN57 hβ hclose hzero)

end ZhangLS.Spec
