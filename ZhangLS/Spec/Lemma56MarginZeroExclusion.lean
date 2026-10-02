import ZhangLS.Spec.Lemma56HighLogDerivative

/-! # Actual high zero exclusion retaining a strict exponent margin

Actual L-functions and their actual zeros and analytic orders are retained.
The original finite prime-window target remains a separate unproved obligation.
-/

namespace ZhangLS.Spec
open Complex Metric Set Finset Filter
open scoped Real Topology
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

lemma lemma56_high_scale_strict_margin {L : ℝ} (hL : 2000 ≤ L) :
    8 * L ^ (11 / 10 : ℝ) ≤ L ^ (9 / 2 : ℝ) ∧
      L ≤ (3 / 4 : ℝ) * L ^ (9 / 2 : ℝ) ∧
      2000 ≤ (3 / 4 : ℝ) * L ^ (9 / 2 : ℝ) ∧
      (3 / 4 : ℝ) * L ^ (9 / 2 : ℝ) ≤ L ^ 5 := by
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hLP := (lemma56_repulsion_scale_bounds hL).2.1
  have hLU := (lemma56_high_repulsion_scale_bounds hL).1
  have hU5 := (lemma56_high_repulsion_scale_bounds hL).2.2
  have h3 : L ^ 3 ≤ L ^ (9 / 2 : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hL1 (show (3 : ℝ) ≤ 9 / 2 by norm_num)
  have h82 : 8 * L ^ 2 ≤ L ^ 3 := by
    have hn := mul_le_mul_of_nonneg_right (by linarith : (8 : ℝ) ≤ L) (sq_nonneg L)
    nlinarith only [hn]
  have h8U : 8 * L ≤ L ^ (9 / 2 : ℝ) := by
    have hL2 : L ≤ L ^ 2 := by nlinarith only [hL1]
    linarith only [hL2, h82, h3]
  exact ⟨(mul_le_mul_of_nonneg_left hLP (by norm_num)).trans (h82.trans h3),
    by linarith only [h8U, hL0], by linarith only [h8U, hL],
    (by have hp := Real.rpow_nonneg hL0 (9 / 2 : ℝ); linarith only [hU5, hp])⟩

lemma lemma56_actual_jensen_log_margin_budget {D q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) (hD : 1 < D) (hL : 2000 ≤ lemma23PaperL D)
    (hq : (q : ℝ) ≤ (D : ℝ) * lemma56PaperT D) {t : ℝ}
    (ht : |t| ≤ 2 * Real.exp (2 * lemma23PaperL D ^ (9 / 2 : ℝ))) :
    lemma56JensenLogSize θ t ≤ 4 * ((3 / 4 : ℝ) * lemma23PaperL D ^ (9 / 2 : ℝ)) := by
  have hDp : (0 : ℝ) < D := by exact_mod_cast Nat.zero_lt_of_lt hD
  have hqp : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hT := lemma56_paper_T_pos D
  have hLp : 0 ≤ lemma23PaperL D := by linarith
  have hL1 : 1 ≤ lemma23PaperL D := by linarith
  have hU0 := Real.rpow_nonneg hLp (9 / 2 : ℝ)
  have he1 : 1 ≤ Real.exp (2 * lemma23PaperL D ^ (9 / 2 : ℝ)) := Real.one_le_exp (by positivity)
  have hX : 8 * (q : ℝ) * (7 / 2 + |t|) ≤
      44 * (D : ℝ) * lemma56PaperT D * Real.exp (2 * lemma23PaperL D ^ (9 / 2 : ℝ)) := by
    calc
      _ ≤ 8 * ((D : ℝ) * lemma56PaperT D) *
          (7 / 2 + 2 * Real.exp (2 * lemma23PaperL D ^ (9 / 2 : ℝ))) := by gcongr
      _ ≤ 8 * ((D : ℝ) * lemma56PaperT D) *
          ((11 / 2 : ℝ) * Real.exp (2 * lemma23PaperL D ^ (9 / 2 : ℝ))) := by
        gcongr
        linarith only [he1]
      _ = _ := by ring
  have hpower : lemma23PaperL D ≤ lemma23PaperL D ^ (11 / 10 : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hL1 (show (1 : ℝ) ≤ 11 / 10 by norm_num)
  have h8 := (lemma56_high_scale_strict_margin hL).1
  unfold lemma56JensenLogSize
  calc
    _ ≤ Real.log (44 * (D : ℝ) * lemma56PaperT D * Real.exp (2 * lemma23PaperL D ^ (9 / 2 : ℝ))) :=
      Real.log_le_log (by positivity) hX
    _ = Real.log 44 + lemma23PaperL D + lemma23PaperL D ^ (11 / 10 : ℝ) +
        2 * lemma23PaperL D ^ (9 / 2 : ℝ) := by
      rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_mul (by positivity) hT.ne',
        Real.log_mul (by norm_num) hDp.ne']
      simp [lemma56PaperT, lemma23PaperL]
    _ ≤ _ := by
      have hc := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 44)
      norm_num at hc
      linarith only [hc, h8, hpower, hL]

theorem lemma56_uniform_primitive_margin_zero_exclusion :
    ∃ D₀ : ℕ, ∀ {D q : ℕ} [NeZero q] (χ : RealPrimitiveCharacter D)
      (θ : DirichletCharacter ℂ q), D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
      θ.IsPrimitive → 1 < q → (q : ℝ) < lemma56PaperT D →
      (fun n : ℕ => θ (n : ZMod q)) ≠ (fun n : ℕ => χ.chi (n : ZMod D)) →
      ∀ ρ : ℂ, 1 - 2 / ((3 / 4 : ℝ) * lemma23PaperL D ^ (9 / 2 : ℝ)) < ρ.re →
        |ρ.im| ≤ 2 * Real.exp (2 * lemma23PaperL D ^ (9 / 2 : ℝ)) →
          DirichletCharacter.LFunction θ ρ ≠ 0 := by
  obtain ⟨Drep, hrep⟩ := lemma56_uniform_repulsion_modulus_threshold
  refine ⟨max Drep lemma57ExplicitModulusThreshold, ?_⟩
  intro D q _ χ θ hDN hD hA hθ hq1 hqT hne ρ hre ht
  letI : NeZero (D * q) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne q)⟩
  have hDN57 : lemma57ExplicitModulusThreshold ≤ D := (le_max_right _ _).trans hDN
  have hLM := hrep D ((le_max_left _ _).trans hDN)
  have hs := lemma56_high_scale_strict_margin hLM.1
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD.le
  have hqp : (q : ℝ) ≤ (D : ℝ) * lemma56PaperT D := by
    nlinarith only [hqT.le, hD1, lemma56_paper_T_pos D]
  have hDqp : ((D * q : ℕ) : ℝ) ≤ (D : ℝ) * lemma56PaperT D := by
    rw [Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left hqT.le (Nat.cast_nonneg _)
  obtain ⟨β, hβ, hclose, hzero, hderiv⟩ := lemma55_actual_simple_real_zero χ hDN57 hA
  exact lemma56_actual_log_budget_zero_exclusion χ θ hD hLM.1 hLM.2
    (lemma56_primitive_positive_level_nonprincipal θ hθ hq1)
    (lemma56_distinct_primitive_twist_nonprincipal χ θ hθ hne) hs.2.2.1 hs.2.1 hs.2.2.2
    hβ hclose hzero hderiv (lemma56_actual_exceptional_zero_local χ hDN57 hβ hclose hzero) hre
    (lemma56_actual_jensen_log_margin_budget θ hD hLM.1 hqp ht)
    (lemma56_actual_jensen_log_margin_budget (lemma44CharacterTwist χ θ) hD hLM.1 hDqp ht)

end ZhangLS.Spec
