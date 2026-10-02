import ZhangLS.Spec.Lemma56LogBudgetZeroExclusion

/-! # Uniform actual zero exclusion at exponential heights

Actual L-functions and their actual zeros and analytic orders are retained.
The original finite prime-window target remains a separate unproved obligation.
-/

namespace ZhangLS.Spec
open Complex Metric Set Finset Filter
open scoped Real Topology
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

lemma lemma56_actual_jensen_log_high_budget {D q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) (hD : 1 < D) (hL : 2000 ≤ lemma23PaperL D)
    (hq : (q : ℝ) ≤ (D : ℝ) * lemma56PaperT D) {U : ℝ}
    (hU : 2000 ≤ U) (hPU : lemma23PaperL D ^ (11 / 10 : ℝ) ≤ U)
    {t : ℝ} (ht : |t| ≤ 2 * Real.exp U) :
    lemma56JensenLogSize θ t ≤ 4 * U := by
  have hDp : (0 : ℝ) < D := by exact_mod_cast Nat.zero_lt_of_lt hD
  have hqp : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hT := lemma56_paper_T_pos D
  have hL1 : 1 ≤ lemma23PaperL D := by linarith
  have hpower : lemma23PaperL D ≤ lemma23PaperL D ^ (11 / 10 : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hL1 (show (1 : ℝ) ≤ 11 / 10 by norm_num)
  have he1 : 1 ≤ Real.exp U := Real.one_le_exp (by linarith)
  have hX : 8 * (q : ℝ) * (7 / 2 + |t|) ≤ 44 * (D : ℝ) * lemma56PaperT D * Real.exp U := by
    calc
      _ ≤ 8 * ((D : ℝ) * lemma56PaperT D) * (7 / 2 + 2 * Real.exp U) := by gcongr
      _ ≤ 8 * ((D : ℝ) * lemma56PaperT D) * ((11 / 2 : ℝ) * Real.exp U) := by
        gcongr
        linarith
      _ = _ := by ring
  unfold lemma56JensenLogSize
  calc
    _ ≤ Real.log (44 * (D : ℝ) * lemma56PaperT D * Real.exp U) := Real.log_le_log (by positivity) hX
    _ = Real.log 44 + lemma23PaperL D + lemma23PaperL D ^ (11 / 10 : ℝ) + U := by
      rw [Real.log_mul (by positivity) (Real.exp_pos U).ne', Real.log_mul (by positivity) hT.ne',
        Real.log_mul (by norm_num) hDp.ne']
      simp [lemma56PaperT, lemma23PaperL]
    _ ≤ _ := by
      have hc := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 44)
      norm_num at hc
      linarith only [hc, hpower, hPU, hU]

lemma lemma56_high_repulsion_scale_bounds {L : ℝ} (hL : 2000 ≤ L) :
    L ≤ L ^ (9 / 2 : ℝ) ∧ L ^ (11 / 10 : ℝ) ≤ L ^ (9 / 2 : ℝ) ∧
      L ^ (9 / 2 : ℝ) ≤ L ^ 5 := by
  have hL1 : 1 ≤ L := by linarith
  refine ⟨?_, Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num), ?_⟩
  · simpa using Real.rpow_le_rpow_of_exponent_le hL1 (show (1 : ℝ) ≤ 9 / 2 by norm_num)
  · simpa using Real.rpow_le_rpow_of_exponent_le hL1 (show (9 / 2 : ℝ) ≤ 5 by norm_num)

theorem lemma56_uniform_primitive_high_zero_exclusion :
    ∃ D₀ : ℕ, ∀ {D q : ℕ} [NeZero q] (χ : RealPrimitiveCharacter D)
      (θ : DirichletCharacter ℂ q), D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
      θ.IsPrimitive → 1 < q → (q : ℝ) < lemma56PaperT D →
      (fun n : ℕ => θ (n : ZMod q)) ≠ (fun n : ℕ => χ.chi (n : ZMod D)) →
      ∀ ρ : ℂ, 1 - 2 / (lemma23PaperL D ^ (9 / 2 : ℝ)) < ρ.re →
        |ρ.im| ≤ 2 * Real.exp (lemma23PaperL D ^ (9 / 2 : ℝ)) →
          DirichletCharacter.LFunction θ ρ ≠ 0 := by
  obtain ⟨Drep, hrep⟩ := lemma56_uniform_repulsion_modulus_threshold
  refine ⟨max Drep lemma57ExplicitModulusThreshold, ?_⟩
  intro D q _ χ θ hDN hD hA hθ hq1 hqT hne ρ hre ht
  letI : NeZero (D * q) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne q)⟩
  have hDN57 : lemma57ExplicitModulusThreshold ≤ D := (le_max_right _ _).trans hDN
  have hLM := hrep D ((le_max_left _ _).trans hDN)
  have hs := lemma56_high_repulsion_scale_bounds hLM.1
  have hU : 2000 ≤ lemma23PaperL D ^ (9 / 2 : ℝ) := hLM.1.trans hs.1
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD.le
  have hqp : (q : ℝ) ≤ (D : ℝ) * lemma56PaperT D := by
    nlinarith only [hqT.le, hD1, lemma56_paper_T_pos D]
  have hDqp : ((D * q : ℕ) : ℝ) ≤ (D : ℝ) * lemma56PaperT D := by
    rw [Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left hqT.le (Nat.cast_nonneg _)
  obtain ⟨β, hβ, hclose, hzero, hderiv⟩ := lemma55_actual_simple_real_zero χ hDN57 hA
  exact lemma56_actual_log_budget_zero_exclusion χ θ hD hLM.1 hLM.2
    (lemma56_primitive_positive_level_nonprincipal θ hθ hq1)
    (lemma56_distinct_primitive_twist_nonprincipal χ θ hθ hne) hU hs.1 hs.2.2
    hβ hclose hzero hderiv (lemma56_actual_exceptional_zero_local χ hDN57 hβ hclose hzero) hre
    (lemma56_actual_jensen_log_high_budget θ hD hLM.1 hqp hU hs.2.1 ht)
    (lemma56_actual_jensen_log_high_budget (lemma44CharacterTwist χ θ) hD hLM.1 hDqp hU hs.2.1 ht)

end ZhangLS.Spec
