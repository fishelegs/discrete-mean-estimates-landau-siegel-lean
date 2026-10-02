import ZhangLS.Spec.Lemma56MixedPowerUpperBound
import ZhangLS.Spec.Lemma55FourZeroFamilies

/-! # Four actual mixed zero families and paper-size budgets

The tags distinguish chi and zeta at height zero from theta and chi theta
at height t, retaining actual functions and multiplicities when t=0.
-/
namespace ZhangLS.Spec
open Complex Finset Metric Set
open scoped Real
set_option maxHeartbeats 1000000

abbrev Lemma56TaggedZero := Σ _ : Fin 4, ℂ

noncomputable def lemma56ZeroFamily {D q : ℕ} [NeZero q]
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ q)
    (t : ℝ) (β : ℂ) (i : Fin 4) : Finset ℂ :=
  letI : NeZero (D * q) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne q)⟩
  ![lemma55ExceptionalRemovedLocalZeros χ 0 β, lemma55ZetaLocalZeroFinset 0,
    lemma56LocalZeroFinset θ t, lemma56LocalZeroFinset (lemma44CharacterTwist χ θ) t] i

noncomputable def lemma56FamilyFunction {D q : ℕ} [NeZero q]
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ q) (i : Fin 4) : ℂ → ℂ :=
  letI : NeZero (D * q) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne q)⟩
  ![dirichletLFunction χ, zetaPoleRemoved, DirichletCharacter.LFunction θ,
    DirichletCharacter.LFunction (lemma44CharacterTwist χ θ)] i

noncomputable def lemma56FamilyOrder {D q : ℕ} [NeZero q]
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ q) (i : Fin 4) (ρ : ℂ) : ℕ :=
  analyticOrderNatAt (lemma56FamilyFunction χ θ i) ρ

noncomputable def lemma56FourZeroFinset {D q : ℕ} [NeZero q]
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ q)
    (t : ℝ) (β : ℂ) : Finset Lemma56TaggedZero :=
  univ.sigma (lemma56ZeroFamily χ θ t β)

noncomputable def lemma56TaggedInverseSquare (t : ℝ) (a : Lemma56TaggedZero) : ℂ :=
  lemma55ZeroInverseSquare (lemma55FamilyHeight t a.1) a.2

lemma lemma56_mem_four_zero_finset {D q : ℕ} [NeZero q]
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ q)
    (t : ℝ) (β : ℂ) (a : Lemma56TaggedZero) :
    a ∈ lemma56FourZeroFinset χ θ t β ↔ a.2 ∈ lemma56ZeroFamily χ θ t β a.1 := by
  classical
  simp [lemma56FourZeroFinset]

lemma lemma56_actual_tagged_zero_order_pos {D q : ℕ} [NeZero q]
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ q)
    (hD : 1 < D) (hθ : θ ≠ 1) (htwist : lemma44CharacterTwist χ θ ≠ 1)
    {t : ℝ} {β : ℂ} {a : Lemma56TaggedZero}
    (ha : a ∈ lemma56FourZeroFinset χ θ t β) :
    1 ≤ lemma56FamilyOrder χ θ a.1 a.2 := by
  letI : NeZero (D * q) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne q)⟩
  obtain ⟨i, ρ⟩ := a
  have hρ := (lemma56_mem_four_zero_finset χ θ t β ⟨i, ρ⟩).mp ha
  fin_cases i <;> simp [lemma56ZeroFamily] at hρ
  · change 1 ≤ analyticOrderNatAt (dirichletLFunction χ) ρ
    exact lemma55_actual_local_zero_order_pos χ hD (erase_subset _ _ hρ)
  · change 1 ≤ analyticOrderNatAt zetaPoleRemoved ρ
    exact lemma55_actual_zeta_local_zero_order_pos hρ
  · change 1 ≤ analyticOrderNatAt (DirichletCharacter.LFunction θ) ρ
    exact lemma56_actual_local_zero_order_pos θ hθ hρ
  · change 1 ≤ analyticOrderNatAt (DirichletCharacter.LFunction (lemma44CharacterTwist χ θ)) ρ
    exact lemma56_actual_local_zero_order_pos (lemma44CharacterTwist χ θ) htwist hρ

lemma lemma56_actual_tagged_inverse_square_bounds {D q : ℕ} [NeZero q]
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ q)
    (hD : 1 < D) (hθ : θ ≠ 1) (htwist : lemma44CharacterTwist χ θ ≠ 1)
    {t : ℝ} {β : ℂ} {a : Lemma56TaggedZero}
    (ha : a ∈ lemma56FourZeroFinset χ θ t β) :
    0 < ‖lemma56TaggedInverseSquare t a‖ ∧ ‖lemma56TaggedInverseSquare t a‖ < 1 := by
  letI : NeZero (D * q) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne q)⟩
  obtain ⟨i, ρ⟩ := a
  have hρ := (lemma56_mem_four_zero_finset χ θ t β ⟨i, ρ⟩).mp ha
  fin_cases i <;> simp [lemma56ZeroFamily] at hρ
  · change 0 < ‖lemma55ZeroInverseSquare 0 ρ‖ ∧ ‖lemma55ZeroInverseSquare 0 ρ‖ < 1
    exact lemma55_actual_inverse_square_norm_bounds χ hD (erase_subset _ _ hρ)
  · change 0 < ‖lemma55ZeroInverseSquare 0 ρ‖ ∧ ‖lemma55ZeroInverseSquare 0 ρ‖ < 1
    exact lemma55_actual_zeta_inverse_square_norm_bounds hρ
  · change 0 < ‖lemma55ZeroInverseSquare t ρ‖ ∧ ‖lemma55ZeroInverseSquare t ρ‖ < 1
    exact lemma56_actual_inverse_square_norm_bounds θ hθ hρ
  · change 0 < ‖lemma55ZeroInverseSquare t ρ‖ ∧ ‖lemma55ZeroInverseSquare t ρ‖ < 1
    exact lemma56_actual_inverse_square_norm_bounds (lemma44CharacterTwist χ θ) htwist hρ

lemma lemma56_actual_jensen_log_paper_budget {D q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) (hD : 1 < D)
    (hL : 2000 ≤ lemma23PaperL D) (hq : (q : ℝ) ≤ (D : ℝ) * lemma56PaperT D)
    {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ)) :
    lemma56JensenLogSize θ t ≤ 4 * lemma23PaperL D ^ (11 / 10 : ℝ) := by
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD.le
  have hDp : (0 : ℝ) < D := by linarith
  have hqp : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hT := lemma56_paper_T_pos D
  have hL1 : 1 ≤ lemma23PaperL D := by linarith
  have hpower : lemma23PaperL D ≤ lemma23PaperL D ^ (11 / 10 : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hL1 (show (1 : ℝ) ≤ 11 / 10 by norm_num)
  have hX : 8 * (q : ℝ) * (7 / 2 + |t|) ≤ 44 * (D : ℝ) ^ 2 * lemma56PaperT D := by
    calc
      _ ≤ 8 * ((D : ℝ) * lemma56PaperT D) * (7 / 2 + 2 * (D : ℝ)) := by gcongr
      _ ≤ 8 * ((D : ℝ) * lemma56PaperT D) * ((11 / 2 : ℝ) * (D : ℝ)) := by
        gcongr
        linarith
      _ = _ := by ring
  unfold lemma56JensenLogSize
  calc
    _ ≤ Real.log (44 * (D : ℝ) ^ 2 * lemma56PaperT D) := Real.log_le_log (by positivity) hX
    _ = Real.log 44 + 2 * lemma23PaperL D + lemma23PaperL D ^ (11 / 10 : ℝ) := by
      rw [Real.log_mul (by positivity) hT.ne', Real.log_mul (by norm_num)
        (pow_ne_zero 2 hDp.ne'), Real.log_pow]
      simp only [lemma56PaperT, Real.log_exp, lemma23PaperL]
      norm_num
    _ ≤ _ := by
      have hc := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 44)
      norm_num at hc
      linarith

lemma lemma56_actual_local_order_sum_paper_budget {D q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) (hθ : θ ≠ 1) (hD : 1 < D)
    (hL : 2000 ≤ lemma23PaperL D) (hq : (q : ℝ) ≤ (D : ℝ) * lemma56PaperT D)
    {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ)) :
    (∑ ρ ∈ lemma56LocalZeroFinset θ t, (analyticOrderNatAt (DirichletCharacter.LFunction θ) ρ : ℝ)) ≤
      24 * lemma23PaperL D ^ (11 / 10 : ℝ) := by
  have hb := lemma56_actual_jensen_paper_budget θ hθ hD hL hq ht
  rw [lemma56_actual_multiplicity_count_eq_sum_orders θ hθ t] at hb
  push_cast at hb
  exact hb

lemma lemma56_actual_four_zero_order_sum_bound {D q : ℕ} [NeZero q]
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ q)
    (hD : 1 < D) (hL : 2000 ≤ lemma23PaperL D) (hq : (q : ℝ) < lemma56PaperT D)
    (hθ : θ ≠ 1) (htwist : lemma44CharacterTwist χ θ ≠ 1)
    {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ)) (β : ℂ) :
    (∑ a ∈ lemma56FourZeroFinset χ θ t β, (lemma56FamilyOrder χ θ a.1 a.2 : ℝ)) ≤
      79 * lemma23PaperL D ^ (11 / 10 : ℝ) := by
  classical
  letI : NeZero (D * q) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne q)⟩
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD.le
  have hqp : (q : ℝ) ≤ (D : ℝ) * lemma56PaperT D := by
    nlinarith [hq.le, lemma56_paper_T_pos D]
  have hDqp : ((D * q : ℕ) : ℝ) ≤ (D : ℝ) * lemma56PaperT D := by
    rw [Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left hq.le (Nat.cast_nonneg _)
  have hχ0 := lemma55_removed_zero_order_sum_bound χ hD hL (by simp : |(0 : ℝ)| ≤ 2 * D) β
  have hζ0 := lemma55_actual_zeta_local_multiplicity_bound hD hL (by simp : |(0 : ℝ)| ≤ 2 * D)
  have hθt := lemma56_actual_local_order_sum_paper_budget θ hθ hD hL hqp ht
  have htw := lemma56_actual_local_order_sum_paper_budget (lemma44CharacterTwist χ θ) htwist hD hL hDqp ht
  have hL1 : 1 ≤ lemma23PaperL D := by linarith
  have hpower : lemma23PaperL D ≤ lemma23PaperL D ^ (11 / 10 : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hL1 (show (1 : ℝ) ≤ 11 / 10 by norm_num)
  unfold lemma56FourZeroFinset
  rw [sum_sigma, Fin.sum_univ_four]
  simp [lemma56ZeroFamily, lemma56FamilyOrder, lemma56FamilyFunction]
  unfold lemma55ZetaLocalMultiplicity at hζ0
  push_cast at hζ0
  change _ ≤ 13 * lemma23PaperL D at hχ0
  change _ ≤ 18 * lemma23PaperL D at hζ0
  linarith only [hχ0, hζ0, hθt, htw, hpower]

noncomputable def lemma56TaggedZeroPowerSum {D q : ℕ} [NeZero q]
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ q)
    (t : ℝ) (β : ℂ) (k : ℕ) : ℂ :=
  ∑ a ∈ lemma56FourZeroFinset χ θ t β, (lemma56FamilyOrder χ θ a.1 a.2 : ℂ) /
    (lemma55JensenCenter (lemma55FamilyHeight t a.1) - a.2) ^ k

lemma lemma56_actual_tagged_power_sum_eq {D q : ℕ} [NeZero q]
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ q)
    (t : ℝ) (β : ℂ) (k : ℕ) :
    letI : NeZero (D * q) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne q)⟩
    lemma56TaggedZeroPowerSum χ θ t β k =
      (lemma55SubsetZeroPowerSum χ 0 (lemma55ExceptionalRemovedLocalZeros χ 0 β) k +
        lemma55ZetaLocalZeroPowerSum 0 k) +
      (lemma56LocalZeroPowerSum θ t k + lemma56LocalZeroPowerSum (lemma44CharacterTwist χ θ) t k) := by
  classical
  letI : NeZero (D * q) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne q)⟩
  unfold lemma56TaggedZeroPowerSum lemma56FourZeroFinset
  rw [sum_sigma, Fin.sum_univ_four]
  simp [lemma56ZeroFamily, lemma56FamilyOrder, lemma56FamilyFunction, lemma55FamilyHeight,
    lemma55SubsetZeroPowerSum, lemma55ZetaLocalZeroPowerSum, lemma56LocalZeroPowerSum, add_assoc]

end ZhangLS.Spec
