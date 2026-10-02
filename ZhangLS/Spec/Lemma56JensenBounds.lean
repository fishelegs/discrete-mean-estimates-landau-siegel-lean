import ZhangLS.Spec.Lemma56NearTwoBound
import ZhangLS.Spec.Lemma56

/-! # Actual local zero counts for arbitrary nonprincipal complex characters

The entire actual L-function and the proved Abel bound supply Jensen's
inputs. The product-modulus character may be imprimitive and its modulus
may share factors with D. Both height endpoints |t|=2D are covered.
-/

namespace ZhangLS.Spec
open Complex Metric Set MeromorphicOn
open scoped Real
set_option maxHeartbeats 1000000

theorem lemma56_actual_jensen_disk_bound {r : ℕ} [NeZero r]
    (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) {t : ℝ} {z : ℂ}
    (hz : z ∈ closedBall (lemma55JensenCenter t) (3 / 2 : ℝ)) :
    ‖DirichletCharacter.LFunction θ z‖ ≤ 2 * (r : ℝ) * (7 / 2 + |t|) := by
  have hσ := lemma55_jensen_disk_re_lower_bound hz
  have hσp : 0 < z.re := by linarith
  have hd := mem_closedBall_iff_norm.mp hz
  have hzn : ‖z‖ ≤ 7 / 2 + |t| := by
    have hn := norm_add_le (z - lemma55JensenCenter t) (lemma55JensenCenter t)
    rw [sub_add_cancel] at hn
    linarith only [hn, hd, lemma55_jensen_center_norm_le t]
  have hquot : (r : ℝ) / z.re ≤ 2 * (r : ℝ) := by
    apply (div_le_iff₀ hσp).mpr
    nlinarith only [hσ, (Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
  calc
    _ ≤ ‖z‖ * ((r : ℝ) / z.re) := lemma56_actual_LFunction_bound_re_pos θ hθ hσp
    _ ≤ (7 / 2 + |t|) * (2 * (r : ℝ)) :=
      mul_le_mul hzn hquot (by positivity) (by positivity)
    _ = _ := by ring

theorem lemma56_actual_L_analyticOnNhd {r : ℕ} [NeZero r]
    (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) :
    AnalyticOnNhd ℂ (DirichletCharacter.LFunction θ) univ := by
  intro z _
  exact (DirichletCharacter.differentiable_LFunction hθ).analyticAt z

theorem lemma56_actual_jensen_center_lower_bound {r : ℕ} [NeZero r]
    (θ : DirichletCharacter ℂ r) (t : ℝ) :
    (1 : ℝ) / 4 ≤ ‖DirichletCharacter.LFunction θ (lemma55JensenCenter t)‖ :=
  lemma56_actual_L_norm_lower_bound θ (by simp)

theorem lemma56_actual_jensen_center_ne_zero {r : ℕ} [NeZero r]
    (θ : DirichletCharacter ℂ r) (t : ℝ) :
    DirichletCharacter.LFunction θ (lemma55JensenCenter t) ≠ 0 := by
  have h := lemma56_actual_jensen_center_lower_bound θ t
  intro hz
  rw [hz, norm_zero] at h
  norm_num at h

noncomputable def lemma56JensenMultiplicityCount {r : ℕ} [NeZero r]
    (θ : DirichletCharacter ℂ r) (t : ℝ) : ℤ :=
  ∑ᶠ ρ : ℂ, divisor (DirichletCharacter.LFunction θ)
    (closedBall (lemma55JensenCenter t) (5 / 4 : ℝ)) ρ

theorem lemma56_actual_jensen_multiplicity_bound {r : ℕ} [NeZero r]
    (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) (t : ℝ) :
    (lemma56JensenMultiplicityCount θ t : ℝ) ≤
      6 * Real.log (8 * (r : ℝ) * (7 / 2 + |t|)) := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne r)
  have hrp : (0 : ℝ) < r := by linarith
  have hM : 1 ≤ 2 * (r : ℝ) * (7 / 2 + |t|) := by
    nlinarith only [hr1, abs_nonneg t]
  have ha := (lemma56_actual_L_analyticOnNhd θ hθ).mono
    (subset_univ (closedBall (lemma55JensenCenter t) |(3 / 2 : ℝ)|))
  have hJ := ha.sum_divisor_le (r := (5 / 4 : ℝ)) (R := (3 / 2 : ℝ))
    (M := 2 * (r : ℝ) * (7 / 2 + |t|)) (by norm_num) (by norm_num) hM
    (lemma56_actual_jensen_center_ne_zero θ t)
    (fun z hz => lemma56_actual_jensen_disk_bound θ hθ (by
      have hz' := sphere_subset_closedBall hz
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] at hz'
      exact hz'))
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 5 / 4),
    show (3 / 2 : ℝ) / (5 / 4) = 6 / 5 by norm_num] at hJ
  have hcenter := lemma56_actual_jensen_center_lower_bound θ t
  have hcp : 0 < ‖DirichletCharacter.LFunction θ (lemma55JensenCenter t)‖ := by linarith
  have hratio : (2 * (r : ℝ) * (7 / 2 + |t|)) /
      ‖DirichletCharacter.LFunction θ (lemma55JensenCenter t)‖ ≤
      8 * (r : ℝ) * (7 / 2 + |t|) := by
    apply (div_le_iff₀ hcp).mpr
    have hh := mul_le_mul_of_nonneg_left hcenter
      (by positivity : 0 ≤ 8 * (r : ℝ) * (7 / 2 + |t|))
    nlinarith only [hh]
  have hlog := Real.log_le_log (by positivity :
      0 < (2 * (r : ℝ) * (7 / 2 + |t|)) /
        ‖DirichletCharacter.LFunction θ (lemma55JensenCenter t)‖) hratio
  have hden : (1 : ℝ) / 6 ≤ Real.log (6 / 5 : ℝ) := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 6 / 5)
    norm_num at h
    exact h
  have hdenp : 0 < Real.log (6 / 5 : ℝ) := by linarith
  have hlogn : 0 ≤ Real.log (8 * (r : ℝ) * (7 / 2 + |t|)) := by
    apply Real.log_nonneg
    nlinarith only [hr1, abs_nonneg t]
  apply hJ.trans
  apply (div_le_iff₀ hdenp).mpr
  have hscale := mul_le_mul_of_nonneg_left hden
    (show 0 ≤ 6 * Real.log (8 * (r : ℝ) * (7 / 2 + |t|)) by positivity)
  nlinarith only [hlog, hscale]

theorem lemma56_actual_jensen_paper_budget {D r : ℕ} [NeZero r]
    (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) (hD : 1 < D)
    (hL : 2000 ≤ lemma23PaperL D) (hr : (r : ℝ) ≤ (D : ℝ) * lemma56PaperT D)
    {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ)) :
    (lemma56JensenMultiplicityCount θ t : ℝ) ≤
      24 * lemma23PaperL D ^ (11 / 10 : ℝ) := by
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD.le
  have hDp : (0 : ℝ) < D := by linarith
  have hrp : (0 : ℝ) < r := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne r)
  have hT := lemma56_paper_T_pos D
  have hL1 : 1 ≤ lemma23PaperL D := by linarith
  have hLp : 0 < lemma23PaperL D := by linarith
  have hpower : lemma23PaperL D ≤ lemma23PaperL D ^ (11 / 10 : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hL1 (show (1 : ℝ) ≤ 11 / 10 by norm_num)
  have hX : 8 * (r : ℝ) * (7 / 2 + |t|) ≤ 44 * (D : ℝ) ^ 2 * lemma56PaperT D := by
    calc
      _ ≤ 8 * ((D : ℝ) * lemma56PaperT D) * (7 / 2 + 2 * (D : ℝ)) := by gcongr
      _ ≤ 8 * ((D : ℝ) * lemma56PaperT D) * ((11 / 2 : ℝ) * (D : ℝ)) := by
        gcongr
        linarith
      _ = _ := by ring
  have hlog : Real.log (8 * (r : ℝ) * (7 / 2 + |t|)) ≤
      4 * lemma23PaperL D ^ (11 / 10 : ℝ) := by
    calc
      _ ≤ Real.log (44 * (D : ℝ) ^ 2 * lemma56PaperT D) :=
        Real.log_le_log (by positivity) hX
      _ = Real.log 44 + 2 * lemma23PaperL D + lemma23PaperL D ^ (11 / 10 : ℝ) := by
        rw [Real.log_mul (by positivity) hT.ne', Real.log_mul (by norm_num)
          (pow_ne_zero 2 hDp.ne'), Real.log_pow]
        simp only [lemma56PaperT, Real.log_exp, lemma23PaperL]
        norm_num
      _ ≤ _ := by
        have hc := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 44)
        norm_num at hc
        linarith
  exact (lemma56_actual_jensen_multiplicity_bound θ hθ t).trans
    (by nlinarith only [hlog])

theorem lemma56_actual_primitive_pair_jensen_bounds {D r : ℕ} [NeZero r]
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ r)
    (hθ : θ.IsPrimitive) (hr1 : 1 < r)
    (hne : (fun n : ℕ => θ (n : ZMod r)) ≠ (fun n : ℕ => χ.chi (n : ZMod D)))
    (hD : 1 < D) (hL : 2000 ≤ lemma23PaperL D)
    (hrT : (r : ℝ) < lemma56PaperT D) {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ)) :
    (lemma56JensenMultiplicityCount θ t : ℝ) ≤ 24 * lemma23PaperL D ^ (11 / 10 : ℝ) ∧
    letI : NeZero (D * r) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne r)⟩
    (lemma56JensenMultiplicityCount (lemma44CharacterTwist χ θ) t : ℝ) ≤
      24 * lemma23PaperL D ^ (11 / 10 : ℝ) := by
  letI : NeZero (D * r) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne r)⟩
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD.le
  have hDp : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hr : (r : ℝ) ≤ (D : ℝ) * lemma56PaperT D := by
    have hT := lemma56_paper_T_pos D
    nlinarith [hrT.le]
  have hDr : ((D * r : ℕ) : ℝ) ≤ (D : ℝ) * lemma56PaperT D := by
    rw [Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left hrT.le hDp
  exact ⟨lemma56_actual_jensen_paper_budget θ
    (lemma56_primitive_positive_level_nonprincipal θ hθ hr1) hD hL hr ht,
    lemma56_actual_jensen_paper_budget (lemma44CharacterTwist χ θ)
      (lemma56_distinct_primitive_twist_nonprincipal χ θ hθ hne) hD hL hDr ht⟩

end ZhangLS.Spec
