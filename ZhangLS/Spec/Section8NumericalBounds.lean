import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
namespace Section8

def delta : ℝ := 3*Real.pi/500

theorem pi_bounds : (31415:ℝ)/10000 ≤ Real.pi ∧ Real.pi ≤ 31416/10000 := by
  constructor <;> linarith [Real.pi_gt_d20, Real.pi_lt_d20]

theorem sqrt_two_bounds : (14142:ℝ)/10000 ≤ Real.sqrt 2 ∧ Real.sqrt 2 ≤ 14143/10000 := by
  have hn := Real.sqrt_nonneg (2:ℝ)
  have he := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  constructor <;> nlinarith

theorem delta_bounds : (18849:ℝ)/1000000 ≤ delta ∧ delta ≤ 19/1000 := by
  unfold delta
  constructor <;> linarith [pi_bounds.1, pi_bounds.2]

theorem sin_delta_bounds : (1884:ℝ)/100000 ≤ Real.sin delta ∧ Real.sin delta ≤ 1885/100000 := by
  have hpos : 0 < delta := lt_of_lt_of_le (by norm_num) delta_bounds.1
  have hone : delta ≤ 1 := le_trans delta_bounds.2 (by norm_num)
  have hcube : delta^3 ≤ (19/1000:ℝ)^3 := by gcongr; exact delta_bounds.2
  constructor
  · have h := Real.sin_gt_sub_cube hpos hone
    linarith [delta_bounds.1]
  · have h := Real.sin_le hpos.le
    unfold delta at h ⊢
    linarith [pi_bounds.2]

theorem cos_delta_bounds : (9998:ℝ)/10000 ≤ Real.cos delta ∧ Real.cos delta ≤ 1 := by
  have hs : delta^2 ≤ (19/1000:ℝ)^2 := by
    gcongr
    · linarith [delta_bounds.1]
    · exact delta_bounds.2
  exact ⟨by linarith [Real.one_sub_sq_div_two_le_cos (x := delta)], Real.cos_le_one _⟩

#print axioms pi_bounds
#print axioms sqrt_two_bounds
#print axioms sin_delta_bounds
#print axioms cos_delta_bounds
end Section8
