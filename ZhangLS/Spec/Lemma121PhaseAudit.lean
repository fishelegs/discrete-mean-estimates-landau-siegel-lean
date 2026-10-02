import ZhangLS.Spec.Lemma82LocalMainTerm
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/-! # Lemma 12.1: a source-level phase-budget audit
These theorems concern the pure phase calculation printed in the proof.
They are not counterexamples involving a character satisfying (A).
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex

/-- Exact phase expression before the paper's final linearization. -/
noncomputable def lemma121Phase (b a : ℂ) (h : ℝ) : ℂ :=
  Complex.exp (-b * (h:ℂ)) * (-1+(b-a)*(h:ℂ))

/-- The printed linear approximation in Lemma 12.1. -/
noncomputable def lemma121LinearPhase (b a : ℂ) (h : ℝ) : ℂ :=
  -1+(2*b-a)*(h:ℂ)

lemma lemma121_phase_linearization_bound (b a : ℂ) (h : ℝ)
    (hb : ‖b*(h:ℂ)‖≤1) :
    ‖lemma121Phase b a h-lemma121LinearPhase b a h‖ ≤
      ‖b*(h:ℂ)‖^2*(1+‖(b-a)*(h:ℂ)‖)+
        ‖b*(h:ℂ)‖*‖(b-a)*(h:ℂ)‖ := by
  let z := b*(h:ℂ)
  let w := (b-a)*(h:ℂ)
  have he : lemma121Phase b a h-lemma121LinearPhase b a h =
      (Complex.exp (-z)-1+z)*(-1+w)-z*w := by
    dsimp [lemma121Phase,lemma121LinearPhase,z,w]
    rw [neg_mul]
    ring
  rw [he]
  have hr : ‖Complex.exp (-z)-1+z‖≤‖z‖^2 := by
    simpa using Complex.norm_exp_sub_one_sub_id_le (x := -z) (by simpa [z] using hb)
  calc
    _ ≤ ‖Complex.exp (-z)-1+z‖*‖-1+w‖+‖z‖*‖w‖ := by
      simpa only [norm_mul] using norm_sub_le ((Complex.exp (-z)-1+z)*(-1+w)) (z*w)
    _ ≤ ‖z‖^2*(1+‖w‖)+‖z‖*‖w‖ := by
      gcongr
      calc
        ‖-1+w‖ ≤ ‖(-1:ℂ)‖+‖w‖ := norm_add_le _ _
        _ = _ := by simp

/-- A rationally bounded trigonometric remainder, well inside the original
0<h/log P<0.004 interval. -/
lemma lemma121_phase_remainder_lower {u : ℝ}
    (hlo : 9/1000≤u) (hhi : u≤12/1000) :
    (1:ℝ)/100000 < Real.cos u + u*Real.sin u - 1 := by
  have hup : 0<u := by linarith
  have hs := Real.sin_gt_sub_cube hup (by linarith : u≤1)
  have hc := Real.one_sub_sq_div_two_le_cos (x := u)
  have hsm := mul_lt_mul_of_pos_left hs hup
  have hsqlo : (9/1000:ℝ)^2≤u^2 := pow_le_pow_left₀ (by norm_num) hlo 2
  have hsqhi : u^2≤(12/1000:ℝ)^2 := pow_le_pow_left₀ hup.le hhi 2
  have hfour : u^4≤(12/1000:ℝ)^4 := pow_le_pow_left₀ hup.le hhi 4
  nlinarith

/-- The limiting j=3 phase at h/log P=1/500 violates the printed 10^-5
linearization budget. This does not assert the existence of a character
satisfying (A). -/
theorem lemma121_limiting_phase_exceeds_printed_budget :
    (1:ℝ)/100000 <
      ‖lemma121Phase (3*I*(Real.pi:ℂ)/2) (3*I*(Real.pi:ℂ)) (1/500) -
        lemma121LinearPhase (3*I*(Real.pi:ℂ)/2) (3*I*(Real.pi:ℂ)) (1/500)‖ := by
  let u : ℝ := 3*Real.pi/1000
  have hu0 : 9/1000≤u := by dsimp [u]; linarith [Real.pi_gt_three]
  have hu1 : u≤12/1000 := by dsimp [u]; linarith [Real.pi_le_four]
  have hh := lemma121_phase_remainder_lower hu0 hu1
  have he : lemma121Phase (3*I*(Real.pi:ℂ)/2) (3*I*(Real.pi:ℂ)) (1/500) -
      lemma121LinearPhase (3*I*(Real.pi:ℂ)/2) (3*I*(Real.pi:ℂ)) (1/500) =
      1-Complex.exp ((-u:ℝ)*I)*(1+(u:ℂ)*I) := by
    unfold lemma121Phase lemma121LinearPhase
    have hz : -(3*I*(Real.pi:ℂ)/2)*((1/500:ℝ):ℂ)=((-u:ℝ):ℂ)*I := by
      dsimp [u]; push_cast; ring
    rw [hz]
    dsimp [u]
    push_cast
    ring
  rw [he]
  have hre : (1-Complex.exp ((-u:ℝ)*I)*(1+(u:ℂ)*I)).re =
      1-Real.cos u-u*Real.sin u := by
    rw [Complex.exp_ofReal_mul_I]
    simp [Complex.mul_re,Real.cos_neg,Real.sin_neg,Complex.cos_ofReal_re,Complex.sin_ofReal_re]
    ring
  have hn := Complex.abs_re_le_norm (1-Complex.exp ((-u:ℝ)*I)*(1+(u:ℂ)*I))
  rw [hre] at hn
  have hab : |1-Real.cos u-u*Real.sin u| = Real.cos u+u*Real.sin u-1 := by
    rw [abs_of_neg (by linarith)]
    ring
  rw [hab] at hn
  exact hh.trans_le hn

end ZhangLS.Spec
