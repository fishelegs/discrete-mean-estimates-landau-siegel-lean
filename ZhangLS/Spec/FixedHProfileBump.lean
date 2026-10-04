import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.MeanValue

/-! The literal original fixed-H bump and its third derivative. -/
set_option autoImplicit false
namespace ZhangLS.Spec.FixedHProfile
open Set Function
open scoped Classical ContDiff
set_option maxHeartbeats 2000000

noncomputable def beta (v : ℝ) : ℝ :=
  if 0 < v ∧ v < 1 then Real.exp (-1 / (v * (1 - v))) else 0

lemma beta_eq_glue (v : ℝ) : beta v = expNegInvGlue (v * (1 - v)) := by
  by_cases hv : 0 < v ∧ v < 1
  · have hp : 0 < v * (1 - v) := mul_pos hv.1 (by linarith [hv.2])
    simp [beta, expNegInvGlue, hv, hp.not_ge, neg_div]
  · have hp : v * (1 - v) ≤ 0 := by
      by_cases h0 : v ≤ 0
      · exact mul_nonpos_of_nonpos_of_nonneg h0 (by linarith)
      · have h1 : 1 ≤ v := by by_contra h; exact hv ⟨by linarith, by linarith⟩
        exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    simp [beta, expNegInvGlue, hv, hp]

lemma beta_contDiff : ContDiff ℝ ∞ beta := by
  have he : beta = fun v => expNegInvGlue (v * (1 - v)) := funext beta_eq_glue
  rw [he]
  exact expNegInvGlue.contDiff.comp (contDiff_id.mul (contDiff_const.sub contDiff_id))

lemma beta_support : Function.support beta = Set.Ioo (0 : ℝ) 1 := by
  ext v
  simp only [Function.mem_support, Set.mem_Ioo]
  by_cases h : 0 < v ∧ v < 1
  · simp [beta, h, (Real.exp_pos _).ne']
  · simp [beta, h]

lemma beta_tsupport : tsupport beta = Set.Icc (0 : ℝ) 1 := by
  rw [tsupport, beta_support, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]

lemma beta_hasCompactSupport : HasCompactSupport beta := by
  rw [HasCompactSupport, beta_tsupport]
  exact isCompact_Icc

lemma beta_midpoint : beta (1 / 2) = Real.exp (-4) := by norm_num [beta]
lemma beta_midpoint_pos : 0 < beta (1 / 2) := by rw [beta_midpoint]; positivity

lemma beta_derivative_contDiff (n : ℕ) : ContDiff ℝ ∞ (iteratedDeriv n beta) := by
  rw [iteratedDeriv_eq_iterate]
  exact beta_contDiff.iterate_deriv n

lemma beta_derivative_tsupport (n : ℕ) : tsupport (iteratedDeriv n beta) ⊆ Set.Icc (0 : ℝ) 1 := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero, beta_tsupport] using (Set.Subset.rfl : Set.Icc (0 : ℝ) 1 ⊆ Set.Icc (0 : ℝ) 1)
  | succ n ih =>
      rw [iteratedDeriv_succ]
      exact tsupport_deriv_subset.trans ih

lemma beta_derivative_hasCompactSupport (n : ℕ) : HasCompactSupport (iteratedDeriv n beta) := by
  exact isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (beta_derivative_tsupport n)

lemma beta_derivative_at_minus_one (n : ℕ) : iteratedDeriv n beta (-1) = 0 := by
  apply Function.notMem_support.mp
  intro h
  have hm := beta_derivative_tsupport n (subset_tsupport _ h)
  norm_num at hm

/-- No nonzero compactly supported smooth function can have an identically
zero derivative of positive order. Here the literal beta is nonzero at 1/2. -/
lemma beta_third_derivative_not_zero : ∃ v : ℝ, iteratedDeriv 3 beta v ≠ 0 := by
  by_contra h
  have h3 : ∀ v : ℝ, iteratedDeriv 3 beta v = 0 := by simpa using h
  have descend (n : ℕ) (hn : ∀ v, iteratedDeriv (n + 1) beta v = 0) :
      ∀ v, iteratedDeriv n beta v = 0 := by
    intro v
    have hd : ∀ v, deriv (iteratedDeriv n beta) v = 0 := by simpa only [iteratedDeriv_succ] using hn
    have hc := is_const_of_deriv_eq_zero ((beta_derivative_contDiff n).differentiable (by simp)) hd v (-1)
    rw [beta_derivative_at_minus_one] at hc
    exact hc
  have h2 := descend 2 h3
  have h1 := descend 1 h2
  have h0 := descend 0 h1
  have hz : beta (1 / 2) = 0 := by simpa only [iteratedDeriv_zero] using h0 (1 / 2)
  exact (ne_of_gt beta_midpoint_pos) hz

end ZhangLS.Spec.FixedHProfile
