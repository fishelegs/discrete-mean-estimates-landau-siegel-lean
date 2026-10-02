import ZhangLS.Spec.Lemma56ZeroRemovedBounds
import ZhangLS.Spec.Lemma23BorelCaratheodory

/-! # Normalized analytic logarithms and all-order Cauchy estimates

Actual Dirichlet L-functions and their actual analytic orders are retained.
These auxiliary results do not assert the complete Lemma 5.6 prime-window estimate.
-/

namespace ZhangLS.Spec
open Complex Metric Set Filter MeromorphicOn Finset
open scoped Topology Real
set_option maxHeartbeats 1000000

def Lemma56ZeroRemovedLogData {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r)
    (t : ℝ) (ℓ : ℂ → ℂ) : Prop :=
  ContinuousOn ℓ (ball (0 : ℂ) (5 / 4 : ℝ)) ∧ ℓ 0 = 0 ∧
    ∀ z ∈ ball (0 : ℂ) (5 / 4 : ℝ), exp (ℓ z) =
      lemma56ZeroRemovedL θ t (lemma55JensenCenter t + z) /
        lemma56ZeroRemovedL θ t (lemma55JensenCenter t)

theorem lemma56_actual_zero_removed_log_exists
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) (t : ℝ) :
    ∃ ℓ : ℂ → ℂ, Lemma56ZeroRemovedLogData θ t ℓ := by
  let U : Set ℂ := ball 0 (5 / 4 : ℝ)
  let q : ℂ → ℂ := fun z => lemma56ZeroRemovedL θ t (lemma55JensenCenter t + z) /
    lemma56ZeroRemovedL θ t (lemma55JensenCenter t)
  have h0 : (0 : ℂ) ∈ U := by simp [U]
  have hc : lemma56ZeroRemovedL θ t (lemma55JensenCenter t) ≠ 0 :=
    lemma56_actual_zero_removed_ne_zero θ hθ (mem_closedBall_self (by norm_num))
  have hshift {z : ℂ} (hz : z ∈ U) :
      lemma55JensenCenter t + z ∈ closedBall (lemma55JensenCenter t) (5 / 4 : ℝ) := by
    simpa [mem_ball_iff_norm, mem_closedBall_iff_norm] using (mem_ball_zero_iff.mp hz).le
  have hqne : ∀ z ∈ U, q z ≠ 0 := fun z hz =>
    div_ne_zero (lemma56_actual_zero_removed_ne_zero θ hθ (hshift hz)) hc
  have hqdif : ∀ z ∈ U, DifferentiableAt ℂ q z := by
    intro z _
    exact ((lemma56_actual_zero_removed_analytic θ hθ t _ (mem_univ _)).differentiableAt.comp z
      (by fun_prop)).div_const _
  have hUc : IsSimplyConnected U := by
    letI : ContractibleSpace U := (convex_ball (0 : ℂ) (5 / 4 : ℝ)).contractibleSpace ⟨0, h0⟩
    change SimplyConnectedSpace U
    infer_instance
  obtain ⟨ℓ₀, hcont, hlift, _hderiv⟩ := lemma23_exists_analytic_log_branch hUc isOpen_ball
    (fun z hz => (hqdif z hz).continuousAt.continuousWithinAt) hqne hqdif
  refine ⟨fun z => ℓ₀ z - ℓ₀ 0, hcont.sub continuousOn_const, by simp, ?_⟩
  intro z hz
  rw [exp_sub, hlift z hz, hlift 0 h0]
  simp [q, hc]

theorem lemma56_actual_zero_removed_log_hasDerivAt
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1)
    {t : ℝ} {ℓ : ℂ → ℂ} (hℓ : Lemma56ZeroRemovedLogData θ t ℓ)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) (5 / 4 : ℝ)) :
    HasDerivAt ℓ (logDeriv (lemma56ZeroRemovedL θ t) (lemma55JensenCenter t + z)) z := by
  let q : ℂ → ℂ := fun w => lemma56ZeroRemovedL θ t (lemma55JensenCenter t + w) /
    lemma56ZeroRemovedL θ t (lemma55JensenCenter t)
  have hc : lemma56ZeroRemovedL θ t (lemma55JensenCenter t) ≠ 0 :=
    lemma56_actual_zero_removed_ne_zero θ hθ (mem_closedBall_self (by norm_num))
  have hs : lemma55JensenCenter t + z ∈ closedBall (lemma55JensenCenter t) (5 / 4 : ℝ) := by
    simpa [mem_closedBall_iff_norm] using (mem_ball_zero_iff.mp hz).le
  have hqne : q z ≠ 0 := div_ne_zero (lemma56_actual_zero_removed_ne_zero θ hθ hs) hc
  have hd : HasDerivAt q (deriv (lemma56ZeroRemovedL θ t) (lemma55JensenCenter t + z) /
      lemma56ZeroRemovedL θ t (lemma55JensenCenter t)) z := by
    have h₀ := (lemma56_actual_zero_removed_analytic θ hθ t
      (lemma55JensenCenter t + z) (mem_univ _)).differentiableAt.hasDerivAt
    have h := h₀.comp z ((hasDerivAt_id z).const_add (lemma55JensenCenter t))
    simpa [q] using h.div_const (lemma56ZeroRemovedL θ t (lemma55JensenCenter t))
  have hdℓ := lemma23_hasDerivAt_of_continuous_exp_lift isOpen_ball hz hℓ.1 hℓ.2.2 hd hqne
  simpa [q, logDeriv_apply, div_div_div_cancel_right₀ hc] using hdℓ

theorem lemma56_actual_zero_removed_log_closed_bound
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1)
    {t : ℝ}
    {ℓ : ℂ → ℂ} (hℓ : Lemma56ZeroRemovedLogData θ t ℓ) {z : ℂ}
    (hz : z ∈ closedBall (0 : ℂ) (9 / 8 : ℝ)) :
    ‖ℓ z‖ ≤ 450 * lemma56JensenLogSize θ t := by
  have hLp : 0 < lemma56JensenLogSize θ t := lemma56_jensen_log_size_pos θ t
  have hdiff : DifferentiableOn ℂ ℓ (ball (0 : ℂ) (5 / 4 : ℝ)) := fun w hw =>
    (lemma56_actual_zero_removed_log_hasDerivAt θ hθ hℓ hw).differentiableAt.differentiableWithinAt
  have hRe : MapsTo ℓ (ball (0 : ℂ) (5 / 4 : ℝ)) {w : ℂ | w.re ≤ 25 * lemma56JensenLogSize θ t} := by
    intro w hw
    change (ℓ w).re ≤ 25 * lemma56JensenLogSize θ t
    have hs : lemma55JensenCenter t + w ∈ closedBall (lemma55JensenCenter t) (3 / 2 : ℝ) := by
      simp only [mem_closedBall_iff_norm, add_sub_cancel_left]
      linarith only [mem_ball_zero_iff.mp hw]
    have hn := lemma56_actual_zero_removed_ratio_bound θ hθ hs
    rw [← hℓ.2.2 w hw, norm_exp] at hn
    have hlog : (ℓ w).re ≤ Real.log (lemma56ZeroRemovedRatioBound θ t) :=
      (Real.le_log_iff_exp_le (lt_trans (by norm_num) (lemma56_zero_removed_ratio_bound_gt_one θ t))).mpr hn
    exact hlog.trans (lemma56_actual_zero_removed_log_ratio_bound θ hθ t)
  have hnorm : ‖z‖ ≤ (9 : ℝ) / 8 := by simpa using mem_closedBall_iff_norm.mp hz
  have hzin : z ∈ ball (0 : ℂ) (5 / 4 : ℝ) := mem_ball_zero_iff.mpr (by linarith only [hnorm])
  have hb := Complex.borelCaratheodory_zero (by positivity : 0 < 25 * lemma56JensenLogSize θ t)
    hdiff hRe (by norm_num : (0 : ℝ) < 5 / 4) hzin hℓ.2.1
  apply hb.trans
  apply (div_le_iff₀ (by linarith only [hnorm] : (0 : ℝ) < 5 / 4 - ‖z‖)).mpr
  nlinarith only [hnorm, hLp]

theorem lemma56_actual_zero_removed_log_cauchy_bound
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1)
    {t : ℝ}
    {ℓ : ℂ → ℂ} (hℓ : Lemma56ZeroRemovedLogData θ t ℓ) (n : ℕ) :
    ‖iteratedDeriv n ℓ 0‖ ≤
      n.factorial * (450 * lemma56JensenLogSize θ t) / (9 / 8 : ℝ) ^ n := by
  have hdiff : DifferentiableOn ℂ ℓ (ball (0 : ℂ) (5 / 4 : ℝ)) := fun w hw =>
    (lemma56_actual_zero_removed_log_hasDerivAt θ hθ hℓ hw).differentiableAt.differentiableWithinAt
  have hclosure : closure (ball (0 : ℂ) (9 / 8 : ℝ)) ⊆ ball (0 : ℂ) (5 / 4 : ℝ) :=
    (closure_ball_subset_closedBall).trans (closedBall_subset_ball (by norm_num))
  exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n (by norm_num)
    (hdiff.mono hclosure).diffContOnCl (fun w hw =>
      lemma56_actual_zero_removed_log_closed_bound θ hθ hℓ (sphere_subset_closedBall hw))

end ZhangLS.Spec
