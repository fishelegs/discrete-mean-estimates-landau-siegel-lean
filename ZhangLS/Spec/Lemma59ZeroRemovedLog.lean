import ZhangLS.Spec.Lemma59ZeroRemovedBounds
import ZhangLS.Spec.Lemma23BorelCaratheodory

/-! # Actual zero factors and zero-removed L-function bounds for Lemma 5.9

The exact actual L-function, divisor and analytic multiplicities are retained.
The full original Lemma 5.9 quotient is proved in `Lemma59.lean`.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Metric Set Filter MeromorphicOn Finset
open scoped Topology Real
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

def Lemma59ZeroRemovedLogData {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r)
    (t : ℝ) (ℓ : ℂ → ℂ) : Prop :=
  ContinuousOn ℓ (ball (0 : ℂ) (7 / 4 : ℝ)) ∧ ℓ 0 = 0 ∧
    ∀ z ∈ ball (0 : ℂ) (7 / 4 : ℝ), exp (ℓ z) =
      lemma59ZeroRemovedL θ t (lemma55JensenCenter t + z) /
        lemma59ZeroRemovedL θ t (lemma55JensenCenter t)

theorem lemma59_actual_zero_removed_log_exists
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) (t : ℝ) :
    ∃ ℓ : ℂ → ℂ, Lemma59ZeroRemovedLogData θ t ℓ := by
  let U : Set ℂ := ball 0 (7 / 4 : ℝ)
  let q : ℂ → ℂ := fun z => lemma59ZeroRemovedL θ t (lemma55JensenCenter t + z) /
    lemma59ZeroRemovedL θ t (lemma55JensenCenter t)
  have h0 : (0 : ℂ) ∈ U := by simp [U]
  have hc : lemma59ZeroRemovedL θ t (lemma55JensenCenter t) ≠ 0 :=
    lemma59_actual_zero_removed_ne_zero θ hθ (mem_closedBall_self (by norm_num))
  have hshift {z : ℂ} (hz : z ∈ U) :
      lemma55JensenCenter t + z ∈ closedBall (lemma55JensenCenter t) (7 / 4 : ℝ) := by
    simpa [mem_ball_iff_norm, mem_closedBall_iff_norm] using (mem_ball_zero_iff.mp hz).le
  have hqne : ∀ z ∈ U, q z ≠ 0 := fun z hz =>
    div_ne_zero (lemma59_actual_zero_removed_ne_zero θ hθ (hshift hz)) hc
  have hqdif : ∀ z ∈ U, DifferentiableAt ℂ q z := by
    intro z _
    exact ((lemma59_actual_zero_removed_analytic θ hθ t _ (mem_univ _)).differentiableAt.comp z
      (by fun_prop)).div_const _
  have hUc : IsSimplyConnected U := by
    letI : ContractibleSpace U := (convex_ball (0 : ℂ) (7 / 4 : ℝ)).contractibleSpace ⟨0, h0⟩
    change SimplyConnectedSpace U
    infer_instance
  obtain ⟨ℓ₀, hcont, hlift, _hderiv⟩ := lemma23_exists_analytic_log_branch hUc isOpen_ball
    (fun z hz => (hqdif z hz).continuousAt.continuousWithinAt) hqne hqdif
  refine ⟨fun z => ℓ₀ z - ℓ₀ 0, hcont.sub continuousOn_const, by simp, ?_⟩
  intro z hz
  rw [exp_sub, hlift z hz, hlift 0 h0]
  simp [q, hc]

theorem lemma59_actual_zero_removed_log_hasDerivAt
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1)
    {t : ℝ} {ℓ : ℂ → ℂ} (hℓ : Lemma59ZeroRemovedLogData θ t ℓ)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) (7 / 4 : ℝ)) :
    HasDerivAt ℓ (logDeriv (lemma59ZeroRemovedL θ t) (lemma55JensenCenter t + z)) z := by
  let q : ℂ → ℂ := fun w => lemma59ZeroRemovedL θ t (lemma55JensenCenter t + w) /
    lemma59ZeroRemovedL θ t (lemma55JensenCenter t)
  have hc : lemma59ZeroRemovedL θ t (lemma55JensenCenter t) ≠ 0 :=
    lemma59_actual_zero_removed_ne_zero θ hθ (mem_closedBall_self (by norm_num))
  have hs : lemma55JensenCenter t + z ∈ closedBall (lemma55JensenCenter t) (7 / 4 : ℝ) := by
    simpa [mem_closedBall_iff_norm] using (mem_ball_zero_iff.mp hz).le
  have hqne : q z ≠ 0 := div_ne_zero (lemma59_actual_zero_removed_ne_zero θ hθ hs) hc
  have hd : HasDerivAt q (deriv (lemma59ZeroRemovedL θ t) (lemma55JensenCenter t + z) /
      lemma59ZeroRemovedL θ t (lemma55JensenCenter t)) z := by
    have h₀ := (lemma59_actual_zero_removed_analytic θ hθ t
      (lemma55JensenCenter t + z) (mem_univ _)).differentiableAt.hasDerivAt
    have h := h₀.comp z ((hasDerivAt_id z).const_add (lemma55JensenCenter t))
    simpa [q] using h.div_const (lemma59ZeroRemovedL θ t (lemma55JensenCenter t))
  have hdℓ := lemma23_hasDerivAt_of_continuous_exp_lift isOpen_ball hz hℓ.1 hℓ.2.2 hd hqne
  simpa [q, logDeriv_apply, div_div_div_cancel_right₀ hc] using hdℓ

theorem lemma59_actual_zero_removed_log_closed_bound
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1)
    {t : ℝ}
    {ℓ : ℂ → ℂ} (hℓ : Lemma59ZeroRemovedLogData θ t ℓ) {z : ℂ}
    (hz : z ∈ closedBall (0 : ℂ) (13 / 8 : ℝ)) :
    ‖ℓ z‖ ≤ 5200 * lemma59JensenLogSize θ t := by
  have hLp : 0 < lemma59JensenLogSize θ t := lemma59_jensen_log_size_pos θ t
  have hdiff : DifferentiableOn ℂ ℓ (ball (0 : ℂ) (7 / 4 : ℝ)) := fun w hw =>
    (lemma59_actual_zero_removed_log_hasDerivAt θ hθ hℓ hw).differentiableAt.differentiableWithinAt
  have hRe : MapsTo ℓ (ball (0 : ℂ) (7 / 4 : ℝ)) {w : ℂ | w.re ≤ 200 * lemma59JensenLogSize θ t} := by
    intro w hw
    change (ℓ w).re ≤ 200 * lemma59JensenLogSize θ t
    have hs : lemma55JensenCenter t + w ∈ closedBall (lemma55JensenCenter t) (15 / 8 : ℝ) := by
      simp only [mem_closedBall_iff_norm, add_sub_cancel_left]
      linarith only [mem_ball_zero_iff.mp hw]
    have hn := lemma59_actual_zero_removed_ratio_bound θ hθ hs
    rw [← hℓ.2.2 w hw, norm_exp] at hn
    have hlog : (ℓ w).re ≤ Real.log (lemma59ZeroRemovedRatioBound θ t) :=
      (Real.le_log_iff_exp_le (lt_trans (by norm_num) (lemma59_zero_removed_ratio_bound_gt_one θ t))).mpr hn
    exact hlog.trans (lemma59_actual_zero_removed_log_ratio_bound θ hθ t)
  have hnorm : ‖z‖ ≤ (13 : ℝ) / 8 := by simpa using mem_closedBall_iff_norm.mp hz
  have hzin : z ∈ ball (0 : ℂ) (7 / 4 : ℝ) := mem_ball_zero_iff.mpr (by linarith only [hnorm])
  have hb := Complex.borelCaratheodory_zero (by positivity : 0 < 200 * lemma59JensenLogSize θ t)
    hdiff hRe (by norm_num : (0 : ℝ) < 7 / 4) hzin hℓ.2.1
  apply hb.trans
  apply (div_le_iff₀ (by linarith only [hnorm] : (0 : ℝ) < 7 / 4 - ‖z‖)).mpr
  nlinarith only [hnorm, hLp]

theorem lemma59_actual_zero_removed_log_cauchy_bound
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1)
    {t : ℝ}
    {ℓ : ℂ → ℂ} (hℓ : Lemma59ZeroRemovedLogData θ t ℓ) (n : ℕ) :
    ‖iteratedDeriv n ℓ 0‖ ≤
      n.factorial * (5200 * lemma59JensenLogSize θ t) / (13 / 8 : ℝ) ^ n := by
  have hdiff : DifferentiableOn ℂ ℓ (ball (0 : ℂ) (7 / 4 : ℝ)) := fun w hw =>
    (lemma59_actual_zero_removed_log_hasDerivAt θ hθ hℓ hw).differentiableAt.differentiableWithinAt
  have hclosure : closure (ball (0 : ℂ) (13 / 8 : ℝ)) ⊆ ball (0 : ℂ) (7 / 4 : ℝ) :=
    (closure_ball_subset_closedBall).trans (closedBall_subset_ball (by norm_num))
  exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n (by norm_num)
    (hdiff.mono hclosure).diffContOnCl (fun w hw =>
      lemma59_actual_zero_removed_log_closed_bound θ hθ hℓ (sphere_subset_closedBall hw))

end ZhangLS.Spec
