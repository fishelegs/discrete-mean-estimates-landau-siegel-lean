import ZhangLS.Spec.Lemma46LogDerivative

/-! # Exponential transport on a genuine zero-free disk -/

namespace ZhangLS.Spec

open Complex Metric Set
open scoped Topology

set_option maxHeartbeats 1000000

/-- Integrating a near-constant logarithmic derivative on a disk. The
logarithm is constructed from nonvanishing, and its error is controlled
by the complex mean-value inequality. -/
theorem lemma46_exponential_transport_on_ball
    {f : ℂ → ℂ} {c x y : ℂ} {R C : ℝ} {a : ℂ}
    (hR : 0 < R)
    (hf : ∀ z ∈ ball c R, DifferentiableAt ℂ f z)
    (hne : ∀ z ∈ ball c R, f z ≠ 0)
    (hb : ∀ z ∈ ball c R, ‖logDeriv f z + a‖ ≤ C)
    (hx : x ∈ ball c R) (hy : y ∈ ball c R) :
    ∃ e : ℂ, ‖e‖ ≤ C * ‖y - x‖ ∧
      f y / f x = Complex.exp (-a * (y - x) + e) := by
  have hc : c ∈ ball c R := mem_ball_self hR
  have hsc : IsSimplyConnected (ball c R) := by
    letI : ContractibleSpace (ball c R) :=
      (convex_ball c R).contractibleSpace ⟨c, hc⟩
    change SimplyConnectedSpace (ball c R)
    exact inferInstance
  obtain ⟨ℓ, hcont, hlift, hd⟩ := lemma23_exists_analytic_log_branch
    hsc isOpen_ball (fun z hz => (hf z hz).continuousAt.continuousWithinAt) hne hf
  let E : ℂ → ℂ := fun z => ℓ z + a * z
  have hE (z : ℂ) (hz : z ∈ ball c R) :
      HasDerivAt E (logDeriv f z + a) z := by
    simpa only [E, logDeriv_apply, mul_one] using
      (hd z hz).add ((hasDerivAt_id z).const_mul a)
  have hbound : ‖E y - E x‖ ≤ C * ‖y - x‖ :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z hz => (hE z hz).hasDerivWithinAt) hb (convex_ball c R) hx hy
  refine ⟨E y - E x, hbound, ?_⟩
  have he : -a * (y - x) + (E y - E x) = ℓ y - ℓ x := by
    dsimp [E]; ring
  rw [he, Complex.exp_sub, hlift y hy, hlift x hx]

end ZhangLS.Spec
