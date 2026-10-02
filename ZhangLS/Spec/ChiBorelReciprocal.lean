import ZhangLS.Spec.Lemma23BorelCaratheodory

namespace ZhangLS.Spec
open Complex Metric Set
open scoped Topology
set_option maxHeartbeats 800000

/-- Borel--Carathéodory turns an upper ratio bound on a zero-free disk into
an inverse bound on its concentric four-fifths disk. -/
theorem chi_inverse_bound_on_disk {f : ℂ → ℂ} {c s : ℂ} {R H : ℝ}
    (hR : 0 < R) (hH : 1 < H)
    (hfdif : ∀ z ∈ ball c R, DifferentiableAt ℂ f z)
    (hfne : ∀ z ∈ ball c R, f z ≠ 0)
    (hNorm : ∀ z ∈ ball c R, ‖f z / f c‖ ≤ H)
    (hs : ‖s-c‖ ≤ 4*R/5) :
    ‖(f s)⁻¹‖ ≤ ‖(f c)⁻¹‖ * H^8 := by
  let U : Set ℂ := ball 0 R
  let q : ℂ → ℂ := fun z => f (c+z) / f c
  have h0 : (0:ℂ) ∈ U := mem_ball_self hR
  have hshift {z : ℂ} (hz : z ∈ U) : c+z ∈ ball c R := by
    have hn : ‖z‖ < R := mem_ball_zero_iff.mp hz
    simpa only [mem_ball_iff_norm, add_sub_cancel_left, sub_zero] using hn
  have hc : f c ≠ 0 := hfne c (mem_ball_self hR)
  have hq0 : q 0 = 1 := by simp [q,hc]
  have hqne : ∀ z ∈ U, q z ≠ 0 := fun z hz => div_ne_zero (hfne _ (hshift hz)) hc
  have hqdif : ∀ z ∈ U, DifferentiableAt ℂ q z := by
    intro z hz
    exact ((hfdif (c+z) (hshift hz)).comp z (by fun_prop)).div_const _
  have hUsc : IsSimplyConnected U := by
    letI : ContractibleSpace U := (convex_ball (0:ℂ) R).contractibleSpace ⟨0,h0⟩
    change SimplyConnectedSpace U
    infer_instance
  obtain ⟨ℓ₀,hcont,hlift,_⟩ := lemma23_exists_analytic_log_branch hUsc isOpen_ball
    (fun z hz => (hqdif z hz).continuousAt.continuousWithinAt) hqne hqdif
  let ℓ : ℂ → ℂ := fun z => ℓ₀ z - ℓ₀ 0
  have hℓcont : ContinuousOn ℓ U := hcont.sub continuousOn_const
  have hℓ0 : ℓ 0 = 0 := by simp [ℓ]
  have hℓlift (z : ℂ) (hz : z ∈ U) : exp (ℓ z) = q z := by
    rw [show ℓ z = ℓ₀ z-ℓ₀ 0 from rfl, exp_sub,hlift z hz,hlift 0 h0,hq0,div_one]
  have hdiff : DifferentiableOn ℂ ℓ U := by
    intro z hz
    exact (lemma23_hasDerivAt_of_continuous_exp_lift isOpen_ball hz hℓcont hℓlift
      (hqdif z hz).hasDerivAt (hqne z hz)).differentiableAt.differentiableWithinAt
  have hM : 0 < Real.log H := Real.log_pos hH
  have hRe : MapsTo ℓ U {z : ℂ | z.re ≤ Real.log H} := by
    intro z hz
    have hn := hNorm (c+z) (hshift hz)
    change ‖q z‖ ≤ H at hn
    rw [←hℓlift z hz,norm_exp] at hn
    exact (Real.le_log_iff_exp_le (by linarith : 0 < H)).mpr hn
  have hsU : s-c ∈ U := mem_ball_zero_iff.mpr (by linarith)
  have hb := Complex.borelCaratheodory_zero hM hdiff hRe hR hsU hℓ0
  have hb' : ‖ℓ (s-c)‖ ≤ 8 * Real.log H := by
    apply hb.trans
    apply (div_le_iff₀ (by linarith : 0 < R - ‖s-c‖)).mpr
    nlinarith
  have hqbound : ‖(q (s-c))⁻¹‖ ≤ H^8 := by
    rw [←hℓlift (s-c) hsU,norm_inv,norm_exp,←Real.exp_neg]
    calc
      _ ≤ Real.exp (8*Real.log H) := Real.exp_le_exp.mpr
        ((neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans hb'))
      _ = H^8 := by
        rw [show 8*Real.log H = Real.log (H^8) by rw [Real.log_pow]; norm_num]
        exact Real.exp_log (pow_pos (by linarith) _)
  have he : (f s)⁻¹ = (f c)⁻¹ * (q (s-c))⁻¹ := by
    dsimp [q]
    rw [add_sub_cancel,inv_div]
    field_simp
  rw [he,norm_mul]
  exact mul_le_mul_of_nonneg_left hqbound (norm_nonneg _)

end ZhangLS.Spec
