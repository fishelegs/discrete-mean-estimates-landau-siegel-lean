import ZhangLS.Spec.Lemma51ShiftEstimates
import ZhangLS.Spec.Lemma23

/-! # Actual square-root logarithmic derivatives and vertical logarithm transport -/

namespace ZhangLS.Spec

open Complex Set UpperHalfPlane

set_option maxHeartbeats 1000000

theorem lemma52_actual_branch_ne_zero {p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : ψ.IsPrimitive) (hp : p ≠ 1)
    (Y : ℂ → ℂ) (hY : Lemma23ActualBranch ψ Y) {s : ℂ} (hs : 0 < s.im) : Y s ≠ 0 :=
  lemma23_square_root_ne_zero (hY.2 s hs) (lemma23DirichletZ_ne_zero_of_im_pos ψ hψ hp hs)

theorem lemma52_actual_branch_hasDerivAt {p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : ψ.IsPrimitive) (hp : p ≠ 1)
    (Y : ℂ → ℂ) (hY : Lemma23ActualBranch ψ Y) {s : ℂ} (hs : 0 < s.im) :
    HasDerivAt Y (-deriv (lemma23DirichletZ ψ) s /
      (lemma23DirichletZ ψ s ^ 2 * (2 * Y s))) s := by
  have hZne := lemma23DirichletZ_ne_zero_of_im_pos ψ hψ hp hs
  have hd := (lemma23DirichletZ_differentiableAt_of_im_ne_zero ψ hs.ne').hasDerivAt
  have hroot := lemma23_hasDerivAt_square_root_on_open isOpen_upperHalfPlaneSet
    hs hY.1 hY.2 (hd.inv hZne) (inv_ne_zero hZne)
  convert hroot using 1
  simp only [div_div]

theorem lemma52_actual_branch_logDeriv {p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : ψ.IsPrimitive) (hp : p ≠ 1)
    (Y : ℂ → ℂ) (hY : Lemma23ActualBranch ψ Y) {s : ℂ} (hs : 0 < s.im) :
    logDeriv Y s = -logDeriv (lemma23DirichletZ ψ) s / 2 := by
  have hZne := lemma23DirichletZ_ne_zero_of_im_pos ψ hψ hp hs
  have hYne := lemma52_actual_branch_ne_zero ψ hψ hp Y hY hs
  have hd := lemma52_actual_branch_hasDerivAt ψ hψ hp Y hY hs
  have hsq := hY.2 s hs
  have hmul : Y s ^ 2 * lemma23DirichletZ ψ s = 1 := by
    rw [hsq, inv_mul_cancel₀ hZne]
  rw [logDeriv_apply, hd.deriv, logDeriv_apply]
  field_simp
  linear_combination deriv (lemma23DirichletZ ψ) s * hmul

theorem lemma52_vertical_log_transport {f : ℂ → ℂ} {s w a : ℂ} {K : ℝ}
    (hf : ∀ z ∈ upperHalfPlaneSet, DifferentiableAt ℂ f z)
    (hne : ∀ z ∈ upperHalfPlaneSet, f z ≠ 0)
    (hpath : ∀ x ∈ Icc (0 : ℝ) 1, s + (x : ℂ) * w ∈ upperHalfPlaneSet)
    (hb : ∀ x ∈ Icc (0 : ℝ) 1, ‖logDeriv f (s + (x : ℂ) * w) - a‖ ≤ K) :
    ∃ e : ℂ, ‖e‖ ≤ K * ‖w‖ ∧ f (s + w) / f s = Complex.exp (a * w + e) := by
  obtain ⟨ℓ, _, hlift, hd⟩ := lemma23_exists_analytic_log_branch
    lemma23_upperHalfPlane_isSimplyConnected isOpen_upperHalfPlaneSet
    (fun z hz => (hf z hz).continuousAt.continuousWithinAt) hne hf
  let E : ℂ → ℂ := fun z => ℓ (s + z * w) - a * z * w
  have hE (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun x : ℝ => E (x : ℂ))
        ((logDeriv f (s + (x : ℂ) * w) - a) * w) x := by
    have harg : HasDerivAt (fun z : ℂ => s + z * w) w (x : ℂ) := by
      simpa using ((hasDerivAt_id (x : ℂ)).mul_const w).const_add s
    have hdℓ := (hd _ (hpath x hx)).comp (x : ℂ) harg
    have hda : HasDerivAt (fun z : ℂ => a * z * w) (a * w) (x : ℂ) := by
      simpa using ((hasDerivAt_id (x : ℂ)).const_mul a).mul_const w
    have he := hdℓ.sub hda
    have heq : deriv f (s + (x : ℂ) * w) / f (s + (x : ℂ) * w) * w - a * w =
        (logDeriv f (s + (x : ℂ) * w) - a) * w := by rw [logDeriv_apply]; ring
    rw [heq] at he
    exact he.comp_ofReal
  have hn (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      ‖(logDeriv f (s + (x : ℂ) * w) - a) * w‖ ≤ K * ‖w‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hb x hx) (norm_nonneg w)
  have hbound := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (hE x hx).hasDerivWithinAt) hn (convex_Icc (0 : ℝ) 1)
    (by norm_num : (0 : ℝ) ∈ Icc (0 : ℝ) 1) (by norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1)
  norm_num only [Complex.ofReal_one, Complex.ofReal_zero, sub_zero, norm_one, mul_one] at hbound
  refine ⟨E 1 - E 0, hbound, ?_⟩
  have he : a * w + (E 1 - E 0) = ℓ (s + w) - ℓ s := by
    dsimp [E]
    simp only [one_mul, mul_one, zero_mul, mul_zero, add_zero, sub_zero]
    ring
  rw [he, Complex.exp_sub]
  have hs := hpath 0 (by norm_num)
  have hsw := hpath 1 (by norm_num)
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at hs
  simp only [Complex.ofReal_one, one_mul] at hsw
  rw [hlift _ hs, hlift _ hsw]

end ZhangLS.Spec
