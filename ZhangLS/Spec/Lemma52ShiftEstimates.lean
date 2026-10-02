import ZhangLS.Spec.Lemma52BranchTransport
import ZhangLS.Spec.Lemma52Offsets

/-! # Vertical logarithmic transport for every actual square-root branch -/

namespace ZhangLS.Spec

open Complex Set UpperHalfPlane

set_option maxHeartbeats 1000000

theorem lemma52_actual_branch_logDeriv_bound {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : ψ.IsPrimitive) (hp : p ≠ 1)
    (Y : ℂ → ℂ) (hY : Lemma23ActualBranch ψ Y) {s : ℂ}
    (hL : 3 ≤ lemma23PaperL D) (hs : Lemma51InExtendedRegion D s) :
    ‖logDeriv Y s - (Real.log ((p : ℝ) * lemma51PaperT0 D) : ℂ) / 2‖ ≤
      (21 / 2) * lemma23PaperL D ^ (-114 : ℤ) := by
  have hT : 0 < lemma51PaperT0 D := by unfold lemma51PaperT0; positivity
  have hpR : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have him : 0 < s.im := hT.trans_le (lemma51_extended_region_data hL hs).2.2.1
  have hb := lemma51_DirichletZ_logDeriv_at_T0 ψ hψ hp hL hs
  have he : logDeriv Y s - (Real.log ((p : ℝ) * lemma51PaperT0 D) : ℂ) / 2 =
      -(logDeriv (lemma23DirichletZ ψ) s + Complex.log (p : ℂ) +
        (Real.log (lemma51PaperT0 D) : ℂ)) / 2 := by
    rw [lemma52_actual_branch_logDeriv ψ hψ hp Y hY him,
      Real.log_mul hpR.ne' hT.ne', ← Complex.natCast_log]
    push_cast
    ring
  rw [he, norm_div, norm_neg]
  norm_num only [norm_ofNat]
  linarith

theorem lemma52_actual_branch_shift {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : ψ.IsPrimitive) (hp : p ≠ 1)
    (Y : ℂ → ℂ) (hY : Lemma23ActualBranch ψ Y) {s : ℂ} {b : ℝ}
    (hL : 3 ≤ lemma23PaperL D) (hs : Lemma51InRegion D s)
    (hb : 0 ≤ b) (hbhi : b ≤ 3 * lemma44PaperAlpha D) :
    ∃ e : ℂ, ‖e‖ ≤ (21 / 2) * lemma23PaperL D ^ (-114 : ℤ) * b ∧
      Y (s + Complex.I * (b : ℂ)) / Y s =
        Complex.exp ((Real.log ((p : ℝ) * lemma51PaperT0 D) : ℂ) / 2 *
          (Complex.I * (b : ℂ)) + e) := by
  have hw := lemma52_offset_shift_window hL hb hbhi
  have hregion (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :=
    lemma51_shift_segment_region hL hs hw.1 hw.2 hx
  have hT : 0 < lemma51PaperT0 D := by unfold lemma51PaperT0; positivity
  have hpath (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      s + (x : ℂ) * (Complex.I * (b : ℂ)) ∈ upperHalfPlaneSet :=
    hT.trans_le (lemma51_extended_region_data hL (hregion x hx)).2.2.1
  obtain ⟨e, he, hratio⟩ := lemma52_vertical_log_transport
    (fun z hz => (lemma52_actual_branch_hasDerivAt ψ hψ hp Y hY hz).differentiableAt)
    (fun z hz => lemma52_actual_branch_ne_zero ψ hψ hp Y hY hz) hpath
    (fun x hx => lemma52_actual_branch_logDeriv_bound ψ hψ hp Y hY hL (hregion x hx))
  refine ⟨e, ?_, hratio⟩
  simpa only [norm_mul, norm_I, Complex.norm_real, Real.norm_eq_abs,
    one_mul, abs_of_nonneg hb] using he

end ZhangLS.Spec
