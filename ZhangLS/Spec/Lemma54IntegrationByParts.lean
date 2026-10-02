import ZhangLS.Spec.Lemma54DerivativeDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # Two actual Mellin integrations by parts, with all endpoint terms proved -/

namespace ZhangLS.Spec

open Complex MeasureTheory Set Filter
open scoped Topology

set_option maxHeartbeats 1000000

theorem lemma54_mellin_integration_by_parts {f f' : ℝ → ℂ} {s : ℂ} (hs : 0 < s.re)
    (hd : ∀ x : ℝ, 0 < x → HasDerivAt f (f' x) x)
    (hf : MellinConvergent f s) (hf' : MellinConvergent f' (s + 1))
    (hzero : Tendsto (fun x : ℝ => (x : ℂ) ^ s * f x) (𝓝[>] 0) (𝓝 0))
    (hinfty : Tendsto (fun x : ℝ => (x : ℂ) ^ s * f x) atTop (𝓝 0)) :
    s * mellin f s = -mellin f' (s + 1) := by
  have hsne : s ≠ 0 := by intro h; simp [h] at hs
  change IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) * f x) (Ioi 0) at hf
  change IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s + 1 - 1) * f' x) (Ioi 0) at hf'
  have hi : IntegrableOn (fun x : ℝ => f x * (s * (x : ℂ) ^ (s - 1))) (Ioi 0) := by
    have hh : IntegrableOn (fun x : ℝ => s * ((x : ℂ) ^ (s - 1) * f x)) (Ioi 0) :=
      hf.const_mul s
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hh
  have hi' : IntegrableOn (fun x : ℝ => f' x * (x : ℂ) ^ s) (Ioi 0) := by
    simpa only [add_sub_cancel_right, mul_comm] using hf'
  have h := integral_Ioi_mul_deriv_eq_deriv_mul
    (u := f) (u' := f') (v := fun x : ℝ => (x : ℂ) ^ s)
    (v' := fun x : ℝ => s * (x : ℂ) ^ (s - 1))
    (fun x hx => hd x hx)
    (fun x hx => hasDerivAt_ofReal_cpow_const (ne_of_gt hx) hsne) hi hi'
    (by simpa only [Pi.mul_apply, mul_comm] using hzero)
    (by simpa only [Pi.mul_apply, mul_comm] using hinfty)
  have hleft : (∫ x : ℝ in Ioi 0, f x * (s * (x : ℂ) ^ (s - 1))) = s * mellin f s := by
    simp_rw [show ∀ x : ℝ, f x * (s * (x : ℂ) ^ (s - 1)) =
      s * ((x : ℂ) ^ (s - 1) * f x) from fun x => by ring]
    rw [integral_const_mul]
    rfl
  have hright : (∫ x : ℝ in Ioi 0, f' x * (x : ℂ) ^ s) = mellin f' (s + 1) := by
    simp only [mellin, add_sub_cancel_right, smul_eq_mul, mul_comm]
  rw [hleft, hright] at h
  simpa only [sub_self, zero_sub] using h

theorem lemma54_actual_mellin_first_integration_by_parts {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ lemma23PaperL D) {s : ℂ} (hs : 0 < s.re) :
    s * lemma54PaperDeltaMellin D s = -mellin (deriv (lemma53PaperDelta D)) (s + 1) := by
  have hb := lemma54_actual_delta_boundary_products hD hL hs
  apply lemma54_mellin_integration_by_parts hs
    (fun x hx => ?_) (lemma54_mellin_convergent hD hL hs)
    (lemma54_first_deriv_mellin_convergent hD hL (by simpa using (show 0 < s.re + 1 by linarith)))
    hb.1 hb.2
  simpa only [lemma54_actual_delta_deriv hD hx] using lemma54_actual_delta_hasDerivAt hD hx

theorem lemma54_actual_mellin_second_integration_by_parts {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ lemma23PaperL D) {s : ℂ} (hs : 0 < s.re) :
    (s + 1) * mellin (deriv (lemma53PaperDelta D)) (s + 1) =
      -mellin (deriv (deriv (lemma53PaperDelta D))) (s + 2) := by
  have hs' : 0 < (s + 1).re := by simp only [add_re, one_re]; linarith
  have hb := lemma54_actual_first_deriv_boundary_products hD hL hs'
  have h := lemma54_mellin_integration_by_parts hs'
    (f := deriv (lemma53PaperDelta D)) (f' := deriv (deriv (lemma53PaperDelta D)))
    (fun x hx => by
      simpa only [lemma54_actual_delta_second_deriv hD hx] using
        lemma54_actual_delta_deriv_hasDerivAt hD hx)
    (lemma54_first_deriv_mellin_convergent hD hL hs')
    (lemma54_second_deriv_mellin_convergent hD hL (by
      simp only [add_re, one_re]; linarith)) hb.1 hb.2
  convert h using 1 <;> congr 2 <;> ring

theorem lemma54_actual_mellin_twice_by_parts {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ lemma23PaperL D) {s : ℂ} (hs : 0 < s.re) :
    s * (s + 1) * lemma54PaperDeltaMellin D s =
      ∫ x : ℝ in Ioi 0, (x : ℂ) ^ (s + 1) * deriv (deriv (lemma53PaperDelta D)) x := by
  have h1 := lemma54_actual_mellin_first_integration_by_parts hD hL hs
  have h2 := lemma54_actual_mellin_second_integration_by_parts hD hL hs
  have he : mellin (deriv (deriv (lemma53PaperDelta D))) (s + 2) =
      ∫ x : ℝ in Ioi 0, (x : ℂ) ^ (s + 1) * deriv (deriv (lemma53PaperDelta D)) x := by
    unfold mellin
    congr 1
    ext x
    simp only [smul_eq_mul]
    congr 2
    ring
  rw [← he]
  calc
    s * (s + 1) * lemma54PaperDeltaMellin D s =
        (s + 1) * (s * lemma54PaperDeltaMellin D s) := by ring
    _ = -( (s + 1) * mellin (deriv (lemma53PaperDelta D)) (s + 1)) := by rw [h1]; ring
    _ = mellin (deriv (deriv (lemma53PaperDelta D))) (s + 2) := by rw [h2]; ring

theorem lemma54_actual_mellin_twice_by_parts_div {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ lemma23PaperL D) {s : ℂ} (hs : 0 < s.re) :
    lemma54PaperDeltaMellin D s =
      (∫ x : ℝ in Ioi 0, (x : ℂ) ^ (s + 1) * deriv (deriv (lemma53PaperDelta D)) x) /
        (s * (s + 1)) := by
  have hsne : s ≠ 0 := by intro h; simp [h] at hs
  have hs1ne : s + 1 ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp only [add_re, one_re, zero_re] at hr
    linarith
  apply (eq_div_iff (mul_ne_zero hsne hs1ne)).mpr
  calc
    lemma54PaperDeltaMellin D s * (s * (s + 1)) =
        s * (s + 1) * lemma54PaperDeltaMellin D s := by ring
    _ = _ := lemma54_actual_mellin_twice_by_parts hD hL hs

end ZhangLS.Spec
