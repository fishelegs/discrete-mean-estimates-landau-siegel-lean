import ZhangLS.Spec.PrimitiveConductorFamily
import ZhangLS.Spec.Proposition141Support

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

/-- Exact positive quotient data, with no coprimality restriction. -/
theorem quotientConductor_forward {D₂ k r : ℕ} (hD : 0 < D₂) (hk : 0 < k)
    (hr : r ∣ D₂*k) :
    0 < r ∧ 0 < D₂*k/r ∧ D₂ ∣ r*(D₂*k/r) ∧ r*(D₂*k/r)/D₂ = k := by
  have hN := Nat.mul_pos hD hk
  have hrp := Nat.pos_of_dvd_of_pos hr hN
  have he : r*(D₂*k/r) = D₂*k := Nat.mul_div_cancel' hr
  refine ⟨hrp,Nat.div_pos (Nat.le_of_dvd hN hr) hrp,?_,?_⟩
  · rw [he]; exact Nat.dvd_mul_right _ _
  · rw [he,Nat.mul_div_right _ hD]

theorem quotientConductor_backward {D₂ r h : ℕ} (hD : 0 < D₂) (hr : 0 < r)
    (hh : 0 < h) (hdiv : D₂ ∣ r*h) :
    0 < r*h/D₂ ∧ r ∣ D₂*(r*h/D₂) ∧ D₂*(r*h/D₂)/r = h := by
  have he : D₂*(r*h/D₂) = r*h := Nat.mul_div_cancel' hdiv
  refine ⟨Nat.div_pos (Nat.le_of_dvd (Nat.mul_pos hr hh) hdiv) hD,?_,?_⟩
  · rw [he]; exact Nat.dvd_mul_right _ _
  · rw [he,Nat.mul_div_right _ hr]

/-- The real weight used by the primitive-conductor bound, including r=1. -/
theorem quotientConductor_weight {D₂ d k r h : ℕ} (hD : 0 < D₂) (hr : 0 < r)
    (he : r*h = D₂*k) :
    Real.sqrt (r:ℝ) / ((d:ℝ)*(k:ℝ)*((D₂*k).totient:ℝ)) =
      (D₂:ℝ) / ((d:ℝ)*(h:ℝ)*((h*r).totient:ℝ)*Real.sqrt (r:ℝ)) := by
  have heR : (r:ℝ)*(h:ℝ) = (D₂:ℝ)*(k:ℝ) := by exact_mod_cast he
  have hrR : 0 < (r:ℝ) := by exact_mod_cast hr
  have hs : Real.sqrt (r:ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hrR)
  have hs2 : Real.sqrt (r:ℝ)^2 = (r:ℝ) := Real.sq_sqrt hrR.le
  rw [show h*r = D₂*k by simpa [mul_comm] using he]
  by_cases hd : d=0
  · subst d; simp
  by_cases hk : k=0
  · subst k
    have hh : h=0 := by nlinarith
    subst h; simp
  have hφ : ((D₂*k).totient:ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.mul_pos hD (Nat.pos_of_ne_zero hk))).ne'
  have hdR : (d:ℝ) ≠ 0 := by exact_mod_cast hd
  have hkR : (k:ℝ) ≠ 0 := by exact_mod_cast hk
  have hh : h ≠ 0 := by intro hz; subst h; rw [mul_zero] at he; exact (Nat.mul_ne_zero hD.ne' hk) he.symm
  have hhR : (h:ℝ) ≠ 0 := by exact_mod_cast hh
  field_simp
  nlinarith [congrArg (fun x : ℝ => x*(d:ℝ)*((D₂*k).totient:ℝ)) heR]

end ZhangLS.Spec
