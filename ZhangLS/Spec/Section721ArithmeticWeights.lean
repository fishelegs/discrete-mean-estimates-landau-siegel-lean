import ZhangLS.Spec.Section721FiniteReindex

set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 4000000

/-- The simultaneous Möbius, totient and complex-power cancellation in (7.21).
Its noncoprime case follows from the actual product μ(rk)μ(r)=0. -/
theorem section721_weight_rearrangement (b : ℂ) {a d r k m : ℕ}
    (ha : 0<a) (hd : 0<d) (hr : 0<r) (hk : 0<k) (hm : 0<m) :
    (ArithmeticFunction.moebius (r*k) : ℂ) /
      ((a : ℂ)*(d : ℂ)*(Nat.totient (r*k) : ℂ)*(r*k : ℂ)^b) /
      (r*m : ℂ)^(1-b) * (ArithmeticFunction.moebius r : ℂ) =
    (↑|ArithmeticFunction.moebius r| : ℂ) /
      ((d : ℂ)*(r : ℂ)*(Nat.totient r : ℂ)) /
      (m : ℂ)^(1-b) / (a*k : ℂ) *
      (if k.Coprime r then
        (ArithmeticFunction.moebius k : ℂ)*(k : ℂ)^(1-b)/(Nat.totient k : ℂ)
      else 0) := by
  have han : (a : ℂ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt ha)
  have hdn : (d : ℂ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
  have hrn : (r : ℂ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hr)
  have hkn : (k : ℂ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk)
  have hmn : (m : ℂ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  have hpr : (Nat.totient r : ℂ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.totient_pos.mpr hr))
  have hpk : (Nat.totient k : ℂ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.totient_pos.mpr hk))
  have hrb : (r : ℂ)^b≠0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hrn)
  have hkb : (k : ℂ)^b≠0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hkn)
  have hms : (m : ℂ)^(1-b)≠0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hmn)
  by_cases h : r.Coprime k
  · have hmu : (ArithmeticFunction.moebius (r*k) : ℂ)*(ArithmeticFunction.moebius r : ℂ) =
        (↑|ArithmeticFunction.moebius r| : ℂ)*(ArithmeticFunction.moebius k : ℂ) := by
      exact_mod_cast proposition71_mobius_coprime_factor h
    rw [if_pos h.symm,Nat.totient_mul h,Nat.cast_mul,
      Complex.natCast_mul_natCast_cpow,Complex.natCast_mul_natCast_cpow,
      Complex.cpow_sub 1 b hrn,Complex.cpow_one,
      Complex.cpow_sub 1 b hkn,Complex.cpow_one]
    field_simp
    exact hmu
  · have hmu : (ArithmeticFunction.moebius (r*k) : ℂ)*(ArithmeticFunction.moebius r : ℂ)=0 := by
      exact_mod_cast (by simpa [h] using proposition71_mobius_factor_all r k)
    rw [if_neg (fun hh => h hh.symm),mul_zero]
    calc
      _ = ((ArithmeticFunction.moebius (r*k) : ℂ)*(ArithmeticFunction.moebius r : ℂ)) /
          ((a : ℂ)*(d : ℂ)*(Nat.totient (r*k) : ℂ)*(r*k : ℂ)^b) /
          (r*m : ℂ)^(1-b) := by ring
      _ = 0 := by rw [hmu]; simp

end ZhangLS.Spec
