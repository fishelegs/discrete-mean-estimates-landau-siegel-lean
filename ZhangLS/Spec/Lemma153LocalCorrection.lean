import ZhangLS.Spec.Lemma153WeightedKernel
/-! Exact extraction for the Section 15.3 local factors.
B,C,E,F denote the four local M-series before the common removal factor:
B=(q∤d,q∤l), C=(q∤d,q∣l), E=(q∣d,q∤l), F=(q∣d,q∣l).
The source definitions give B=C+λE−λF. The extraction variable is
` t = χ(q) q^βⱼ `; using χ(q) instead would leave a first-order term. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def lemma153LocalChiVarpi (B C E F lam t : ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 1 else
    C/B + lam*E/B*t^n + lam*F/B*(lemma83LocalH2 1 t n-1-t^n)

noncomputable def lemma153ShiftedLocalCorrection (B C E F lam t z : ℂ) : ℂ :=
  (C-lam*F)/B*(1-t*z)^2 + (lam*E-lam*F)/B*(1-z)^2 +
    lam*F/B*(1-t*z^2)

lemma lemma153_local_chi_varpi_eq (B C E F lam t : ℂ)
    (hB : B ≠ 0) (hcompat : B = C+lam*E-lam*F) (n : ℕ) :
    lemma153LocalChiVarpi B C E F lam t n =
      (C-lam*F)/B + (lam*E-lam*F)/B*t^n + lam*F/B*lemma83LocalH2 1 t n := by
  unfold lemma153LocalChiVarpi
  split_ifs with hn
  · subst n
    simp only [lemma83LocalH2,lemma83AddConvolution,antidiagonal_zero,sum_singleton,
      pow_zero,mul_one,one_mul]
    field_simp
    linear_combination hcompat
  · ring

lemma lemma153_actual_local_hasSum (B C E F lam t z : ℂ)
    (hB : B ≠ 0) (hcompat : B = C+lam*E-lam*F)
    (hz : ‖z‖ < 1) (htz : ‖t*z‖ < 1) :
    HasSum (fun n : ℕ => ((n:ℂ)+1)*lemma153LocalChiVarpi B C E F lam t n*z^n)
      (lemma153ShiftedLocalCorrection B C E F lam t z /
        ((1-z)^2*(1-t*z)^2)) := by
  have h0 := (lemma153_weighted_geometric_hasSum z hz).mul_left ((C-lam*F)/B)
  have h1 := (lemma153_weighted_geometric_hasSum (t*z) htz).mul_left ((lam*E-lam*F)/B)
  have h2 := (lemma153_weighted_h2_hasSum 1 t z (by simpa using hz) htz).mul_left (lam*F/B)
  convert (h0.add h1).add h2 using 1
  · funext n
    rw [lemma153_local_chi_varpi_eq B C E F lam t hB hcompat n,mul_pow]
    ring
  · have hzn := lemma83_one_sub_ne_zero hz
    have htzn := lemma83_one_sub_ne_zero htz
    unfold lemma153ShiftedLocalCorrection
    simp only [one_mul]
    field_simp
    all_goals ring

lemma lemma153_shifted_local_extraction (B C E F lam t z : ℂ)
    (hB : B ≠ 0) (hcompat : B = C+lam*E-lam*F)
    (hz : ‖z‖ < 1) (htz : ‖t*z‖ < 1) :
    (1-z)^2*(1-t*z)^2 *
      (∑' n : ℕ, ((n:ℂ)+1)*lemma153LocalChiVarpi B C E F lam t n*z^n) =
        lemma153ShiftedLocalCorrection B C E F lam t z := by
  rw [(lemma153_actual_local_hasSum B C E F lam t z hB hcompat hz htz).tsum_eq]
  exact mul_div_cancel₀ _ (mul_ne_zero (pow_ne_zero 2 (lemma83_one_sub_ne_zero hz))
    (pow_ne_zero 2 (lemma83_one_sub_ne_zero htz)))

lemma lemma153_shifted_local_polynomial (B C E F lam t z : ℂ)
    (hB : B ≠ 0) (hcompat : B = C+lam*E-lam*F) :
    lemma153ShiftedLocalCorrection B C E F lam t z =
      1 + (2*(C+lam*E*t)/B-2*(1+t))*z +
        (t^2*C+lam*E-(t^2+t+1)*lam*F)/B*z^2 := by
  unfold lemma153ShiftedLocalCorrection
  field_simp
  linear_combination -(1-2*z-2*t*z)*hcompat

/-- An explicit constant nonzero shift changes the removed first-order term.
This identity records the issue without asserting any unproved global zero. -/
lemma lemma153_original_shifted_difference (v t z U : ℂ) (htz : 1-t*z ≠ 0) :
    ((1-v*z)^2/(1-t*z)^2)*U-U =
      U*(2*(t-v)*z+(v^2-t^2)*z^2)/(1-t*z)^2 := by
  have hzt : 1-z*t ≠ 0 := by simpa [mul_comm] using htz
  field_simp [htz,hzt]
  all_goals ring

/-- The first coefficient of the old removal equals the repaired coefficient
plus 2χ(q)(q^βⱼ−1). -/
lemma lemma153_first_coefficient_shift_error (B C E lam v w : ℂ) :
    (2*(C+lam*E*(v*w))/B-2*(1+v)) -
      (2*(C+lam*E*(v*w))/B-2*(1+v*w)) = 2*v*(w-1) := by ring

/-- The unperturbed model has a quadratic correction after shifted extraction. -/
lemma lemma153_shifted_free_factor (t z : ℂ) :
    lemma153ShiftedLocalCorrection 1 1 1 1 1 t z = 1-t*z^2 := by
  simp [lemma153ShiftedLocalCorrection]

end ZhangLS.Spec
