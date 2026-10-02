import ZhangLS.Spec.Section8NumericalIntegrals
import ZhangLS.Spec.Section8NumericalBounds
set_option autoImplicit false
noncomputable section
open Complex
namespace Section8

abbrev r : ℝ := Real.sqrt 2
abbrev co : ℝ := Real.cos delta
abbrev si : ℝ := Real.sin delta

theorem phase_three : exp (3*p*I/4) = -(r:ℂ)/2 + (r:ℂ)/2*I := by
  have h : 3*p*I/4 = (((Real.pi-Real.pi/4:ℝ):ℂ)*I) := by push_cast; ring
  rw [h, Complex.exp_ofReal_mul_I, Real.cos_pi_sub, Real.sin_pi_sub,
    Real.cos_pi_div_four, Real.sin_pi_div_four]
  push_cast
  ring

theorem phase_five : exp (5*p*I/4) = -(r:ℂ)/2 - (r:ℂ)/2*I := by
  have h : 5*p*I/4 = (((Real.pi+Real.pi/4:ℝ):ℂ)*I) := by push_cast; ring
  rw [h, Complex.exp_ofReal_mul_I, Real.cos_add, Real.sin_add,
    Real.cos_pi_div_four, Real.sin_pi_div_four, Real.cos_pi, Real.sin_pi]
  push_cast
  ring

theorem phase_half : exp (p*I/2) = I := by
  have h : p*I/2 = (((Real.pi/2:ℝ):ℂ)*I) := by push_cast; ring
  rw [h, Complex.exp_ofReal_mul_I, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

theorem phase_neg_half : exp (-p*I/2) = -I := by
  have h : -p*I/2 = (((-(Real.pi/2):ℝ):ℂ)*I) := by push_cast; ring
  rw [h, Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

theorem phase_delta : exp (3*p*I/500) = (co:ℂ) + (si:ℂ)*I := by
  have h : 3*p*I/500 = (delta:ℂ)*I := by unfold delta; push_cast; ring
  rw [h, Complex.exp_ofReal_mul_I]

theorem phase_neg_delta : exp (-3*p*I/500) = (co:ℂ) - (si:ℂ)*I := by
  have h : -3*p*I/500 = (((-delta:ℝ):ℂ)*I) := by unfold delta; push_cast; ring
  rw [h, Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

theorem phase_11 : exp ((3*p*I/2)*((63/125:ℝ):ℂ)) =
    (-(r:ℂ)/2 + (r:ℂ)/2*I) * ((co:ℂ) + (si:ℂ)*I) := by
  have h : (3*p*I/2)*((63/125:ℝ):ℂ) = 3*p*I/4 + 3*p*I/500 := by push_cast; ring
  rw [h, Complex.exp_add, phase_three, phase_delta]

theorem phase_22 : exp ((5*p*I/2)*((1/2:ℝ):ℂ)) = -(r:ℂ)/2 - (r:ℂ)/2*I := by
  have h : (5*p*I/2)*((1/2:ℝ):ℂ) = 5*p*I/4 := by push_cast; ring
  rw [h, phase_five]

theorem phase_12a : exp ((3*p*I/2)*((1/2:ℝ):ℂ)) = -(r:ℂ)/2 + (r:ℂ)/2*I := by
  have h : (3*p*I/2)*((1/2:ℝ):ℂ) = 3*p*I/4 := by push_cast; ring
  rw [h, phase_three]

theorem phase_12b : exp ((-p*I)*((1/2:ℝ):ℂ)) = -I := by
  have h : (-p*I)*((1/2:ℝ):ℂ) = -p*I/2 := by push_cast; ring
  rw [h, phase_neg_half]

theorem phase_21b : exp ((p*I)*((1/2:ℝ):ℂ)) = I := by
  have h : (p*I)*((1/2:ℝ):ℂ) = p*I/2 := by push_cast; ring
  rw [h, phase_half]

end Section8
