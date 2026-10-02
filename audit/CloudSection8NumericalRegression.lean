import ZhangLS.Spec.Section8NumericalLower

/-! Definitional regression tests against the literal source, independently expanded. -/
set_option autoImplicit false
noncomputable section
open Complex
namespace Section8

example (z : ℝ) : f16 z = (1+(Real.pi:ℂ)*Complex.I/2*z)*exp (3*(Real.pi:ℂ)*Complex.I/2*z) := rfl
example (z : ℝ) : f26 z = (1-(Real.pi:ℂ)*Complex.I/2*z)*exp (3*(Real.pi:ℂ)*Complex.I/2*z) := rfl
example (z : ℝ) : f36 z = (1-3*(Real.pi:ℂ)*Complex.I/2*z)*exp (3*(Real.pi:ℂ)*Complex.I/2*z) := rfl
example (z : ℝ) : f17 z = (1+3*(Real.pi:ℂ)*Complex.I/2*z)*exp (5*(Real.pi:ℂ)*Complex.I/2*z) := rfl
example (z : ℝ) : f27 z = (1+(Real.pi:ℂ)*Complex.I/2*z)*exp (5*(Real.pi:ℂ)*Complex.I/2*z) := rfl
example (z : ℝ) : f37 z = (1-(Real.pi:ℂ)*Complex.I/2*z)*exp (5*(Real.pi:ℂ)*Complex.I/2*z) := rfl
example (z : ℝ) : g16 z = 8/3+(-5/3-(Real.pi:ℂ)*Complex.I/2*z)*exp (-3*(Real.pi:ℂ)*Complex.I/2*z) := rfl
example (z : ℝ) : g26 z = 4/3+(-1/3+(Real.pi:ℂ)*Complex.I/2*z)*exp (-3*(Real.pi:ℂ)*Complex.I/2*z) := rfl
example (z : ℝ) : g36 z = 8/9+(1/9+(Real.pi:ℂ)*Complex.I/6*z)*exp (-3*(Real.pi:ℂ)*Complex.I/2*z) := rfl
example (z : ℝ) : g17 z = 24/25+(1/25+(Real.pi:ℂ)*Complex.I/10*z)*exp (-5*(Real.pi:ℂ)*Complex.I/2*z) := rfl
example (z : ℝ) : g27 z = 12/25+(13/25+3*(Real.pi:ℂ)*Complex.I/10*z)*exp (-5*(Real.pi:ℂ)*Complex.I/2*z) := rfl
example (z : ℝ) : g37 z = 8/25+(17/25-3*(Real.pi:ℂ)*Complex.I/10*z)*exp (-5*(Real.pi:ℂ)*Complex.I/2*z) := rfl

example (z : ℝ) : h11 z = (1:ℂ)/2*f16 z*g16 z + 2*f26 z*g26 z + 3/2*f36 z*g36 z := rfl
example (z : ℝ) : h22 z = (1:ℂ)/2*f17 z*g17 z + 2*f27 z*g27 z + 3/2*f37 z*g37 z := rfl
example (z : ℝ) : h12 z = (1:ℂ)/2*f16 (z+1/250)*g17 z + 2*f26 (z+1/250)*g27 z + 3/2*f36 (z+1/250)*g37 z := rfl
example (z : ℝ) : h21 z = (1:ℂ)/2*f17 z*g16 (z+1/250) + 2*f27 z*g26 (z+1/250) + 3/2*f37 z*g36 (z+1/250) := rfl

example : b11 = (1:ℂ)/((63/125)^2*(Real.pi:ℂ)) * ∫ z in (0:ℝ)..(63/125), h11 z := rfl
example : b22 = (1:ℂ)/((1/2)^2*(Real.pi:ℂ)) * ∫ z in (0:ℝ)..(1/2), h22 z := rfl
example : b12 = (1:ℂ)/((63/125)*(1/2)*(Real.pi:ℂ)) * ∫ z in (0:ℝ)..(1/2), h12 z := rfl
example : b21 = (1:ℂ)/((63/125)*(1/2)*(Real.pi:ℂ)) * ∫ z in (0:ℝ)..(1/2), h21 z := rfl
example : iota2 = (94977:ℂ)/100000-(138995:ℂ)/100000*Complex.I := rfl
example : c12 = b12 + star b21 := rfl
example : c21 = star c12 := rfl
example : c1 = (b11+star b11) + iota2*star (b12+star b21) +
  star iota2*(b12+star b21) + (‖iota2‖^2:ℝ)*(b22+star b22) := rfl

-- End-to-end semantic assertion: the literal complex expression is real.
theorem c1_eq_ofReal_re : c1 = (c1.re:ℂ) := by
  apply Complex.ext <;> simp [c1_im_zero]

-- This is an unconditional fact about the literal functions and actual interval integrals.
example : 7 < c1.re := c1_re_gt_seven
example : ¬ c1.re < (69955:ℝ)/10000 := printed_8_24_is_false
end Section8


#print axioms Section8.p
#print axioms Section8.I
#print axioms Section8.f16
#print axioms Section8.f26
#print axioms Section8.f36
#print axioms Section8.f17
#print axioms Section8.f27
#print axioms Section8.f37
#print axioms Section8.g16
#print axioms Section8.g26
#print axioms Section8.g36
#print axioms Section8.g17
#print axioms Section8.g27
#print axioms Section8.g37
#print axioms Section8.h11
#print axioms Section8.h22
#print axioms Section8.h21
#print axioms Section8.h12
#print axioms Section8.b11
#print axioms Section8.b22
#print axioms Section8.b21
#print axioms Section8.b12
#print axioms Section8.c11
#print axioms Section8.c22
#print axioms Section8.c12
#print axioms Section8.c21
#print axioms Section8.iota2
#print axioms Section8.c1
#print axioms Section8.pe
#print axioms Section8.pePrimitive
#print axioms Section8.pePrimitive_hasDerivAt
#print axioms Section8.integral_pe
#print axioms Section8.h11_closed
#print axioms Section8.h22_closed
#print axioms Section8.h12_closed
#print axioms Section8.h21_closed
#print axioms Section8.pp
#print axioms Section8.pp_hasDerivAt
#print axioms Section8.F11
#print axioms Section8.F22
#print axioms Section8.F12
#print axioms Section8.F21
#print axioms Section8.p_ne
#print axioms Section8.k3_ne
#print axioms Section8.k5_ne
#print axioms Section8.k_ne
#print axioms Section8.F11_hasDerivAt
#print axioms Section8.F22_hasDerivAt
#print axioms Section8.F12_hasDerivAt
#print axioms Section8.F21_hasDerivAt
#print axioms Section8.b11_integrated
#print axioms Section8.b22_integrated
#print axioms Section8.b12_integrated
#print axioms Section8.b21_integrated
#print axioms Section8.delta
#print axioms Section8.pi_bounds
#print axioms Section8.sqrt_two_bounds
#print axioms Section8.delta_bounds
#print axioms Section8.sin_delta_bounds
#print axioms Section8.cos_delta_bounds
#print axioms Section8.r
#print axioms Section8.co
#print axioms Section8.si
#print axioms Section8.phase_three
#print axioms Section8.phase_five
#print axioms Section8.phase_half
#print axioms Section8.phase_neg_half
#print axioms Section8.phase_delta
#print axioms Section8.phase_neg_delta
#print axioms Section8.phase_11
#print axioms Section8.phase_22
#print axioms Section8.phase_12a
#print axioms Section8.phase_12b
#print axioms Section8.phase_21b
#print axioms Section8.b11_re
#print axioms Section8.b22_re
#print axioms Section8.b12_re
#print axioms Section8.b12_im
#print axioms Section8.b21_re
#print axioms Section8.b21_im
#print axioms Section8.closedValue
#print axioms Section8.c1_re_closed
#print axioms Section8.c1_im_zero
#print axioms Section8.closedValue_lower
#print axioms Section8.c1_re_lower
#print axioms Section8.c1_re_gt_seven
#print axioms Section8.printed_8_24_is_false
#print axioms Section8.c1_eq_ofReal_re

#check Section8.c1_re_lower
#check Section8.c1_re_gt_seven
#check Section8.printed_8_24_is_false
