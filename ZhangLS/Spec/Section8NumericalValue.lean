import ZhangLS.Spec.Section8NumericalCoordinates
set_option autoImplicit false
noncomputable section
open Complex
namespace Section8

def closedValue (x y u v : ℝ) : ℝ :=
  -94977*u/125000 + 288912124*u*y/(44296875*x) + 6246962*u/(2953125*x) + 1050334352*u*y/(66976875*x^2) - 1405018*u/(118125*x^2) - 5770120277*x/25000000000 + 27799*v/25000 + 131291794*y*v/(44296875*x) - 26313520697059*y/(3691406250000*x) + 31006183*v/(19687500*x) + 27003485520589/(1476562500000*x) - 2311296992*y*v/(66976875*x^2) - 4595551947059*y/(1153564453125*x^2) - 334739*v/(23625*x^2) + 444784/(23625*x^2)

theorem c1_re_closed : c1.re = closedValue Real.pi r co si := by
  norm_num [c1, c11, c22, c12, c21, iota2, I, Complex.sq_norm, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im]
  rw [b11_re, b22_re, b12_re, b12_im, b21_re, b21_im]
  unfold closedValue
  ring

theorem c1_im_zero : c1.im = 0 := by
  norm_num [c1, c11, c22, c12, c21, iota2, I, Complex.sq_norm, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im]
  ring

end Section8
