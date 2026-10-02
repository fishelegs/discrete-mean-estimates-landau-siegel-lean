import ZhangLS.Spec.Section8NumericalPhases
set_option autoImplicit false
noncomputable section
open Complex
namespace Section8

theorem b11_re : b11.re =
    co*(1000*r/(567*Real.pi) + 1000000*r/(107163*Real.pi^2)) + 21*Real.pi/125 +
    si*(1000*r/(567*Real.pi) - 1000000*r/(107163*Real.pi^2)) - 500/(189*Real.pi) := by
  rw [b11_integrated]
  unfold F11 pePrimitive pp
  rw [phase_11]
  norm_num [p, I, co, si, Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im,
    Complex.inv_re, Complex.inv_im, Complex.normSq_apply, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  field_simp [Real.pi_ne_zero]
  norm_num [Complex.I_sq, Complex.mul_re, Complex.mul_im, ← Complex.ofReal_pow]
  field_simp [Real.pi_ne_zero]
  ring

theorem b22_re : b22.re = -Real.pi/10 - 48*r/(125*Real.pi) + 104/(25*Real.pi) - 768*r/(625*Real.pi^2) := by
  rw [b22_integrated]
  unfold F22 pePrimitive pp
  rw [phase_22]
  norm_num [p, I, co, si, Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im,
    Complex.inv_re, Complex.inv_im, Complex.normSq_apply, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  field_simp [Real.pi_ne_zero]
  norm_num [Complex.I_sq, Complex.mul_re, Complex.mul_im, ← Complex.ofReal_pow]
  field_simp [Real.pi_ne_zero]
  ring

theorem b12_re : b12.re = -2*co/5 + 16*co*r/(25*Real.pi) - co/(63*Real.pi) + 640*co*r/(189*Real.pi^2) + 260*co/(63*Real.pi^2) + 16*r*si/(25*Real.pi) + 1097*si/(525*Real.pi) - 640*r*si/(189*Real.pi^2) - 500*si/(189*Real.pi^2) := by
  rw [b12_integrated]
  unfold F12 pePrimitive
  rw [phase_delta, phase_12a, phase_12b]
  norm_num [p, I, co, si, Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im,
    Complex.inv_re, Complex.inv_im, Complex.normSq_apply, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  field_simp [Real.pi_ne_zero]
  norm_num [Complex.I_sq, Complex.mul_re, Complex.mul_im, ← Complex.ofReal_pow]
  field_simp [Real.pi_ne_zero]
  ring

theorem b12_im : b12.im = -16*co*r/(25*Real.pi) - 1097*co/(525*Real.pi) + 640*co*r/(189*Real.pi^2) + 500*co/(189*Real.pi^2) - 2*si/5 + 16*r*si/(25*Real.pi) - si/(63*Real.pi) + 640*r*si/(189*Real.pi^2) + 260*si/(63*Real.pi^2) := by
  rw [b12_integrated]
  unfold F12 pePrimitive
  rw [phase_delta, phase_12a, phase_12b]
  norm_num [p, I, co, si, Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im,
    Complex.inv_re, Complex.inv_im, Complex.normSq_apply, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  field_simp [Real.pi_ne_zero]
  norm_num [Complex.I_sq, Complex.mul_re, Complex.mul_im, ← Complex.ofReal_pow]
  field_simp [Real.pi_ne_zero]
  ring

theorem b21_re : b21.re = -co/(63*Real.pi) - 500*co/(189*Real.pi^2) - 200*r/(189*Real.pi) - 247*si/(189*Real.pi) - 640*r/(189*Real.pi^2) - 500*si/(189*Real.pi^2) := by
  rw [b21_integrated]
  unfold F21 pePrimitive
  rw [phase_neg_delta, phase_22, phase_21b]
  norm_num [p, I, co, si, Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im,
    Complex.inv_re, Complex.inv_im, Complex.normSq_apply, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  field_simp [Real.pi_ne_zero]
  norm_num [Complex.I_sq, Complex.mul_re, Complex.mul_im, ← Complex.ofReal_pow]
  field_simp [Real.pi_ne_zero]
  ring

theorem b21_im : b21.im = -247*co/(189*Real.pi) - 500*co/(189*Real.pi^2) - 200*r/(189*Real.pi) + si/(63*Real.pi) + 640*r/(189*Real.pi^2) + 500*si/(189*Real.pi^2) + 1280/(189*Real.pi^2) := by
  rw [b21_integrated]
  unfold F21 pePrimitive
  rw [phase_neg_delta, phase_22, phase_21b]
  norm_num [p, I, co, si, Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im,
    Complex.inv_re, Complex.inv_im, Complex.normSq_apply, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  field_simp [Real.pi_ne_zero]
  norm_num [Complex.I_sq, Complex.mul_re, Complex.mul_im, ← Complex.ofReal_pow]
  field_simp [Real.pi_ne_zero]
  ring

end Section8
