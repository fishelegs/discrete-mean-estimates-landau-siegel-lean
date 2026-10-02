import ZhangLS.Spec.Section8NumericalObjects
set_option autoImplicit false
noncomputable section
open Complex intervalIntegral
namespace Section8

theorem h11_closed (z : ℝ) : h11 z =
    (16/3 - 8*p*I/3*z) * exp (3*p*I/2*z) +
    (-4/3 + 2*p*I/3*z - (p*I)^2*(z:ℂ)^2) := by
  have he : exp (3*p*I/2*z) * exp (-3*p*I/2*z) = 1 := by
    rw [← Complex.exp_add]
    convert Complex.exp_zero using 1
    congr 1
    ring
  dsimp [h11, f16, f26, f36, g16, g26, g36]
  linear_combination (-4/3 + 2*p*I/3*z - (p*I)^2*(z:ℂ)^2) * he

theorem h22_closed (z : ℝ) : h22 z =
    (48/25 + 24*p*I/25*z) * exp (5*p*I/2*z) +
    (52/25 + 6*p*I/25*z + 3*(p*I)^2/5*(z:ℂ)^2) := by
  have he : exp (5*p*I/2*z) * exp (-5*p*I/2*z) = 1 := by
    rw [← Complex.exp_add]
    convert Complex.exp_zero using 1
    congr 1
    ring
  dsimp [h22, f17, f27, f37, g17, g27, g37]
  linear_combination (52/25 + 6*p*I/25*z + 3*(p*I)^2/5*(z:ℂ)^2) * he

theorem h12_closed (z : ℝ) : h12 z =
    exp (3*p*I/500) * ((48/25 - 12*p*I/3125 - 24*p*I/25*z) * exp (3*p*I/2*z) +
      (52/25 - 51*p*I/6250 + ((p*I)^2/625 - 46*p*I/25)*z +
      2*(p*I)^2/5*(z:ℂ)^2) * exp (-p*I*z)) := by
  have hs : exp (3*p*I/2*((z+1/250:ℝ):ℂ)) = exp (3*p*I/500)*exp (3*p*I/2*z) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have he : exp (3*p*I/2*z) * exp (-5*p*I/2*z) = exp (-p*I*z) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  dsimp [h12, f16, f26, f36, g17, g27, g37]
  rw [hs]
  push_cast
  linear_combination exp (3*p*I/500) *
    (52/25 - 51*p*I/6250 + ((p*I)^2/625 - 46*p*I/25)*z + 2*(p*I)^2/5*(z:ℂ)^2) * he

theorem h21_closed (z : ℝ) : h21 z =
    (16/3 + 8*p*I/3*z) * exp (5*p*I/2*z) +
    exp (-3*p*I/500) * (-4/3 + p*I/250 - 2*p*I/3*z) * exp (p*I*z) := by
  have hs : exp (-3*p*I/2*((z+1/250:ℝ):ℂ)) = exp (-3*p*I/500)*exp (-3*p*I/2*z) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have he : exp (5*p*I/2*z) * exp (-3*p*I/2*z) = exp (p*I*z) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  dsimp [h21, f17, f27, f37, g16, g26, g36]
  rw [hs]
  push_cast
  linear_combination exp (-3*p*I/500) * (-4/3 + p*I/250 - 2*p*I/3*z) * he

end Section8
