import ZhangLS.Spec.Section8NumericalAlgebra
set_option autoImplicit false
noncomputable section
open Complex intervalIntegral
namespace Section8

def pp (A B C : ℂ) (z : ℝ) : ℂ := A*(z:ℂ) + B*(z:ℂ)^2/2 + C*(z:ℂ)^3/3

theorem pp_hasDerivAt (A B C : ℂ) (z : ℝ) :
    HasDerivAt (pp A B C) (A + B*z + C*(z:ℂ)^2) z := by
  have h : HasDerivAt (fun w : ℂ => A*w + B*w^2/2 + C*w^3/3)
      (A + B*z + C*(z:ℂ)^2) (z:ℂ) := by
    convert (((hasDerivAt_id (z:ℂ)).const_mul A).add
      ((((hasDerivAt_id (z:ℂ)).pow 2).const_mul B).div_const 2)).add
      ((((hasDerivAt_id (z:ℂ)).pow 3).const_mul C).div_const 3) using 1
    dsimp
    ring
  exact h.comp_ofReal

def F11 (z : ℝ) : ℂ := pePrimitive (16/3) (-8*p*I/3) 0 (3*p*I/2) z +
  pp (-4/3) (2*p*I/3) (-(p*I)^2) z
def F22 (z : ℝ) : ℂ := pePrimitive (48/25) (24*p*I/25) 0 (5*p*I/2) z +
  pp (52/25) (6*p*I/25) (3*(p*I)^2/5) z
def F12 (z : ℝ) : ℂ := exp (3*p*I/500) *
  (pePrimitive (48/25 - 12*p*I/3125) (-24*p*I/25) 0 (3*p*I/2) z +
   pePrimitive (52/25 - 51*p*I/6250) ((p*I)^2/625 - 46*p*I/25)
    (2*(p*I)^2/5) (-p*I) z)
def F21 (z : ℝ) : ℂ := pePrimitive (16/3) (8*p*I/3) 0 (5*p*I/2) z +
  exp (-3*p*I/500) * pePrimitive (-4/3 + p*I/250) (-2*p*I/3) 0 (p*I) z

lemma p_ne : p ≠ 0 := by simpa only [p, ne_eq, Complex.ofReal_eq_zero] using Real.pi_ne_zero
lemma k3_ne : 3*p*I/2 ≠ 0 := by exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) p_ne) Complex.I_ne_zero) (by norm_num)
lemma k5_ne : 5*p*I/2 ≠ 0 := by exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) p_ne) Complex.I_ne_zero) (by norm_num)
lemma k_ne : p*I ≠ 0 := mul_ne_zero p_ne Complex.I_ne_zero

 theorem F11_hasDerivAt (z : ℝ) : HasDerivAt F11 (h11 z) z := by
  convert (pePrimitive_hasDerivAt (16/3) (-8*p*I/3) 0 _ k3_ne z).add
    (pp_hasDerivAt (-4/3) (2*p*I/3) (-(p*I)^2) z) using 1
  rw [h11_closed]
  dsimp [pe]
  ring

 theorem F22_hasDerivAt (z : ℝ) : HasDerivAt F22 (h22 z) z := by
  convert (pePrimitive_hasDerivAt (48/25) (24*p*I/25) 0 _ k5_ne z).add
    (pp_hasDerivAt (52/25) (6*p*I/25) (3*(p*I)^2/5) z) using 1
  rw [h22_closed]
  dsimp [pe]
  ring

 theorem F12_hasDerivAt (z : ℝ) : HasDerivAt F12 (h12 z) z := by
  convert ((pePrimitive_hasDerivAt (48/25 - 12*p*I/3125) (-24*p*I/25) 0 _ k3_ne z).add
    (pePrimitive_hasDerivAt (52/25 - 51*p*I/6250) ((p*I)^2/625 - 46*p*I/25)
      (2*(p*I)^2/5) (-p*I) (by simpa only [neg_mul] using neg_ne_zero.mpr k_ne) z)).const_mul
    (exp (3*p*I/500)) using 1
  rw [h12_closed]
  dsimp [pe]
  ring

 theorem F21_hasDerivAt (z : ℝ) : HasDerivAt F21 (h21 z) z := by
  convert (pePrimitive_hasDerivAt (16/3) (8*p*I/3) 0 _ k5_ne z).add
    ((pePrimitive_hasDerivAt (-4/3+p*I/250) (-2*p*I/3) 0 _ k_ne z).const_mul
      (exp (-3*p*I/500))) using 1
  rw [h21_closed]
  dsimp [pe]
  ring

 theorem b11_integrated : b11 = 1/((63/125)^2*p) * (F11 (63/125) - F11 0) := by
  unfold b11
  congr 1
  apply integral_eq_sub_of_hasDerivAt (fun z _ => F11_hasDerivAt z)
  exact (by unfold h11 f16 f26 f36 g16 g26 g36; fun_prop : Continuous h11).intervalIntegrable _ _
 theorem b22_integrated : b22 = 1/((1/2)^2*p) * (F22 (1/2) - F22 0) := by
  unfold b22
  congr 1
  apply integral_eq_sub_of_hasDerivAt (fun z _ => F22_hasDerivAt z)
  exact (by unfold h22 f17 f27 f37 g17 g27 g37; fun_prop : Continuous h22).intervalIntegrable _ _
 theorem b12_integrated : b12 = 1/((63/125)*(1/2)*p) * (F12 (1/2) - F12 0) := by
  unfold b12
  congr 1
  apply integral_eq_sub_of_hasDerivAt (fun z _ => F12_hasDerivAt z)
  exact (by unfold h12 f16 f26 f36 g17 g27 g37; fun_prop : Continuous h12).intervalIntegrable _ _
 theorem b21_integrated : b21 = 1/((63/125)*(1/2)*p) * (F21 (1/2) - F21 0) := by
  unfold b21
  congr 1
  apply integral_eq_sub_of_hasDerivAt (fun z _ => F21_hasDerivAt z)
  exact (by unfold h21 f17 f27 f37 g16 g26 g36; fun_prop : Continuous h21).intervalIntegrable _ _

end Section8
