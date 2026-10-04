import ZhangLS.Spec.FixedHDiagonalIBP
import Mathlib.Analysis.Complex.Basic

/-! Exact real-part algebra, retaining literal cyclic `j+1`, `j+2`. -/
set_option autoImplicit false
namespace ZhangLS.Spec.FixedHDiagonal
open Complex MeasureTheory

noncomputable def scaledShift (δ : ℝ) (j : Fin 3) : ℂ :=
  I * ((Real.pi * (if j = 0 then 1 - 5*δ else
    if j = 1 then 2*(1+δ) else 3*(1-δ)) : ℝ) : ℂ)

noncomputable def firstKernel (β : Fin 3 → ℂ) (j : Fin 3)
    (f f' : ℝ → ℝ) (x : ℝ) : ℂ :=
  -(f' x : ℂ) - β j * (f x : ℂ)

noncomputable def secondKernel (β : Fin 3 → ℂ) (j : Fin 3)
    (f f' : ℝ → ℝ) (b x : ℝ) : ℂ :=
  -(f' x : ℂ) + (β (j+1) + β (j+2)) * (f x : ℂ) +
    (β (j+1) * β (j+2)) * (tail f b x : ℂ)

lemma pure_imaginary_product (u v w p t h : ℝ) :
    ((-(p : ℂ) - (I * (u : ℂ)) * (t : ℂ)) *
      (-(p : ℂ) + (I*(v : ℂ) + I*(w : ℂ)) * (t : ℂ) +
        ((I*(v : ℂ))*(I*(w : ℂ))) * (h : ℂ))).re =
      p^2 + u*(v+w)*t^2 + v*w*p*h := by
  simp [Complex.mul_re, Complex.mul_im]
  ring

/-- The coefficient is the sum of all three pairwise shift products. -/
lemma cyclic_coefficient (δ : ℝ) (j : Fin 3) :
    let q : Fin 3 → ℝ := fun k => if k = 0 then 1-5*δ else
      if k = 1 then 2*(1+δ) else 3*(1-δ)
    q j * (q (j+1) + q (j+2)) + q (j+1) * q (j+2) = 11-26*δ-δ^2 := by
  fin_cases j <;> norm_num [Fin.ext_iff, Fin.val_add] <;> ring

/-- No conjugation: the expression is the literal `Re(F*G)`. -/
theorem scaled_diagonal {f f' : ℝ → ℝ} {a b : ℝ}
    (hf : Continuous f) (hf' : Continuous f')
    (hd : ∀ x, HasDerivAt f (f' x) x) (ha : f a = 0)
    (δ : ℝ) (j : Fin 3) :
    (∫ x in a..b, (firstKernel (scaledShift δ) j f f' x *
      secondKernel (scaledShift δ) j f f' b x).re) =
      (∫ x in a..b, (f' x)^2) +
      Real.pi^2 * (11-26*δ-δ^2) * (∫ x in a..b, (f x)^2) := by
  let q : Fin 3 → ℝ := fun k => Real.pi *
    (if k = 0 then 1-5*δ else if k = 1 then 2*(1+δ) else 3*(1-δ))
  have hp (x : ℝ) : (firstKernel (scaledShift δ) j f f' x *
      secondKernel (scaledShift δ) j f f' b x).re =
      (f' x)^2 + (q j * (q (j+1) + q (j+2))) * (f x)^2 +
      (q (j+1) * q (j+2)) * (f' x * tail f b x) := by
    simpa only [firstKernel, secondKernel, scaledShift, q, mul_assoc] using
      pure_imaginary_product (q j) (q (j+1)) (q (j+2)) (f' x) (f x) (tail f b x)
  have h1 : IntervalIntegrable (fun x => (f' x)^2) volume a b :=
    (hf'.pow 2).intervalIntegrable a b
  have h2 : IntervalIntegrable (fun x => (q j*(q (j+1)+q (j+2)))*(f x)^2) volume a b :=
    ((hf.pow 2).const_mul (q j * (q (j+1)+q (j+2)))).intervalIntegrable a b
  have h3 : IntervalIntegrable (fun x => (q (j+1)*q (j+2))*(f' x*tail f b x)) volume a b :=
    ((hf'.mul (tail_continuous hf b)).const_mul
    (q (j+1)*q (j+2))).intervalIntegrable a b
  simp_rw [hp]
  rw [intervalIntegral.integral_add (h1.add h2) h3,
    intervalIntegral.integral_add h1 h2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_deriv_tail hf hf' hd ha]
  have hc : q j * (q (j+1)+q (j+2)) + q (j+1)*q (j+2) =
      Real.pi^2 * (11-26*δ-δ^2) := by
    dsimp [q]
    let r : Fin 3 → ℝ := fun k => if k = 0 then 1-5*δ else
      if k = 1 then 2*(1+δ) else 3*(1-δ)
    calc
      _ = Real.pi^2 * (r j * (r (j+1)+r (j+2)) + r (j+1)*r (j+2)) := by
        dsimp [r]; ring
      _ = _ := by rw [cyclic_coefficient δ j]
  linear_combination hc * (∫ x in a..b, (f x)^2)

end ZhangLS.Spec.FixedHDiagonal
