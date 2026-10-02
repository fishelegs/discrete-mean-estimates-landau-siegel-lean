import ZhangLS.Spec.Lemma84Definitions
import Mathlib.Analysis.Complex.RemovableSingularity
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Metric Set
set_option maxHeartbeats 1000000

lemma lemma84_partial_fractions (a b m s : ℂ) (hm : m ≠ 0)
    (hs : s ≠ 0) (hsm : s+m ≠ 0) :
    (s+a)*(s+b)/s/(s+m)^2 =
      (a*b/m^2)/s + (1-a*b/m^2)/(s+m) - ((a-m)*(b-m)/m)/(s+m)^2 := by
  field_simp
  <;> ring

lemma lemma84_exponential_pole_circleIntegrable (ℓ w : ℂ) {R : ℝ}
    (hw : ‖w‖ < R) (n : ℕ) :
    CircleIntegrable (fun s : ℂ => (s-w)^(-(n:ℤ))*exp (s*ℓ)) 0 R := by
  have hR : 0 < R := (norm_nonneg _).trans_lt hw
  apply ContinuousOn.circleIntegrable hR.le
  apply ContinuousOn.mul _ (by fun_prop)
  apply ContinuousOn.zpow₀ (by fun_prop)
  intro s hs
  have hns : s ≠ w := Metric.sphere_disjoint_ball.ne_of_mem hs
    (by simpa only [mem_ball,dist_zero_right] using hw)
  exact Or.inl (sub_ne_zero.mpr hns)

lemma lemma84_exponential_simple_circle (ℓ w : ℂ) {R : ℝ} (hw : ‖w‖ < R) :
    (2*Real.pi*I : ℂ)⁻¹*circleIntegral (fun s : ℂ => exp (s*ℓ)/(s-w)) 0 R =
      exp (w*ℓ) := by
  have hd : Differentiable ℂ (fun s : ℂ => exp (s*ℓ)) := by fun_prop
  have hh := hd.diffContOnCl.two_pi_i_inv_smul_circleIntegral_sub_inv_smul
    (c := 0) (R := R) (w := w) (by simpa using hw)
  simpa only [smul_eq_mul,div_eq_mul_inv,mul_comm] using hh

lemma lemma84_exponential_double_circle (ℓ w : ℂ) {R : ℝ} (hw : ‖w‖ < R) :
    (2*Real.pi*I : ℂ)⁻¹*circleIntegral (fun s : ℂ => exp (s*ℓ)/(s-w)^2) 0 R =
      ℓ*exp (w*ℓ) := by
  have hd : Differentiable ℂ (fun s : ℂ => exp (s*ℓ)) := by fun_prop
  have hh := Complex.two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable
    isOpen_univ (c := 0) (R := R) (f := fun s : ℂ => exp (s*ℓ)) (w₀ := w)
    (subset_univ _) hd.differentiableOn (by simpa using hw)
  have hder : HasDerivAt (fun s : ℂ => exp (s*ℓ)) (ℓ*exp (w*ℓ)) w := by
    simpa [mul_comm] using ((hasDerivAt_id w).mul_const ℓ).cexp
  rw [hder.deriv] at hh
  simpa only [smul_eq_mul,div_eq_mul_inv,mul_comm] using hh

/-- The actual two-pole circle integral, evaluated with no residue oracle. -/
lemma lemma84_model_circle_integral (a b m ℓ : ℂ) {R : ℝ}
    (hm : m ≠ 0) (hmR : ‖m‖ < R) :
    (2*Real.pi*I : ℂ)⁻¹ *
      circleIntegral (fun s : ℂ => (s+a)*(s+b)/s*exp (s*ℓ)/(s+m)^2) 0 R =
      a*b/m^2 + (1-a*b/m^2-(a-m)*(b-m)/m*ℓ)*exp (-m*ℓ) := by
  let A := a*b/m^2
  let B := 1-a*b/m^2
  let C := -((a-m)*(b-m)/m)
  let f : ℂ → ℂ := fun s => exp (s*ℓ)/s
  let g : ℂ → ℂ := fun s => exp (s*ℓ)/(s+m)
  let h : ℂ → ℂ := fun s => exp (s*ℓ)/(s+m)^2
  have hR : 0 < R := (norm_nonneg _).trans_lt hmR
  have hf : CircleIntegrable f 0 R := by
    simpa [f,zpow_neg,div_eq_mul_inv,mul_comm] using
      lemma84_exponential_pole_circleIntegrable ℓ 0 (by simpa using hR) 1
  have hg : CircleIntegrable g 0 R := by
    simpa [g,zpow_neg,div_eq_mul_inv,mul_comm] using
      lemma84_exponential_pole_circleIntegrable ℓ (-m) (by simpa using hmR) 1
  have hh : CircleIntegrable h 0 R := by
    simpa [h,zpow_neg,div_eq_mul_inv,mul_comm] using
      lemma84_exponential_pole_circleIntegrable ℓ (-m) (by simpa using hmR) 2
  have hid : circleIntegral (fun s : ℂ => (s+a)*(s+b)/s*exp (s*ℓ)/(s+m)^2) 0 R =
      circleIntegral (fun s : ℂ => A*f s+B*g s+C*h s) 0 R := by
    apply circleIntegral.integral_congr hR.le
    intro s hs
    have hsn : ‖s‖ = R := by simpa using mem_sphere_iff_norm.mp hs
    have hs0 : s ≠ 0 := by intro h; rw [h,norm_zero] at hsn; linarith
    have hsm : s+m ≠ 0 := by
      intro he
      have heq : s = -m := eq_neg_of_add_eq_zero_left he
      rw [heq,norm_neg] at hsn
      linarith
    have hp := lemma84_partial_fractions a b m s hm hs0 hsm
    dsimp [A,B,C,f,g,h]
    calc
      _ = ((s+a)*(s+b)/s/(s+m)^2)*exp (s*ℓ) := by ring
      _ = _ := by rw [hp]; ring
  have hAf : CircleIntegrable (fun z => A*f z) 0 R := hf.const_mul A
  have hBg : CircleIntegrable (fun z => B*g z) 0 R := hg.const_mul B
  have hCh : CircleIntegrable (fun z => C*h z) 0 R := hh.const_mul C
  have hAB : CircleIntegrable (fun z => A*f z+B*g z) 0 R := hAf.add hBg
  rw [hid,circleIntegral.integral_add hAB hCh, circleIntegral.integral_add hAf hBg]
  simp only [circleIntegral.integral_const_mul]
  have hfval := lemma84_exponential_simple_circle ℓ 0 (by simpa using hR)
  have hgval := lemma84_exponential_simple_circle ℓ (-m) (by simpa using hmR)
  have hhval := lemma84_exponential_double_circle ℓ (-m) (by simpa using hmR)
  simp only [sub_zero,zero_mul,exp_zero,sub_neg_eq_add] at hfval hgval hhval
  change (2*Real.pi*I : ℂ)⁻¹*(A*circleIntegral f 0 R+B*circleIntegral g 0 R+C*circleIntegral h 0 R) = _
  calc
    _ = A*((2*Real.pi*I : ℂ)⁻¹*circleIntegral f 0 R) +
        B*((2*Real.pi*I : ℂ)⁻¹*circleIntegral g 0 R) +
        C*((2*Real.pi*I : ℂ)⁻¹*circleIntegral h 0 R) := by ring
    _ = A*1+B*exp (-m*ℓ)+C*(ℓ*exp (-m*ℓ)) := by rw [hfval,hgval,hhval]
    _ = _ := by dsimp [A,B,C]; ring

end ZhangLS.Spec
