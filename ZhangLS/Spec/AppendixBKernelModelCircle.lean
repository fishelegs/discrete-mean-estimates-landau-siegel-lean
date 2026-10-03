import ZhangLS.Spec.AppendixBKernelPerronBridge
import ZhangLS.Spec.Lemma84Residue

/-! Exact evaluation of Appendix B's rational model on the actual circle.
This calculation is independent of the zeta approximation. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace ZhangLS.Spec
open Complex Metric Set

noncomputable def appendixBModelLeading (X x : ℝ) (β γ : ℂ) : ℂ :=
  (((x : ℂ)^γ)*((1-β/γ)*(Real.log x : ℂ)+β/γ^2)-β/γ^2)/(Real.log X : ℂ)

lemma appendixB_model_partial_fractions {β γ s : ℂ}
    (hγ : γ≠0) (hs : s≠0) (hsg : s≠γ) :
    (s-β)/s/(s-γ)^2 = (-β/γ^2)/s+(β/γ^2)/(s-γ)+(1-β/γ)/(s-γ)^2 := by
  field_simp [hγ,hs,sub_ne_zero.mpr hsg]
  <;> ring

/-- Proven residue sum at the actual simple and double poles; no numerical
finite-D approximation enters this identity. -/
theorem appendixB_model_circle_integral (β γ ℓ : ℂ) {R : ℝ}
    (hγ : γ≠0) (hγR : ‖γ‖<R) :
    (2*Real.pi*I : ℂ)⁻¹*circleIntegral
      (fun s : ℂ => (s-β)/s*exp (s*ℓ)/(s-γ)^2) 0 R =
        exp (γ*ℓ)*((1-β/γ)*ℓ+β/γ^2)-β/γ^2 := by
  let A := -β/γ^2
  let B := β/γ^2
  let C := 1-β/γ
  let f : ℂ → ℂ := fun s => exp (s*ℓ)/s
  let g : ℂ → ℂ := fun s => exp (s*ℓ)/(s-γ)
  let h : ℂ → ℂ := fun s => exp (s*ℓ)/(s-γ)^2
  have hR : 0<R := (norm_nonneg _).trans_lt hγR
  have hf : CircleIntegrable f 0 R := by
    simpa [f,zpow_neg,div_eq_mul_inv,mul_comm] using
      lemma84_exponential_pole_circleIntegrable ℓ 0 (by simpa using hR) 1
  have hg : CircleIntegrable g 0 R := by
    simpa [g,zpow_neg,div_eq_mul_inv,mul_comm] using
      lemma84_exponential_pole_circleIntegrable ℓ γ hγR 1
  have hh : CircleIntegrable h 0 R := by
    simpa [h,zpow_neg,div_eq_mul_inv,mul_comm] using
      lemma84_exponential_pole_circleIntegrable ℓ γ hγR 2
  have he : circleIntegral (fun s : ℂ => (s-β)/s*exp (s*ℓ)/(s-γ)^2) 0 R =
      circleIntegral (fun s => A*f s+B*g s+C*h s) 0 R := by
    apply circleIntegral.integral_congr hR.le
    intro s hs
    have hn : ‖s‖=R := by simpa using mem_sphere_iff_norm.mp hs
    have hs0 : s≠0 := by intro e; rw [e,norm_zero] at hn; linarith
    have hsg : s≠γ := by intro e; rw [e] at hn; linarith
    have hp := appendixB_model_partial_fractions (β := β) hγ hs0 hsg
    dsimp [A,B,C,f,g,h]
    calc
      _ = ((s-β)/s/(s-γ)^2)*exp (s*ℓ) := by ring
      _ = _ := by rw [hp]; ring
  have hAf : CircleIntegrable (fun z => A*f z) 0 R := hf.const_mul A
  have hBg : CircleIntegrable (fun z => B*g z) 0 R := hg.const_mul B
  have hCh : CircleIntegrable (fun z => C*h z) 0 R := hh.const_mul C
  have hAB : CircleIntegrable (fun z => A*f z+B*g z) 0 R := hAf.add hBg
  rw [he,circleIntegral.integral_add hAB hCh,
    circleIntegral.integral_add hAf hBg]
  simp only [circleIntegral.integral_const_mul]
  have hfval := lemma84_exponential_simple_circle ℓ 0 (by simpa using hR)
  have hgval := lemma84_exponential_simple_circle ℓ γ hγR
  have hhval := lemma84_exponential_double_circle ℓ γ hγR
  simp only [sub_zero,zero_mul,exp_zero] at hfval
  change (2*Real.pi*I : ℂ)⁻¹*(A*circleIntegral f 0 R+B*circleIntegral g 0 R+C*circleIntegral h 0 R)=_
  calc
    _ = A*((2*Real.pi*I : ℂ)⁻¹*circleIntegral f 0 R)+
        B*((2*Real.pi*I : ℂ)⁻¹*circleIntegral g 0 R)+
        C*((2*Real.pi*I : ℂ)⁻¹*circleIntegral h 0 R) := by ring
    _ = A*1+B*exp (γ*ℓ)+C*(ℓ*exp (γ*ℓ)) := by rw [hfval,hgval,hhval]
    _ = _ := by dsimp [A,B,C]; ring

lemma appendixB_model_circle_eq_leading (X : ℝ) {x : ℝ} (hx : 0<x)
    (β γ : ℂ) {R : ℝ} (hγ : γ≠0) (hγR : ‖γ‖<R) :
    ((2*Real.pi*I : ℂ)⁻¹*circleIntegral
      (fun s : ℂ => (s-β)/s*(x : ℂ)^s/(s-γ)^2) 0 R)/(Real.log X : ℂ) =
        appendixBModelLeading X x β γ := by
  simp_rw [lemma84_positive_cpow_eq_exp hx]
  rw [appendixB_model_circle_integral β γ (Real.log x : ℂ) hγ hγR]
  simp [appendixBModelLeading,lemma84_positive_cpow_eq_exp hx]

end ZhangLS.Spec
