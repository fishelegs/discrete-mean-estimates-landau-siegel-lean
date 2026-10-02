import ZhangLS.Spec.Lemma102Definitions
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Metric
set_option maxHeartbeats 2000000

lemma lemma102_exponential_triple_circle (ℓ : ℂ) {R : ℝ} (hR : 0<R) :
    (2*Real.pi*I:ℂ)⁻¹ * circleIntegral (fun s : ℂ => exp (s*ℓ)/s^3) 0 R = ℓ^2/2 := by
  have hd : Differentiable ℂ (fun s : ℂ => exp (ℓ*s)) := by fun_prop
  have hh := hd.differentiableOn.circleIntegral_one_div_sub_center_pow_smul hR 2
    (c := (0:ℂ))
  rw [iteratedDeriv_cexp_const_mul] at hh
  norm_num [smul_eq_mul,div_eq_mul_inv,mul_comm] at hh
  have he : circleIntegral (fun s : ℂ => exp (s*ℓ)/s^3) 0 R =
      (2*Real.pi*I:ℂ)/2*ℓ^2 := by
    calc
      _ = circleIntegral (fun s : ℂ => exp (ℓ*s)*(s^3)⁻¹) 0 R := by
        apply circleIntegral.integral_congr hR.le
        intro s _
        simp only [div_eq_mul_inv,mul_comm s ℓ]
      _ = _ := hh.trans (by ring)
  rw [he]
  field_simp

/-- The third-order pole at the unshifted origin is evaluated by Cauchy's
higher derivative formula, rather than by the shifted G formula. -/
lemma lemma102_model_circle_integral (a b ℓ : ℂ) {R : ℝ} (hR : 0<R) :
    (2*Real.pi*I:ℂ)⁻¹ *
      circleIntegral (fun s : ℂ => (s+a)*(s+b)/s*exp (s*ℓ)/s^2) 0 R =
        1+(a+b)*ℓ+a*b/2*ℓ^2 := by
  let f : ℂ → ℂ := fun s => exp (s*ℓ)/s
  let g : ℂ → ℂ := fun s => exp (s*ℓ)/s^2
  let h : ℂ → ℂ := fun s => exp (s*ℓ)/s^3
  have hf : CircleIntegrable f 0 R := by
    simpa [f,zpow_neg,div_eq_mul_inv,mul_comm] using
      lemma84_exponential_pole_circleIntegrable ℓ 0 (by simpa using hR) 1
  have hg : CircleIntegrable g 0 R := by
    simpa [g,zpow_neg,div_eq_mul_inv,mul_comm] using
      lemma84_exponential_pole_circleIntegrable ℓ 0 (by simpa using hR) 2
  have hh : CircleIntegrable h 0 R := by
    simpa [h,zpow_neg,div_eq_mul_inv,mul_comm] using
      lemma84_exponential_pole_circleIntegrable ℓ 0 (by simpa using hR) 3
  have hid : circleIntegral (fun s : ℂ => (s+a)*(s+b)/s*exp (s*ℓ)/s^2) 0 R =
      circleIntegral (fun s => f s+(a+b)*g s+(a*b)*h s) 0 R := by
    apply circleIntegral.integral_congr hR.le
    intro s hs
    have hs0 : s≠0 := by
      intro he
      have heq := mem_sphere_iff_norm.mp hs
      simp [he] at heq
      linarith
    dsimp [f,g,h]
    field_simp
    ring
  have hBg : CircleIntegrable (fun s => (a+b)*g s) 0 R := hg.const_mul (a+b)
  have hCh : CircleIntegrable (fun s => (a*b)*h s) 0 R := hh.const_mul (a*b)
  have hAB : CircleIntegrable (fun s => f s+(a+b)*g s) 0 R := hf.add hBg
  rw [hid,circleIntegral.integral_add hAB hCh,
    circleIntegral.integral_add hf hBg]
  simp only [circleIntegral.integral_const_mul]
  have hvf : (2*Real.pi*I:ℂ)⁻¹*circleIntegral f 0 R=1 := by
    simpa [f] using lemma84_exponential_simple_circle ℓ 0 (by simpa using hR)
  have hvg : (2*Real.pi*I:ℂ)⁻¹*circleIntegral g 0 R=ℓ := by
    simpa [g] using lemma84_exponential_double_circle ℓ 0 (by simpa using hR)
  have hvh : (2*Real.pi*I:ℂ)⁻¹*circleIntegral h 0 R=ℓ^2/2 :=
    lemma102_exponential_triple_circle ℓ hR
  calc
    _ = (2*Real.pi*I:ℂ)⁻¹*circleIntegral f 0 R +
      (a+b)*((2*Real.pi*I:ℂ)⁻¹*circleIntegral g 0 R)+
      (a*b)*((2*Real.pi*I:ℂ)⁻¹*circleIntegral h 0 R) := by ring
    _ = _ := by rw [hvf,hvg,hvh]; ring

end ZhangLS.Spec
