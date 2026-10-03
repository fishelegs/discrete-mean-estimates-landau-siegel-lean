import ZhangLS.Spec.AppendixBTailGaussianMellin
import ZhangLS.Spec.AppendixBKernelOriginalPhases
import ZhangLS.Spec.AppendixBKernelBoundaryIntegrals
import ZhangLS.Spec.Lemma44MiddleContour

/-! Transfer of the frozen full-ramp contour envelopes to the actual Gaussian
complementary tail. No new first-order contour majorant is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace ZhangLS.Spec
open Complex MeasureTheory

lemma appendixB_linear_gaussian_bound {A : ℝ} (hA : 0<A) (u : ℝ) :
    |u| *Real.exp (-(u^2/(4*A^2)))≤2*A := by
  let y := |u|/(2*A)
  have hy : 0≤y := by dsimp [y]; positivity
  have hyexp : y≤Real.exp (y^2) := by
    have he := Real.add_one_le_exp (y^2)
    nlinarith [sq_nonneg (y-1/2)]
  have hye : y*Real.exp (-(y^2))≤1 := by
    rw [Real.exp_neg,mul_inv_le_iff₀ (Real.exp_pos _)]
    simpa using hyexp
  have he : y^2=u^2/(4*A^2) := by
    dsimp [y]
    rw [div_pow,sq_abs]
    ring
  have hh := mul_le_mul_of_nonneg_left hye (show 0≤2*A by positivity)
  rw [he] at hh
  have hyid : 2*A*y=|u| := by dsimp [y]; field_simp
  rw [←mul_assoc,hyid,mul_one] at hh
  exact hh

/-- A global Gaussian multiplier bound, uniform in Im(s) and gamma.
It costs only L^15, which is absorbed by the frozen exponential contour budget. -/
theorem appendixB_gaussian_multiplier_bound {D : ℕ} (hL : 1≤lemma23PaperL D)
    {s γ : ℂ} (hγ : γ.re=0) (hs : |s.re|≤1) :
    ‖(s-γ)*lemma57OmegaOne D (s-γ)‖≤
      3*Real.exp 1*lemma23PaperL D^15 := by
  let A := lemma23PaperL D^15
  let u := (s-γ).im
  have hA : 1≤A := one_le_pow₀ hL
  have hAp : 0<A := by linarith
  have hnorm : ‖s-γ‖≤1+|u| := by
    have hh := Complex.norm_le_abs_re_add_abs_im (s-γ)
    simp only [sub_re,hγ,sub_zero] at hh
    exact hh.trans (add_le_add hs (le_refl |u|))
  have hz : s-γ=(s.re : ℂ)+(u : ℂ)*I := by
    apply Complex.ext <;> simp [u,hγ]
  have hω : ‖lemma57OmegaOne D (s-γ)‖=
      Real.exp (s.re^2/(4*A^2))*Real.exp (-(u^2/(4*A^2))) := by
    rw [hz,lemma44_Omega_norm_vertical]
    have hpow : lemma23PaperL D^30=A^2 := by dsimp [A]; ring
    rw [hpow,←Real.exp_add]
    congr 1
    ring
  have hexp : Real.exp (s.re^2/(4*A^2))≤Real.exp 1 := by
    apply Real.exp_le_exp.mpr
    apply (div_le_iff₀ (by positivity : 0<4*A^2)).mpr
    have hsq : s.re^2≤1 := by nlinarith [sq_abs s.re,abs_nonneg s.re]
    nlinarith
  have htail : Real.exp (-(u^2/(4*A^2)))≤1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (div_nonneg (sq_nonneg u) (by positivity)))
  have hlin := appendixB_linear_gaussian_bound hAp u
  rw [norm_mul,hω]
  calc
    _ ≤ (1+|u|)*(Real.exp 1*Real.exp (-(u^2/(4*A^2)))) :=
      mul_le_mul hnorm (mul_le_mul_of_nonneg_right hexp (Real.exp_pos _).le)
        (by positivity) (by positivity)
    _ = Real.exp 1*(Real.exp (-(u^2/(4*A^2)))+
        |u| *Real.exp (-(u^2/(4*A^2)))) := by ring
    _ ≤ Real.exp 1*(3*A) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      linarith
    _ = _ := by dsimp [A]; ring

lemma appendixB_source_power_bracket (L z : ℝ) (γ s : ℂ) {l₁ : ℕ} (hl : 0<l₁) :
    exp (γ*((L*(0.504-z) : ℝ) : ℂ))*
        (((Real.exp (z*L)/l₁ : ℝ) : ℂ)^s)-
      exp (γ*((L*0.004 : ℝ) : ℂ))*
        (((Real.exp (0.5*L)/l₁ : ℝ) : ℂ)^s)=
      lemma151TailNumerator L z γ s*exp (-s*(Real.log (l₁ : ℝ) : ℂ)) := by
  have hlr : 0<(l₁ : ℝ) := Nat.cast_pos.mpr hl
  rw [lemma84_positive_cpow_eq_exp (div_pos (Real.exp_pos _) hlr),
    lemma84_positive_cpow_eq_exp (div_pos (Real.exp_pos _) hlr)]
  simp only [Real.log_div (Real.exp_pos _).ne' hlr.ne',Real.log_exp]
  unfold lemma151TailNumerator
  rw [sub_mul,←exp_add,←exp_add,←exp_add,←exp_add]
  apply congrArg₂ (fun a b : ℂ => exp a-exp b)
  all_goals push_cast; ring

/-- Exact algebraic transfer to the already validated genuine full-ramp integrands. -/
lemma appendixB_tail_integrand_full_kernel_factorization (D : ℕ) (L z : ℝ)
    (β γ s : ℂ) {l₁ : ℕ} (hl : 0<l₁) (hsg : s≠γ) :
    lemma151TailIntegrand D L z β γ l₁ s=
      ((s-γ)*lemma57OmegaOne D (s-γ)) *
      (exp (γ*((L*(0.504-z) : ℝ) : ℂ))*
        appendixBZetaIntegrand (Real.exp (z*L)/l₁) β γ s-
       exp (γ*((L*0.004 : ℝ) : ℂ))*
        appendixBZetaIntegrand (Real.exp (0.5*L)/l₁) β γ s) := by
  have hn := appendixB_source_power_bracket L z γ s hl
  unfold lemma151TailIntegrand appendixBZetaIntegrand
  rw [show lemma151TailNumerator L z γ s*riemannZeta (1+s)/riemannZeta (1+s-β)*
      lemma57OmegaOne D (s-γ)*exp (-s*(Real.log (l₁ : ℝ) : ℂ))/(s-γ)=
      (lemma151TailNumerator L z γ s*exp (-s*(Real.log (l₁ : ℝ) : ℂ)))*
      (riemannZeta (1+s)/riemannZeta (1+s-β))*lemma57OmegaOne D (s-γ)/(s-γ) by ring,
    ←hn]
  field_simp [sub_ne_zero.mpr hsg]
  <;> ring

/-- A proved pointwise contour envelope. The only loss relative to two full
ramps is 3 exp(1)L^15; all l1-dependent powers remain genuine. -/
theorem appendixB_tail_integrand_norm_transfer {D : ℕ} (hL : 1≤lemma23PaperL D)
    (L z : ℝ) (β : ℂ) {γ s : ℂ} (hγ : γ.re=0) (hs : |s.re|≤1)
    {l₁ : ℕ} (hl : 0<l₁) (hsg : s≠γ) :
    ‖lemma151TailIntegrand D L z β γ l₁ s‖≤
      (3*Real.exp 1*lemma23PaperL D^15)*
        (‖appendixBZetaIntegrand (Real.exp (z*L)/l₁) β γ s‖+
          ‖appendixBZetaIntegrand (Real.exp (0.5*L)/l₁) β γ s‖) := by
  rw [appendixB_tail_integrand_full_kernel_factorization D L z β γ s hl hsg,norm_mul]
  have hn := norm_sub_le
    (exp (γ*((L*(0.504-z) : ℝ) : ℂ))*appendixBZetaIntegrand (Real.exp (z*L)/l₁) β γ s)
    (exp (γ*((L*0.004 : ℝ) : ℂ))*appendixBZetaIntegrand (Real.exp (0.5*L)/l₁) β γ s)
  simp only [norm_mul,appendixB_imaginary_exp_norm hγ,one_mul] at hn
  exact mul_le_mul (appendixB_gaussian_multiplier_bound hL hγ hs) hn (norm_nonneg _)
    (by positivity)

end ZhangLS.Spec
