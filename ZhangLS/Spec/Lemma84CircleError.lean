import ZhangLS.Spec.Lemma84CircleQuotient
import ZhangLS.Spec.Lemma84Residue
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Metric Set
set_option maxHeartbeats 1000000

/-- An additive arithmetic perturbation estimate. Π may be zero. -/
lemma lemma84_product_error_bound (q v u p : ℂ) {E M δ : ℝ}
    (hE : 0 ≤ E) (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (hq : ‖q-v‖ ≤ E) (hv : ‖v‖ ≤ M) (hu : ‖u-p‖ ≤ δ) :
    ‖q*u-v*p‖ ≤ E*(‖p‖+δ)+M*δ := by
  have hup : ‖u‖ ≤ ‖p‖+δ := by
    have hh : ‖u‖ ≤ ‖u-p‖+‖p‖ := by simpa using norm_add_le (u-p) p
    linarith only [hh,hu]
  rw [show q*u-v*p = (q-v)*u+v*(u-p) by ring]
  apply (norm_add_le _ _).trans
  simp only [norm_mul]
  exact add_le_add (mul_le_mul hq hup (norm_nonneg _) hE)
    (mul_le_mul hv hu (norm_nonneg _) hM)

lemma lemma84_normalized_circle_product_error
    (q v u k : ℂ → ℂ) (p : ℂ) {R E M δ B : ℝ}
    (hR : 0 ≤ R) (hE : 0 ≤ E) (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hB : 0 ≤ B)
    (hq : ∀ s ∈ sphere 0 R, ‖q s-v s‖ ≤ E)
    (hv : ∀ s ∈ sphere 0 R, ‖v s‖ ≤ M)
    (hu : ∀ s ∈ sphere 0 R, ‖u s-p‖ ≤ δ)
    (hk : ∀ s ∈ sphere 0 R, ‖k s‖ ≤ B) :
    ‖(2*Real.pi*I : ℂ)⁻¹ * circleIntegral
      (fun s => (q s*u s-v s*p)*k s) 0 R‖ ≤ R*B*(E*(‖p‖+δ)+M*δ) := by
  have hh := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR
    (f := fun s => (q s*u s-v s*p)*k s) (c := 0)
    (C := B*(E*(‖p‖+δ)+M*δ)) (by
      intro s hs
      rw [norm_mul]
      have hb := lemma84_product_error_bound (q s) (v s) (u s) p hE hM hδ
        (hq s hs) (hv s hs) (hu s hs)
      have hm := mul_le_mul hb (hk s hs) (norm_nonneg _) (by positivity : 0 ≤ E*(‖p‖+δ)+M*δ)
      simpa only [mul_comm] using hm)
  simpa only [smul_eq_mul,mul_assoc] using hh

lemma lemma84_model_ratio_bound (A a b s : ℂ) {α : ℝ}
    (hα : 0 < α) (hs : ‖s‖ = 5*α) (ha : ‖a‖ ≤ 3*α) (hb : ‖b‖ ≤ 3*α) :
    ‖A*(s+a)*(s+b)/s‖ ≤ 13*‖A‖*α := by
  have hsa : ‖s+a‖ ≤ 8*α := (norm_add_le _ _).trans (by linarith)
  have hsb : ‖s+b‖ ≤ 8*α := (norm_add_le _ _).trans (by linarith)
  rw [norm_div,norm_mul,norm_mul,hs]
  apply (div_le_iff₀ (by positivity : 0 < 5*α)).mpr
  have hp := mul_le_mul hsa hsb (norm_nonneg _) (by positivity : 0 ≤ 8*α)
  have hh := mul_le_mul_of_nonneg_left hp (norm_nonneg A)
  nlinarith only [hh,mul_nonneg (norm_nonneg A) (sq_nonneg α)]

lemma lemma84_circle_kernel_bound (s m : ℂ) {α ℓ H : ℝ}
    (hα : 0 < α) (hℓ : 0 ≤ ℓ) (hH : α*ℓ ≤ H)
    (hs : ‖s‖ = 5*α) (hm : ‖m‖ ≤ 3*α) :
    ‖exp (s*(ℓ:ℂ))/(s+m)^2‖ ≤ Real.exp (5*H)/(4*α^2) := by
  have hlow : 2*α ≤ ‖s+m‖ := by
    have hh := norm_sub_norm_le s (-m)
    simp only [norm_neg,sub_neg_eq_add] at hh
    linarith only [hh,hm,hs]
  have hsq : 4*α^2 ≤ ‖s+m‖^2 := by nlinarith only [sq_le_sq₀ (by positivity : 0 ≤ 2*α) (norm_nonneg (s+m)) |>.mpr hlow]
  have hexp : ‖exp (s*(ℓ:ℂ))‖ ≤ Real.exp (5*H) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    have hre : s.re ≤ 5*α := (Complex.re_le_norm s).trans_eq hs
    nlinarith only [mul_le_mul_of_nonneg_right hre hℓ,hH]
  rw [norm_div,norm_pow]
  exact div_le_div₀ (by positivity) hexp (by positivity) hsq

/-- Quantitative circle error retaining the Π factor. This theorem does not
silently absorb a polylogarithmic factor into the paper's L⁻⁶ target. -/
lemma lemma84_actual_circle_error_with_pi {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hDN : lemma57ExplicitModulusThreshold ≤ D) (hA : NormalizedAssumptionA χ)
    (hC : lemma58ErrorConstant ≤ lemma23PaperL D)
    (a b m p : ℂ) (U : ℂ → ℂ) (δ ℓ H : ℝ)
    (ha : ‖a‖ ≤ 3*lemma44PaperAlpha D) (hb : ‖b‖ ≤ 3*lemma44PaperAlpha D)
    (hm : ‖m‖ ≤ 3*lemma44PaperAlpha D) (hδ : 0 ≤ δ) (hℓ : 0 ≤ ℓ)
    (hscale : lemma44PaperAlpha D*ℓ ≤ H)
    (hU : ∀ s ∈ sphere 0 (5*lemma44PaperAlpha D), ‖U s-p‖ ≤ δ) :
    ‖(2*Real.pi*I : ℂ)⁻¹ * circleIntegral (fun s =>
      (dirichletLFunction χ (1+s+a)*dirichletLFunction χ (1+s+b)/dirichletLFunction χ (1+s)*U s -
        (LDerivAtOne χ*(s+a)*(s+b)/s)*p) * exp (s*(ℓ:ℂ))/(s+m)^2)
      0 (5*lemma44PaperAlpha D)‖ ≤
        (5*lemma44PaperAlpha D)*(Real.exp (5*H)/(4*lemma44PaperAlpha D^2))*
          ((8*lemma58ErrorConstant)*lemma23PaperL D^(-15 : ℤ)*(‖p‖+δ) +
            (13*‖LDerivAtOne χ‖*lemma44PaperAlpha D)*δ) := by
  have hL : 100 ≤ lemma23PaperL D := by
    change 100 ≤ Real.log (D:ℝ)
    linarith [lemma57_log_ge_ten_million hDN]
  have hα := (lemma83_alpha_small hL).1
  have hLp : 0 < lemma23PaperL D := by linarith
  have hh := lemma84_normalized_circle_product_error
    (fun s => dirichletLFunction χ (1+s+a)*dirichletLFunction χ (1+s+b)/dirichletLFunction χ (1+s))
    (fun s => LDerivAtOne χ*(s+a)*(s+b)/s) U
    (fun s => exp (s*(ℓ:ℂ))/(s+m)^2) p
    (R := 5*lemma44PaperAlpha D) (E := (8*lemma58ErrorConstant)*lemma23PaperL D^(-15 : ℤ))
    (M := 13*‖LDerivAtOne χ‖*lemma44PaperAlpha D) (δ := δ)
    (B := Real.exp (5*H)/(4*lemma44PaperAlpha D^2))
    (by positivity) (by positivity [lemma58_error_constant_pos]) (by positivity) hδ (by positivity)
    (fun s hs => lemma84_actual_circle_quotient χ hDN hA hC a b s ha hb
      (by simpa using mem_sphere_iff_norm.mp hs))
    (fun s hs => lemma84_model_ratio_bound _ a b s hα
      (by simpa using mem_sphere_iff_norm.mp hs) ha hb) hU
    (fun s hs => lemma84_circle_kernel_bound s m hα hℓ hscale
      (by simpa using mem_sphere_iff_norm.mp hs) hm)
  simpa only [mul_div_assoc] using hh

end ZhangLS.Spec
