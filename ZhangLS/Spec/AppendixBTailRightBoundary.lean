import ZhangLS.Spec.AppendixBTailMultiplier

/-! Standard right-line parametrization and the genuine infinite right tails
of the original complementary Gaussian source integrand. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace ZhangLS.Spec
open Complex MeasureTheory Set

lemma appendixB_source_standard_line_mellin {D : ℕ} (hD : 1<D)
    (L z : ℝ) {b : ℝ} (hb : 0<b) {β γ : ℂ}
    (hβ : β.re=0) (hγ : γ.re=0) {l₁ : ℕ} (hl : 0<l₁) :
    Integrable (fun t : ℝ => lemma151TailIntegrand D L z β γ l₁
      ((b : ℂ)+I*(t : ℂ))) ∧
    (2*(Real.pi : ℂ)*I)⁻¹*(∫ t : ℝ,
      lemma151TailIntegrand D L z β γ l₁ ((b : ℂ)+I*(t : ℂ))*I)=
        appendixBSourceGaussianSlice D L z β γ l₁ := by
  have hs := appendixB_source_gaussian_slice_mellin hD L z hb hβ hγ hl
  have he (t : ℝ) : γ+((b : ℂ)+((t+(-γ.im) : ℝ) : ℂ)*I)=
      (b : ℂ)+I*(t : ℂ) := by
    apply Complex.ext <;> simp [hγ] <;> ring
  have hi := hs.1.comp_add_right (-γ.im)
  constructor
  · apply hi.congr
    filter_upwards [] with t
    rw [he]
  · have ht := integral_add_right_eq_self (μ := (volume : Measure ℝ)) (fun t : ℝ =>
      lemma151TailIntegrand D L z β γ l₁ (γ+((b : ℂ)+(t : ℂ)*I))*I) (-γ.im)
    simp_rw [he] at ht
    rw [ht]
    exact hs.2

lemma appendixB_log_kernel_mono_positive {b x y : ℝ}
    (hb : 0≤b) (hx : 0<x) (hxy : x≤y) (v t : ℝ) :
    ‖lemma84LogKernel b (Real.log x) v t‖≤
      ‖lemma84LogKernel b (Real.log y) v t‖ := by
  simp only [lemma84_log_kernel_norm]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left (Real.log_le_log hx hxy) hb

/-- The actual Gaussian source right tails, including their honest integrability.
Both source powers retain l1. The constant is twice the checked multiplier
bound times the frozen full-ramp right-tail budget. -/
theorem appendixB_tail_right_tails {D : ℕ} (hD : 1<D)
    (hL : 1≤lemma23PaperL D) {L z b Y : ℝ} (hLP : 0≤L) (hz : 0.5≤z)
    (hb : 0<b) (hb1 : b≤1) (hY : 0<Y) {β γ : ℂ}
    (hβ : β.re=0) (hγ : γ.re=0) (hγY : |γ.im|≤Y/2)
    {l₁ : ℕ} (hl : 0<l₁) :
    let f := fun t : ℝ => lemma151TailIntegrand D L z β γ l₁ ((b : ℂ)+I*(t : ℂ))
    ‖∫ t : ℝ in Ioi Y, f t‖+‖∫ t : ℝ in Iic (-Y), f t‖≤
      16*(3*Real.exp 1*lemma23PaperL D^15)*(2+1/b)^2*
        Real.exp (b*Real.log (Real.exp (z*L)/(l₁ : ℝ)))/Y := by
  dsimp only
  let x := Real.exp (0.5*L)/(l₁ : ℝ)
  let y := Real.exp (z*L)/(l₁ : ℝ)
  let C := 3*Real.exp 1*lemma23PaperL D^15
  let M := (2+1/b)^2
  let f := fun t : ℝ => lemma151TailIntegrand D L z β γ l₁ ((b : ℂ)+I*(t : ℂ))
  let K := lemma84LogKernel b (Real.log y) (-γ).im
  have hC : 0≤C := by dsimp [C]; positivity
  have hM : 0≤M := sq_nonneg _
  have hx : 0<x := div_pos (Real.exp_pos _) (Nat.cast_pos.mpr hl)
  have hxy : x≤y := by
    dsimp [x,y]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right hz hLP
  have hy : 0<y := hx.trans_le hxy
  have hfi : Integrable f := (appendixB_source_standard_line_mellin hD L z hb hβ hγ hl).1
  have hKi : Integrable K := lemma84_log_kernel_integrable hb _ _
  have hpoint (t : ℝ) : ‖f t‖≤(2*C*M)*‖K t‖ := by
    let s : ℂ := (b : ℂ)+I*(t : ℂ)
    have hs : |s.re|≤1 := by simpa [s,abs_of_pos hb] using hb1
    have hsg : s≠γ := by
      intro he
      have hr := congrArg Complex.re he
      simp [s,hγ] at hr
      linarith
    have ht := appendixB_tail_integrand_norm_transfer hL L z β hγ hs hl hsg
    have hnum : ‖riemannZeta (1+s)/riemannZeta (1+s-β)‖≤M :=
      appendixB_right_ratio_bound hb hβ t
    have hfx : ‖appendixBZetaIntegrand x β γ s‖≤M*‖K t‖ := by
      rw [appendixB_integrand_eq_log_kernel hx β γ hγ,norm_mul]
      exact mul_le_mul hnum (appendixB_log_kernel_mono_positive hb.le hx hxy _ _)
        (norm_nonneg _) hM
    have hfy : ‖appendixBZetaIntegrand y β γ s‖≤M*‖K t‖ := by
      rw [appendixB_integrand_eq_log_kernel hy β γ hγ,norm_mul]
      exact mul_le_mul_of_nonneg_right hnum (norm_nonneg _)
    apply ht.trans
    change C*(_+_)≤_
    exact (mul_le_mul_of_nonneg_left (add_le_add hfy hfx) hC).trans_eq (by ring)
  have hbound (S : Set ℝ) (hS : MeasurableSet S) :
      ‖∫ t : ℝ in S, f t‖≤(2*C*M)*(∫ t : ℝ in S, ‖K t‖) := by
    apply (norm_integral_le_integral_norm _).trans
    have hh := setIntegral_mono_on hfi.norm.integrableOn
      (hKi.norm.const_mul (2*C*M)).integrableOn hS (fun t _ => hpoint t)
    simpa only [integral_const_mul] using hh
  have hm : |(-γ).im|≤Y/2 := by simpa using hγY
  have hu := (hbound (Ioi Y) measurableSet_Ioi).trans
    (mul_le_mul_of_nonneg_left (lemma84_log_kernel_positive_tail hb hY (Real.log y) _ hm)
      (show 0≤2*C*M by positivity))
  have hlower := (hbound (Iic (-Y)) measurableSet_Iic).trans
    (mul_le_mul_of_nonneg_left (lemma84_log_kernel_negative_tail hb hY (Real.log y) _ hm)
      (show 0≤2*C*M by positivity))
  exact (add_le_add hu hlower).trans_eq (by dsimp [C,M,y]; ring)

end ZhangLS.Spec
