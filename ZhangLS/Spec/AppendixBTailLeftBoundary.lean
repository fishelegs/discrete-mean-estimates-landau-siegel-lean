import ZhangLS.Spec.AppendixBTailMultiplier
import ZhangLS.Spec.AppendixBTailOriginalRange

/-! Integrated genuine left contour bound, uniform in positive l1 and in
z in the source interval. The lower source scale is kept exact. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace ZhangLS.Spec
open Complex MeasureTheory Set

lemma appendixB_log_kernel_mono_negative {b x y : ℝ}
    (hb : b≤0) (hx : 0<x) (hxy : x≤y) (v t : ℝ) :
    ‖lemma84LogKernel b (Real.log y) v t‖≤
      ‖lemma84LogKernel b (Real.log x) v t‖ := by
  simp only [lemma84_log_kernel_norm]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left (Real.log_le_log hx hxy) hb

/-- The sharp lower scale exp(L/2)/l1 is never replaced by exp(L/2). -/
theorem appendixB_tail_left_boundary_bound {D : ℕ} (hL : 1≤lemma23PaperL D)
    {L z M : ℝ} (hLP : 0≤L) (hz : 0.5≤z) (hM : 0≤M)
    (β : ℂ) {γ : ℂ} (hγ : γ.re=0) {l₁ : ℕ} (hl : 0<l₁)
    (hnum : ∀ s : ℂ, AppendixBContourPoint D s →
      ‖riemannZeta (1+s)/riemannZeta (1+s-β)‖≤M) :
    ‖∫ t : ℝ in -appendixBContourHeight D..appendixBContourHeight D,
      lemma151TailIntegrand D L z β γ l₁
        ((-1/lemma23PaperL D : ℝ)+I*(t : ℂ))‖≤
      (6*Real.exp 1*lemma23PaperL D^15)*M*
        Real.exp (-Real.log (Real.exp (0.5*L)/(l₁ : ℝ))/lemma23PaperL D)*
          Real.pi*lemma23PaperL D := by
  let x := Real.exp (0.5*L)/(l₁ : ℝ)
  let y := Real.exp (z*L)/(l₁ : ℝ)
  let C := 3*Real.exp 1*lemma23PaperL D^15
  have hLp : 0<lemma23PaperL D := by linarith
  have hx : 0<x := div_pos (Real.exp_pos _) (Nat.cast_pos.mpr hl)
  have hxy : x≤y := by
    dsimp [x,y]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right hz hLP
  have hy : 0<y := hx.trans_le hxy
  have hb : -1/lemma23PaperL D≤0 := div_nonpos_of_nonpos_of_nonneg (by norm_num) hLp.le
  have hY : 0≤appendixBContourHeight D := by
    unfold appendixBContourHeight
    positivity [proposition71_zeta_aux_height_pos D]
  have hC : 0≤C := by dsimp [C]; positivity
  have hh := lemma84_left_vertical_integral_bound
    (fun t : ℝ => lemma151TailIntegrand D L z β γ l₁
      ((-1/lemma23PaperL D : ℝ)+I*(t : ℂ)))
    (δ := 1/lemma23PaperL D) (H := appendixBContourHeight D) (M := 2*C*M)
    (by positivity) hY (by positivity) (Real.log x) (-γ).im (by
      intro t ht
      let s : ℂ := ((-1/lemma23PaperL D : ℝ)+I*(t : ℂ))
      have hsre : s.re= -1/lemma23PaperL D := by simp [s]
      have hs : AppendixBContourPoint D s :=
        Or.inl ⟨hsre,by simpa [s] using abs_le.mpr ⟨ht.1.le,ht.2⟩⟩
      have habs : |s.re|≤1 := by
        rw [hsre,abs_div,abs_neg,abs_one,abs_of_pos hLp]
        exact (div_le_one hLp).mpr hL
      have hsg : s≠γ := by
        intro he
        have hr := congrArg Complex.re he
        rw [hsre,hγ,neg_div] at hr
        have hi : 0<1/lemma23PaperL D := by positivity
        linarith
      have hf := appendixB_tail_integrand_norm_transfer hL L z β hγ habs hl hsg
      have hfx : ‖appendixBZetaIntegrand x β γ s‖≤
          M*‖lemma84LogKernel (-1/lemma23PaperL D) (Real.log x) (-γ).im t‖ := by
        rw [appendixB_integrand_eq_log_kernel hx β γ hγ,norm_mul]
        exact mul_le_mul_of_nonneg_right (hnum s hs) (norm_nonneg _)
      have hfy : ‖appendixBZetaIntegrand y β γ s‖≤
          M*‖lemma84LogKernel (-1/lemma23PaperL D) (Real.log x) (-γ).im t‖ := by
        rw [appendixB_integrand_eq_log_kernel hy β γ hγ,norm_mul]
        exact mul_le_mul (hnum s hs) (appendixB_log_kernel_mono_negative hb hx hxy _ _)
          (norm_nonneg _) hM
      apply hf.trans
      change C*(_+_)≤_
      have hp := mul_le_mul_of_nonneg_left (add_le_add hfy hfx) hC
      exact hp.trans_eq (by simp only [neg_div]; ring))
  apply hh.trans_eq
  dsimp [C,x]
  field_simp
  <;> ring

/-- The actual auxiliary zeta strip and original source scales discharge the
left-side hypotheses with one threshold before every l1<T and source z. -/
theorem appendixB_actual_tail_left_uniform :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      ∀ β γ : ℂ, β.re=0 → ‖β‖≤3*lemma44PaperAlpha D → γ.re=0 →
      ∀ l₁ : ℕ, 0<l₁ → (l₁ : ℝ)<lemma56PaperT D →
      ∀ z : ℝ, z∈Icc (0.5 : ℝ) 0.504 →
      ‖∫ t : ℝ in -appendixBContourHeight D..appendixBContourHeight D,
        lemma151TailIntegrand D (lemma23PaperL D^9) z β γ l₁
          ((-1/lemma23PaperL D : ℝ)+I*(t : ℂ))‖≤
        (6*Real.exp 1*lemma23PaperL D^15)*appendixBContourMajorant D*
          Real.exp (-(lemma23PaperL D^(1/10 : ℝ)))*Real.pi*lemma23PaperL D := by
  obtain ⟨N,hN,hbound⟩ := appendixB_actual_contour_ratio_bound
  obtain ⟨M,hM⟩ := Filter.eventually_atTop.mp appendixB_source_scales_uniform
  refine ⟨max N M,hN.trans (le_max_left _ _),?_⟩
  intro D hD β γ hβre hβ hγ l₁ hl hlT z hz
  obtain ⟨hL,hboundD⟩ := hbound D ((le_max_left _ _).trans hD)
  have hLp : 0<lemma23PaperL D := by linarith
  have hnum := fun s hs => (hboundD β hβre hβ s hs).2
  have hM0 : 0≤appendixBContourMajorant D := by
    unfold appendixBContourMajorant
    positivity
  have hh := appendixB_tail_left_boundary_bound (by linarith : 1≤lemma23PaperL D)
    (show 0≤lemma23PaperL D^9 by positivity) hz.1 hM0 β hγ hl hnum
  have hscale := (hM D ((le_max_right _ _).trans hD)).2 l₁ hl hlT (0.5 : ℝ)
    (by norm_num : (0.5 : ℝ)∈Icc (0.5 : ℝ) 0.504)
  have he := lemma84_paper_left_exponential hLp hscale.1
  exact hh.trans (by gcongr)

end ZhangLS.Spec
