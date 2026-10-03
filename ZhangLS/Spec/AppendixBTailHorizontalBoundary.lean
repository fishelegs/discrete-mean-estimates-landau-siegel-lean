import ZhangLS.Spec.AppendixBTailLeftBoundary

/-! Both genuine horizontal connectors for the complementary Gaussian source
kernel, transferred from the already checked zeta ramp envelopes. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace ZhangLS.Spec
open Complex MeasureTheory Set

lemma appendixB_tail_horizontal_bound {D : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) {L z M : ℝ} (hLP : 0≤L) (hz : 0.5≤z)
    (hM : 0≤M) (β : ℂ) {γ : ℂ} (hγre : γ.re=0)
    (hγ : ‖γ‖≤3*lemma44PaperAlpha D) {l₁ : ℕ} (hl : 0<l₁)
    (hx1 : 1≤Real.exp (0.5*L)/(l₁ : ℝ))
    (hscale : lemma44PaperAlpha D*Real.log (Real.exp (z*L)/(l₁ : ℝ))≤Real.pi)
    (hnum : ∀ s : ℂ, AppendixBContourPoint D s →
      ‖riemannZeta (1+s)/riemannZeta (1+s-β)‖≤M) :
    ‖∫ σ : ℝ in (-1/lemma23PaperL D)..(6*lemma44PaperAlpha D),
      lemma151TailIntegrand D L z β γ l₁ ((σ : ℂ)-I*(appendixBContourHeight D : ℂ))‖+
    ‖∫ σ : ℝ in (-1/lemma23PaperL D)..(6*lemma44PaperAlpha D),
      lemma151TailIntegrand D L z β γ l₁ ((σ : ℂ)+I*(appendixBContourHeight D : ℂ))‖≤
      (6*Real.exp 1*lemma23PaperL D^15)*
        (8*M*Real.exp (6*Real.pi)*(6*lemma44PaperAlpha D+1/lemma23PaperL D)/
          (appendixBContourHeight D)^2) := by
  let x := Real.exp (0.5*L)/(l₁ : ℝ)
  let y := Real.exp (z*L)/(l₁ : ℝ)
  let C := 3*Real.exp 1*lemma23PaperL D^15
  have hLp : 0<lemma23PaperL D := by linarith
  have ha := lemma83_alpha_small (by linarith : 100≤lemma23PaperL D)
  have hx : 0<x := lt_of_lt_of_le zero_lt_one hx1
  have hxy : x≤y := by
    dsimp [x,y]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right hz hLP
  have hy : 0<y := hx.trans_le hxy
  have hy1 : 1≤y := hx1.trans hxy
  have hscalex : lemma44PaperAlpha D*Real.log x≤Real.pi :=
    (mul_le_mul_of_nonneg_left (Real.log_le_log hx hxy) ha.1.le).trans hscale
  have hC : 0≤C := by dsimp [C]; positivity
  have hH1 : 1≤proposition71ZetaAuxHeight D :=
    Real.one_le_exp (Real.rpow_nonneg hLp.le _)
  have hYlow : 1/2≤appendixBContourHeight D := by
    unfold appendixBContourHeight
    linarith
  have hY : 0<appendixBContourHeight D := by linarith
  have hγY : ‖-γ‖≤appendixBContourHeight D/2 := by
    rw [norm_neg]
    linarith [ha.2]
  have hbound (s : ℂ) (hs : AppendixBContourPoint D s)
      (him : |s.im|=appendixBContourHeight D)
      (hre : -1/lemma23PaperL D≤s.re ∧ s.re≤6*lemma44PaperAlpha D) :
      ‖lemma151TailIntegrand D L z β γ l₁ s‖≤
        8*C*M*Real.exp (6*Real.pi)/(appendixBContourHeight D)^2 := by
    have hinv : 1/lemma23PaperL D≤1 := (div_le_one hLp).mpr (by linarith)
    have hsr : |s.re|≤1 := by
      apply abs_le.mpr
      have hlo := hre.1
      rw [neg_div] at hlo
      constructor <;> linarith [hre.2,ha.2]
    have hsg : s≠γ := by
      intro he
      rw [he] at him
      have hi := (Complex.abs_im_le_norm γ).trans hγ
      linarith [ha.2]
    have hfull (q : ℝ) (hq : 1≤q)
        (hqa : lemma44PaperAlpha D*Real.log q≤Real.pi) :
        ‖appendixBZetaIntegrand q β γ s‖≤
          4*M*Real.exp (6*Real.pi)/(appendixBContourHeight D)^2 := by
      have hk := lemma84_horizontal_kernel_bound s (-γ) hY (Real.log_nonneg hq)
        him hγY hre.2 (show (6*lemma44PaperAlpha D)*Real.log q≤6*Real.pi by linarith)
      unfold appendixBZetaIntegrand
      rw [mul_div_assoc,lemma84_positive_cpow_eq_exp (zero_lt_one.trans_le hq),norm_mul]
      exact (mul_le_mul (hnum s hs) (by simpa only [sub_eq_add_neg] using hk)
        (norm_nonneg _) hM).trans_eq (by ring)
    have ht := appendixB_tail_integrand_norm_transfer (by linarith : 1≤lemma23PaperL D)
      L z β hγre hsr hl hsg
    apply ht.trans
    change C*(_+_)≤_
    exact (mul_le_mul_of_nonneg_left (add_le_add (hfull y hy1 hscale) (hfull x hx1 hscalex))
      hC).trans_eq (by ring)
  have hab : -1/lemma23PaperL D≤6*lemma44PaperAlpha D := by
    have hi : 0<1/lemma23PaperL D := by positivity
    rw [neg_div]
    linarith [ha.1]
  have hlo (σ : ℝ) (hσ : σ∈Icc (-1/lemma23PaperL D) (6*lemma44PaperAlpha D)) :
      ‖lemma151TailIntegrand D L z β γ l₁ ((σ : ℂ)-I*(appendixBContourHeight D : ℂ))‖≤
        8*C*M*Real.exp (6*Real.pi)/(appendixBContourHeight D)^2 := by
    have him : |((σ : ℂ)-I*(appendixBContourHeight D : ℂ)).im|=appendixBContourHeight D := by
      simp [abs_of_pos hY]
    exact hbound _ (Or.inr ⟨him,by simpa using hσ.1,by simpa using hσ.2⟩) him
      (by simpa using hσ)
  have hhi (σ : ℝ) (hσ : σ∈Icc (-1/lemma23PaperL D) (6*lemma44PaperAlpha D)) :
      ‖lemma151TailIntegrand D L z β γ l₁ ((σ : ℂ)+I*(appendixBContourHeight D : ℂ))‖≤
        8*C*M*Real.exp (6*Real.pi)/(appendixBContourHeight D)^2 := by
    have him : |((σ : ℂ)+I*(appendixBContourHeight D : ℂ)).im|=appendixBContourHeight D := by
      simp [abs_of_pos hY]
    exact hbound _ (Or.inr ⟨him,by simpa using hσ.1,by simpa using hσ.2⟩) him
      (by simpa using hσ)
  have hh := lemma84_horizontal_integrals_bound (lemma151TailIntegrand D L z β γ l₁) hab
    (show 0≤8*C*M*Real.exp (6*Real.pi)/(appendixBContourHeight D)^2 by positivity) hlo hhi
  exact hh.trans_eq (by dsimp [C]; ring)

end ZhangLS.Spec
