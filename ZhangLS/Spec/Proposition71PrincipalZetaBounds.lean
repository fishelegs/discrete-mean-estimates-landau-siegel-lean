import ZhangLS.Spec.Proposition71PrincipalShortGeometry
import ZhangLS.Spec.Proposition71ZetaRightAnchor
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Set
open scoped Classical
set_option maxHeartbeats 2500000

/-- A uniform all-height right-line bound for the actual three-shift zeta
quotient, on Re(s)=1+α with the original α. -/
lemma proposition71_principal_zeta_right_bound {D : ℕ} (hL : 3≤lemma23PaperL D)
    (β : Fin 3 → ℂ) (hβ : ∀j, (β j).re=0) {s : ℂ}
    (hs : s.re=1+lemma44PaperAlpha D) :
    ‖riemannZeta (s+β 0)*riemannZeta (s+β 1)*riemannZeta (s+β 2)/riemannZeta s‖≤
      81*lemma23PaperL D^36 := by
  have hL0 : 0≤lemma23PaperL D := by linarith
  have hα := proposition71_zeta_paper_alpha_budget hL
  have hs1 : 1<s.re := by rw [hs]; linarith [hα.1]
  have hb (j : Fin 3) : ‖riemannZeta (s+β j)‖≤3*lemma23PaperL D^9 := by
    have hz := (proposition71_zeta_right_half_bounds (s := s+β j) (by simpa [hβ j] using hs1)).1
    have hre : (s+β j).re-1=lemma44PaperAlpha D := by simp [hs,hβ j]
    rw [hre] at hz
    exact hz.trans hα.2.2.1
  have hi : ‖(riemannZeta s)⁻¹‖≤3*lemma23PaperL D^9 := by
    have hz := (proposition71_zeta_right_half_bounds hs1).2
    rw [hs,add_sub_cancel_left] at hz
    exact hz.trans hα.2.2.1
  rw [div_eq_mul_inv,norm_mul,norm_mul,norm_mul]
  calc
    _≤(3*lemma23PaperL D^9)*(3*lemma23PaperL D^9)*(3*lemma23PaperL D^9)*(3*lemma23PaperL D^9) := by
      gcongr <;> first | exact hb 0 | exact hb 1 | exact hb 2
    _=_ := by ring

/-- The actual closed-strip δ estimate in Cauchy-frequency form. Unlike the
line-one eighth-order estimate, this is valid on every shifted edge. -/
lemma proposition71_principal_delta_cauchy_bound {D : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) {s : ℂ} (hs : 1/2≤s.re) (hs2 : s.re≤2) :
    ‖lemma54PaperDeltaMellin D s‖≤
      4*lemma54MellinStripConstant*lemma23PaperL D^3200/(1+s.im^2) := by
  have hb := lemma54_actual_mellin_closed_strip_bound hD hL hs hs2
  rw [Real.rpow_ofNat] at hb
  have hnorm : ‖s‖^2=s.re^2+s.im^2 := by rw [Complex.sq_norm,Complex.normSq_apply]; ring
  have hn : 0<‖s‖^2 := by rw [hnorm]; nlinarith [sq_nonneg s.im]
  have hden : 1+s.im^2≤4*‖s‖^2 := by rw [hnorm]; nlinarith [sq_nonneg s.im]
  have hC : 0≤lemma54MellinStripConstant*lemma23PaperL D^3200 := by
    have hh := lemma54_mellin_strip_constant_pos
    positivity
  apply hb.trans
  apply (div_le_div_iff₀ hn (by positivity : 0<1+s.im^2)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hden hC]

/-- All shifted numerator factors and the actual denominator are controlled
on the H/2 rectangle whenever the displayed pole separation holds. -/
theorem proposition71_principal_zeta_short_rectangle_bound :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D → 2000≤lemma23PaperL D →
      ∀ c : ℝ, 0<c → c*lemma44PaperAlpha D*lemma23PaperL D≤1/10 →
      ∀ s : ℂ, s∈Icc (1-1/lemma23PaperL D) (1+lemma44PaperAlpha D) ×ℂ
        Icc (-proposition71ZetaAuxHeight D/2) (proposition71ZetaAuxHeight D/2) →
      s≠1 → (∀j : Fin 3, 1/lemma23PaperL D≤‖s+lemma83PaperBeta D c j-1‖) →
      ‖riemannZeta (s+lemma83PaperBeta D c 0)*riemannZeta (s+lemma83PaperBeta D c 1)*
        riemannZeta (s+lemma83PaperBeta D c 2)/riemannZeta s‖≤
      (9*Real.exp 1)^4*lemma23PaperL D^44 := by
  obtain ⟨D₀,hD₀,hstrip⟩ := proposition71_zeta_paper_strip_bounds
  refine ⟨D₀,hD₀,?_⟩
  intro D hDN hL c hc hsmall s hs hs1 hsep
  have hlogpos : 0<lemma23PaperL D := by linarith
  have hLp : 0<1/lemma23PaperL D := by positivity
  have hm := proposition71_short_rectangle_shift_margin hL hc hsmall hs
  have hz := (hstrip D hDN).2
  have hi := (hz s hs1 hs.1.1 hs.1.2 hm.2.2.1).2.1
  have hb (j : Fin 3) : ‖riemannZeta (s+lemma83PaperBeta D c j)‖≤9*Real.exp 1*lemma23PaperL D^9 := by
    have hn : s+lemma83PaperBeta D c j≠1 := by
      intro he
      have hh := hsep j
      rw [he,sub_self,norm_zero] at hh
      linarith
    exact (hz _ hn (by simpa [lemma83_beta_re] using hs.1.1)
      (by simpa [lemma83_beta_re] using hs.1.2) (hm.2.2.2 j)).2.2 (hsep j)
  rw [div_eq_mul_inv,norm_mul,norm_mul,norm_mul]
  calc
    _≤(9*Real.exp 1*lemma23PaperL D^9)*(9*Real.exp 1*lemma23PaperL D^9)*
      (9*Real.exp 1*lemma23PaperL D^9)*(9*Real.exp 1*lemma23PaperL D^17) := by
      gcongr <;> first | exact hb 0 | exact hb 1 | exact hb 2
    _=_ := by ring

end ZhangLS.Spec
