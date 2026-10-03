import ZhangLS.Spec.Proposition71PrincipalBoundaryPointwise
import ZhangLS.Spec.Proposition71PrincipalRightMellin
import ZhangLS.Spec.Proposition71WeightedHeightTail
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Classical Topology
set_option maxHeartbeats 2500000

lemma proposition71_integrable_cauchy_tails (f : ℝ → ℂ) (hf : Integrable f)
    {B H : ℝ} (hB : 0≤B) (hH : 0<H) (hb : ∀t : ℝ, ‖f t‖≤B/(1+t^2)) :
    ‖∫t : ℝ in Iic (-H),f t‖+‖∫t : ℝ in Ioi H,f t‖≤2*B/H := by
  have hm : Integrable (fun t : ℝ => B*(1+t^2)⁻¹) := integrable_inv_one_add_sq.const_mul B
  have hbound (S : Set ℝ) (hS : MeasurableSet S) :
      ‖∫t : ℝ in S,f t‖≤B*(∫t : ℝ in S,(1+t^2)⁻¹) := by
    apply (norm_integral_le_integral_norm _).trans
    have hh := setIntegral_mono_on hf.norm.integrableOn hm.integrableOn hS
      (fun t _ => by simpa only [div_eq_mul_inv] using hb t)
    simpa only [integral_const_mul] using hh
  have hl := (hbound (Iic (-H)) measurableSet_Iic).trans
    (mul_le_mul_of_nonneg_left (proposition71_negative_cauchy_tail hH) hB)
  have hr := (hbound (Ioi H) measurableSet_Ioi).trans
    (mul_le_mul_of_nonneg_left (proposition71_positive_cauchy_tail hH) hB)
  exact (add_le_add hl hr).trans_eq (by ring)

/-- Both actual infinite source tails on Re(s)=1+α, with full finite-prime
losses and H⁻¹ saving proved from the integrable Cauchy envelope. -/
theorem proposition71_principal_right_tails {D : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) (c : ℝ) {d m : ℕ} (hd : d≠0) (hm : m≠0)
    {q : ℝ} (hq : 0<q) :
    let F := fun t : ℝ => proposition71PrincipalMellinIntegrand D (lemma83PaperBeta D c) d m q
      (((1+lemma44PaperAlpha D : ℝ) : ℂ)+(t : ℂ)*I)
    ‖∫t : ℝ in Iic (-(proposition71ZetaAuxHeight D/2)),F t‖+
      ‖∫t : ℝ in Ioi (proposition71ZetaAuxHeight D/2),F t‖≤
      1296*lemma54MellinStripConstant*proposition71PrincipalArithmeticBound D d m*
        q^(1+lemma44PaperAlpha D)*lemma23PaperL D^3236/proposition71ZetaAuxHeight D := by
  dsimp only
  let F := fun t : ℝ => proposition71PrincipalMellinIntegrand D (lemma83PaperBeta D c) d m q
    (((1+lemma44PaperAlpha D : ℝ) : ℂ)+(t : ℂ)*I)
  let B := 324*lemma54MellinStripConstant*proposition71PrincipalArithmeticBound D d m*
    q^(1+lemma44PaperAlpha D)*lemma23PaperL D^3236
  have hα := (proposition71_zeta_paper_alpha_budget (by linarith : 3≤lemma23PaperL D)).1
  have hσ : 1<1+lemma44PaperAlpha D := by linarith
  have hi : Integrable F := (proposition71_actual_general_principal_mellin_source hD hL
    (lemma83PaperBeta D c) (lemma83_beta_re D c) hσ hd hm hq).2.1
  have hA := proposition71_principal_arithmetic_bound_nonneg hL d m
  have hC := lemma54_mellin_strip_constant_pos
  have hB : 0≤B := by dsimp [B]; positivity
  have hH : 0<proposition71ZetaAuxHeight D/2 := by have := proposition71_zeta_aux_height_pos D; positivity
  have ht := proposition71_integrable_cauchy_tails F hi hB hH
    (fun t => proposition71_principal_right_pointwise hD hL c hd m hq t)
  apply ht.trans_eq
  dsimp [B]
  field_simp
  ring

end ZhangLS.Spec
