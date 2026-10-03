import ZhangLS.Spec.Proposition71PrincipalZetaBounds
import ZhangLS.Spec.Proposition71PrincipalEnvelopeMonotone
import ZhangLS.Spec.Proposition71PrincipalEdgeGeometry
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Set
open scoped Classical
set_option maxHeartbeats 2500000

/-- The complete arithmetic multiplier for the contour budget. -/
noncomputable def proposition71PrincipalArithmeticBound (D d m : ℕ) : ℝ :=
  (lemma34Tau 5 d : ℝ)*proposition71KappaEulerEnvelope d (1-1/lemma23PaperL D)*
    proposition71LambdaEulerEnvelope (d*m) (1-1/lemma23PaperL D)

lemma proposition71_principal_arithmetic_bound_nonneg {D : ℕ}
    (hL : 2000≤lemma23PaperL D) (d m : ℕ) : 0≤proposition71PrincipalArithmeticBound D d m := by
  have hi : 1/lemma23PaperL D≤1/2000 := one_div_le_one_div_of_le (by norm_num) hL
  have ha : 0<1-1/lemma23PaperL D := by linarith
  have hk := proposition71_kappa_euler_envelope_nonneg d ha
  have hl := proposition71_lambda_euler_envelope_nonneg (d*m) ha
  unfold proposition71PrincipalArithmeticBound
  positivity

/-- Genuine all-height right-boundary estimate with full finite arithmetic losses. -/
lemma proposition71_principal_right_pointwise {D : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) (c : ℝ) {d : ℕ} (hd : d≠0) (m : ℕ)
    {q : ℝ} (hq : 0<q) (t : ℝ) :
    ‖proposition71PrincipalMellinIntegrand D (lemma83PaperBeta D c) d m q
      (((1+lemma44PaperAlpha D : ℝ) : ℂ)+(t : ℂ)*I)‖≤
      324*lemma54MellinStripConstant*proposition71PrincipalArithmeticBound D d m*
        q^(1+lemma44PaperAlpha D)*lemma23PaperL D^3236/(1+t^2) := by
  let s : ℂ := ((1+lemma44PaperAlpha D : ℝ) : ℂ)+(t : ℂ)*I
  have hre : s.re=1+lemma44PaperAlpha D := by simp [s]
  have him : s.im=t := by simp [s]
  have hi : 1/lemma23PaperL D≤1/2000 := one_div_le_one_div_of_le (by norm_num) hL
  have hp := proposition71_zeta_paper_alpha_budget (by linarith : 3≤lemma23PaperL D)
  have ha : 0<1-1/lemma23PaperL D := by linarith
  have hs : 1-1/lemma23PaperL D≤s.re := by rw [hre]; linarith [hp.1]
  have hreal := proposition71_short_rectangle_real_bounds hL (s := s) ⟨hs,hre.le⟩
  have hZ := proposition71_principal_zeta_right_bound (by linarith : 3≤lemma23PaperL D)
    (lemma83PaperBeta D c) (lemma83_beta_re D c) hre
  have hδ := proposition71_principal_delta_cauchy_bound hD hL hreal.1 hreal.2
  have hA := proposition71_principal_arithmetic_bound_nonneg hL d m
  have hCM := lemma54_mellin_strip_constant_pos
  apply (proposition71_principal_integrand_norm_uniform_euler D (lemma83PaperBeta D c)
    (lemma83_beta_re D c) hd m hq ha hs).trans
  change proposition71PrincipalArithmeticBound D d m*
    ‖riemannZeta (s+lemma83PaperBeta D c 0)*riemannZeta (s+lemma83PaperBeta D c 1)*
      riemannZeta (s+lemma83PaperBeta D c 2)/riemannZeta s‖*
    q^s.re*‖lemma54PaperDeltaMellin D s‖≤_
  calc
    _≤proposition71PrincipalArithmeticBound D d m*(81*lemma23PaperL D^36)*q^s.re*
      (4*lemma54MellinStripConstant*lemma23PaperL D^3200/(1+s.im^2)) := by gcongr
    _=_ := by rw [hre,him]; ring

/-- The whole-strip estimate for the left and horizontal edges, after actual
zeta exclusion and pole separation, with every arithmetic factor preserved. -/
theorem proposition71_principal_separated_pointwise :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D → 2000≤lemma23PaperL D →
      ∀ c : ℝ, 0<c → c*lemma44PaperAlpha D*lemma23PaperL D≤1/10 →
      ∀ d m : ℕ, d≠0 → ∀ q : ℝ, 0<q → ∀ s : ℂ,
      s∈Icc (1-1/lemma23PaperL D) (1+lemma44PaperAlpha D) ×ℂ
        Icc (-proposition71ZetaAuxHeight D/2) (proposition71ZetaAuxHeight D/2) →
      s≠1 → (∀j : Fin 3, 1/lemma23PaperL D≤‖s+lemma83PaperBeta D c j-1‖) →
      ‖proposition71PrincipalMellinIntegrand D (lemma83PaperBeta D c) d m q s‖≤
        4*lemma54MellinStripConstant*(9*Real.exp 1)^4*proposition71PrincipalArithmeticBound D d m*
          q^s.re*lemma23PaperL D^3244/(1+s.im^2) := by
  obtain ⟨D₀,hD₀,hbound⟩ := proposition71_principal_zeta_short_rectangle_bound
  refine ⟨D₀,hD₀,?_⟩
  intro D hDN hL c hc hsmall d m hd q hq s hs hs1 hsep
  have hD : 1<D := by omega
  have hi : 1/lemma23PaperL D≤1/2000 := one_div_le_one_div_of_le (by norm_num) hL
  have ha : 0<1-1/lemma23PaperL D := by linarith
  have hreal := proposition71_short_rectangle_real_bounds hL hs.1
  have hZ := hbound D hDN hL c hc hsmall s hs hs1 hsep
  have hδ := proposition71_principal_delta_cauchy_bound hD hL hreal.1 hreal.2
  have hA := proposition71_principal_arithmetic_bound_nonneg hL d m
  have hCM := lemma54_mellin_strip_constant_pos
  apply (proposition71_principal_integrand_norm_uniform_euler D (lemma83PaperBeta D c)
    (lemma83_beta_re D c) hd m hq ha hs.1.1).trans
  change proposition71PrincipalArithmeticBound D d m*
    ‖riemannZeta (s+lemma83PaperBeta D c 0)*riemannZeta (s+lemma83PaperBeta D c 1)*
      riemannZeta (s+lemma83PaperBeta D c 2)/riemannZeta s‖*
    q^s.re*‖lemma54PaperDeltaMellin D s‖≤_
  calc
    _≤proposition71PrincipalArithmeticBound D d m*((9*Real.exp 1)^4*lemma23PaperL D^44)*q^s.re*
      (4*lemma54MellinStripConstant*lemma23PaperL D^3200/(1+s.im^2)) := by gcongr
    _=_ := by ring

end ZhangLS.Spec
