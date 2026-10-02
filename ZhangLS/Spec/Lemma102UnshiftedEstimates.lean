import ZhangLS.Spec.Lemma102UnshiftedSumCirclePolynomial
import ZhangLS.Spec.Lemma102CircleBudget
import ZhangLS.Spec.Lemma84Repaired
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Filter Topology
set_option maxHeartbeats 2000000


/-- Genuine uniform error bounds. The first line displays the precise Π loss;
the second is an explicitly weaker L⁻⁵ repair; the third retains the original
L⁻⁶ scale whenever Π vanishes. This unshifted component is not a proof of `Lemma102Target`. -/
theorem lemma102_unshifted_main_error_bounds :
    ∀ c : ℝ, 0 < c → ∃ D₀ : ℕ, 2 ≤ D₀ ∧
      ∀ D : ℕ, D₀ ≤ D → ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
      ∀ j : Fin 3, ∀ d r : ℕ, 0 < d → 0 < r →
      (d*r : ℝ) < lemma23PaperP D*lemma56PaperT D^(-2 : ℤ) →
      ∀ x : ℝ, lemma56PaperT D ≤ x → x < lemma23PaperP D →
        let E := ‖lemma102LogSum χ c j d r x-LDerivAtOne χ*lemma83Pi χ d r*lemma102LogMain D c j x‖
        E ≤ lemma23PaperL D^(-6 : ℤ) +
          lemma84TaylorCircleConstant*lemma23PaperL D^(-6 : ℤ)*‖lemma83Pi χ d r‖ +
          lemma84CorrectionCircleConstant*lemma23PaperL D^(-7 : ℤ)*
            (1+9*Real.log (lemma23PaperL D))^(lemma84PiExponent+2) ∧
        E ≤ 3*lemma23PaperL D^(-5 : ℤ) ∧
        (lemma83Pi χ d r=0 → E ≤ 2*lemma23PaperL D^(-6 : ℤ)) ∧
        E ≤ (2+lemma84TaylorCircleConstant*‖lemma83Pi χ d r‖)*lemma23PaperL D^(-6 : ℤ) := by
  intro c hc
  obtain ⟨Dt,hDt,htransfer⟩ := lemma102_unshifted_actual_sum_circle_transfer c hc
  obtain ⟨Dc,_,hcsmall⟩ := lemma46_exists_contraction_threshold (c := 5*c) (by positivity)
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hK : 3*lemma83FiniteShiftWeight ≤ (lemma84PiExponent:ℝ) := Nat.le_ceil _
  have hC1 := lemma84_circle_constants_pos.1
  have hC2 := lemma84_circle_constants_pos.2
  have hS : 0 < lemma83PrimeProductScale := by unfold lemma83PrimeProductScale; positivity
  have hp1 := ht.eventually (lemma83_polylog_eventually_le
    (lemma84TaylorCircleConstant*lemma83PrimeProductScale) (mul_pos hC1 hS) lemma84PiExponent)
  have hp2 := ht.eventually (lemma83_polylog_eventually_le lemma84CorrectionCircleConstant hC2 (lemma84PiExponent+2))
  obtain ⟨D₀,hD₀⟩ := Filter.eventually_atTop.mp (show ∀ᶠ D : ℕ in atTop,
      2 ≤ D ∧ Dt ≤ D ∧ Dc ≤ D ∧ lemma57ExplicitModulusThreshold ≤ D ∧
      2000 ≤ lemma23PaperL D ∧ lemma58ErrorConstant ≤ lemma23PaperL D ∧
      (lemma84TaylorCircleConstant*lemma83PrimeProductScale)*(1+9*Real.log (lemma23PaperL D))^lemma84PiExponent ≤ lemma23PaperL D ∧
      lemma84CorrectionCircleConstant*(1+9*Real.log (lemma23PaperL D))^(lemma84PiExponent+2) ≤ lemma23PaperL D from by
    filter_upwards [eventually_ge_atTop (2:ℕ),eventually_ge_atTop Dt,eventually_ge_atTop Dc,
      eventually_ge_atTop lemma57ExplicitModulusThreshold,ht.eventually_ge_atTop 2000,
      ht.eventually_ge_atTop lemma58ErrorConstant,hp1,hp2] with D h2 ht hc hn hL hC h1 h2'
    exact ⟨h2,ht,hc,hn,hL,hC,h1,h2'⟩)
  refine ⟨D₀,(hD₀ D₀ le_rfl).1,?_⟩
  intro D hDD χ hA j d r hd hr hcut x hxT hxP
  dsimp only
  obtain ⟨h2,hDtD,hDcD,hDN,hL,hCE,hpoly1,hpoly2⟩ := hD₀ D hDD
  have hLp : 0 < lemma23PaperL D := by linarith
  have hL1 : 1 ≤ lemma23PaperL D := by linarith
  have hsmall : c*lemma44PaperAlpha D*lemma23PaperL D ≤ 1/10 := by
    have hh := hcsmall D hDcD
    nlinarith only [hh]
  have ht := htransfer D hDtD χ hA j d r hd hr hcut x hxT hxP
  have hcircle := lemma102_paper_circle_error_with_pi χ hDN hA hCE hc hsmall j d r lemma84PiExponent
    hd hr hcut hK hxT hxP
  have hmain : ‖lemma102LogSum χ c j d r x-LDerivAtOne χ*lemma83Pi χ d r*lemma102LogMain D c j x‖ ≤
      lemma23PaperL D^(-6 : ℤ)+lemma84TaylorCircleConstant*lemma23PaperL D^(-6 : ℤ)*‖lemma83Pi χ d r‖+
      lemma84CorrectionCircleConstant*lemma23PaperL D^(-7 : ℤ)*(1+9*Real.log (lemma23PaperL D))^(lemma84PiExponent+2) := by
    have he : lemma102LogSum χ c j d r x-LDerivAtOne χ*lemma83Pi χ d r*lemma102LogMain D c j x =
        (lemma102LogSum χ c j d r x-lemma102PaperCircle χ c j d r x)+
          (lemma102PaperCircle χ c j d r x-LDerivAtOne χ*lemma83Pi χ d r*lemma102LogMain D c j x) := by ring
    rw [he]
    apply (norm_add_le _ _).trans
    exact (add_le_add ht hcircle).trans_eq (by ring)
  have hcancel6 : lemma23PaperL D*lemma23PaperL D^(-6 : ℤ)=lemma23PaperL D^(-5 : ℤ) := by
    simpa using (zpow_add₀ hLp.ne' 1 (-6)).symm
  have hcancel7 : lemma23PaperL D*lemma23PaperL D^(-7 : ℤ)=lemma23PaperL D^(-6 : ℤ) := by
    simpa using (zpow_add₀ hLp.ne' 1 (-7)).symm
  have hTaylor : lemma84TaylorCircleConstant*lemma23PaperL D^(-6 : ℤ)*‖lemma83Pi χ d r‖ ≤ lemma23PaperL D^(-5 : ℤ) := by
    have hPi := lemma84_pi_polylog_bound χ (by linarith only [hL] : 100 ≤ lemma23PaperL D)
      d r lemma84PiExponent hd hr hcut hK
    calc
      _ ≤ lemma84TaylorCircleConstant*lemma23PaperL D^(-6 : ℤ)*
          (lemma83PrimeProductScale*(1+9*Real.log (lemma23PaperL D))^lemma84PiExponent) :=
        mul_le_mul_of_nonneg_left hPi (by positivity)
      _ = ((lemma84TaylorCircleConstant*lemma83PrimeProductScale)*
          (1+9*Real.log (lemma23PaperL D))^lemma84PiExponent)*lemma23PaperL D^(-6 : ℤ) := by ring
      _ ≤ lemma23PaperL D*lemma23PaperL D^(-6 : ℤ) := mul_le_mul_of_nonneg_right hpoly1 (by positivity)
      _ = _ := hcancel6
  have hCorrection : lemma84CorrectionCircleConstant*lemma23PaperL D^(-7 : ℤ)*
      (1+9*Real.log (lemma23PaperL D))^(lemma84PiExponent+2) ≤ lemma23PaperL D^(-6 : ℤ) := by
    have hh := mul_le_mul_of_nonneg_right hpoly2 (show 0 ≤ lemma23PaperL D^(-7 : ℤ) by positivity)
    rw [hcancel7] at hh
    nlinarith only [hh]
  have hp : lemma23PaperL D^(-6 : ℤ) ≤ lemma23PaperL D^(-5 : ℤ) :=
    zpow_le_zpow_right₀ hL1 (by norm_num)
  refine ⟨hmain,by nlinarith only [hmain,hTaylor,hCorrection,hp],?_,?_⟩
  · intro hPi
    simp only [hPi,norm_zero,mul_zero,zero_mul,sub_zero,add_zero] at hmain ⊢
    nlinarith only [hmain,hCorrection]
  · nlinarith only [hmain,hCorrection]

/-- Uniform actual sum estimate retaining the complete arithmetic loss. -/
theorem lemma102_unshifted_error_with_pi :
    ∀ c : ℝ, 0 < c → ∃ D₀ : ℕ, 2 ≤ D₀ ∧
      ∀ D : ℕ, D₀ ≤ D → ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
      ∀ j : Fin 3, ∀ d r : ℕ, 0 < d → 0 < r →
      (d*r : ℝ) < lemma23PaperP D*lemma56PaperT D^(-2 : ℤ) →
      ∀ x : ℝ, lemma56PaperT D ≤ x → x < lemma23PaperP D →
        ‖lemma102LogSum χ c j d r x-LDerivAtOne χ*lemma83Pi χ d r*lemma102LogMain D c j x‖ ≤
          (2+lemma84TaylorCircleConstant*‖lemma83Pi χ d r‖)*lemma23PaperL D^(-6 : ℤ) := by
  intro c hc
  obtain ⟨D₀,hD02,hmain⟩ := lemma102_unshifted_main_error_bounds c hc
  exact ⟨D₀,hD02,fun D hD χ hA j d r hd hr hcut x hxT hxP =>
    (hmain D hD χ hA j d r hd hr hcut x hxT hxP).2.2.2⟩


end ZhangLS.Spec
