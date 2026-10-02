import ZhangLS.Spec.Lemma84SumCircleQuantitative
import ZhangLS.Spec.Lemma84ScalarContourBudget
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Filter Topology
set_option maxHeartbeats 2000000

noncomputable def lemma84ContourTransferConstant (C : ℝ) (K : ℕ) : ℝ :=
  (C*Real.pi+16*C*Real.exp (6*Real.pi)+64*Real.exp (6*Real.pi))*lemma84UScalarConstant K

lemma lemma84_contour_transfer_constant_pos {C : ℝ} (hC : 0 ≤ C) (K : ℕ) :
    0 < lemma84ContourTransferConstant C K := by
  unfold lemma84ContourTransferConstant
  positivity [lemma84_u_scalar_constant_pos K]

lemma lemma84_actual_sum_circle_polynomial {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 2000 ≤ lemma23PaperL D)
    (hlog : 20*Real.log (lemma23PaperL D) ≤ lemma23PaperL D) {ρ : ℝ}
    (hρ : 0 < 1-ρ) (hclose : 1-ρ ≤ 64*lemma23PaperL D^(-2022 : ℤ))
    (hzero : dirichletLFunction χ (ρ:ℂ)=0) (hsimple : deriv (dirichletLFunction χ) (ρ:ℂ) ≠ 0)
    (hunique : ∀ z : ℂ, Lemma55InZeroRegion D z → dirichletLFunction χ z=0 → z=(ρ:ℂ))
    (c : ℝ) (j : Fin 3) (μ d r K : ℕ) (hd : 0 < d) (hr : 0 < r)
    (hcut : (d*r : ℝ) < lemma23PaperP D*lemma56PaperT D^(-2 : ℤ))
    (hK : 9*lemma84UGrowthConstant ≤ (K:ℝ)) {x C : ℝ}
    (hxT : lemma56PaperT D < x) (hxP : x < lemma23PaperP D) (hC : 0 ≤ C)
    (hnum : ∀ s : ℂ, Lemma84ContourPoint D s →
      ‖lemma84ContourNumerator χ c j d r s‖ ≤ C*lemma23PaperL D^28*lemma84UContourScale D K) :
    ‖lemma84XiSum χ c j μ d r x-lemma84PaperCircle χ c j μ d r x‖ ≤
      lemma84ContourTransferConstant C K*lemma23PaperL D^(K+29)*
        Real.exp (-(lemma23PaperL D^(1/10:ℝ))) := by
  have hLp : 0 < lemma23PaperL D := by linarith
  have hL1 : 1 ≤ lemma23PaperL D := by linarith
  have hDpos : (0:ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hgeom := lemma84_paper_rectangle_geometry hD hL
  have hb : 0 < 6*lemma44PaperAlpha D := by positivity [hgeom.1]
  have hU := lemma84_u_contour_scale_nonneg (K := K) hL1
  have hraw := lemma84_actual_sum_circle_quantitative χ hD hL hρ hclose hzero hsimple hunique
    c j μ d r hd hr hxT hxP (by positivity : 0 ≤ C*lemma23PaperL D^28*lemma84UContourScale D K) hnum
  have hMr := lemma84_right_majorant_polylog (by linarith only [hL] : 100 ≤ lemma23PaperL D)
    hlog d r K hd hr hcut hK hb
  have hInv := lemma84_modulus_inverse_exponential hD hL1
  have hwidth : 6*lemma44PaperAlpha D+1/lemma23PaperL D ≤ 2 := by
    have hi : 1/lemma23PaperL D ≤ 1 := (div_le_one hLp).mpr hL1
    linarith only [hgeom.2.2.2.2,hi]
  have hscalar := lemma84_total_boundary_scalar_budget (lemma23PaperL D) D C (lemma84UContourScale D K)
    (lemma84UScalarConstant K) (Real.exp (-(lemma23PaperL D^(1/10:ℝ))))
    (6*lemma44PaperAlpha D+1/lemma23PaperL D) ((1+(6*lemma44PaperAlpha D)⁻¹)^3) K
    hL1 hDpos hC hU (lemma84_u_scalar_constant_pos K).le (Real.exp_pos _).le
    (lemma84_u_scale_polynomial hL1 K) hInv.1 hInv.2 (by positivity) hwidth
    (by positivity) (lemma84_six_alpha_right_scale (by linarith only [hL]))
  apply hraw.trans
  apply le_trans _ hscalar
  apply add_le_add le_rfl
  apply div_le_div_of_nonneg_right _ hDpos.le
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMr (by norm_num : (0:ℝ) ≤ 8))
    (Real.exp_pos (6*Real.pi)).le
  exact hh.trans_eq (by ring)

/-- Complete genuine Perron-to-circle transfer with the original strict
dr and x cutoffs and uniform conductor threshold. The original main-term
Taylor/Π issue is intentionally separate from this theorem. -/
theorem lemma84_actual_sum_circle_transfer :
    ∀ c : ℝ, 0 < c → ∃ D₀ : ℕ, 2 ≤ D₀ ∧
      ∀ D : ℕ, D₀ ≤ D → ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
      ∀ j : Fin 3, ∀ μ d r : ℕ, 0 < d → 0 < r →
      (d*r : ℝ) < lemma23PaperP D*lemma56PaperT D^(-2 : ℤ) →
      ∀ x : ℝ, lemma56PaperT D < x → x < lemma23PaperP D →
        ‖lemma84XiSum χ c j μ d r x-lemma84PaperCircle χ c j μ d r x‖ ≤
          lemma23PaperL D^(-6 : ℤ) := by
  intro c hc
  obtain ⟨C,hC,Dn,hDn,hnum⟩ := lemma84_actual_uniform_contour_numerator
  obtain ⟨D55,h55⟩ := lemma55_at_constant_sixty_four.2
  obtain ⟨Dc,_,hcsmall⟩ := lemma46_exists_contraction_threshold (c := 5*c) (by positivity)
  let K : ℕ := ⌈9*lemma84UGrowthConstant⌉₊
  have hK : 9*lemma84UGrowthConstant ≤ (K:ℝ) := Nat.le_ceil _
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have he := ht.eventually (lemma84_stretched_exponential_absorption
    (lemma84ContourTransferConstant C K) (lemma84_contour_transfer_constant_pos hC.le K) (K+29) 6)
  have hp := ht.eventually (lemma83_polylog_eventually_le 20 (by norm_num) 1)
  obtain ⟨D₀,hD₀⟩ := Filter.eventually_atTop.mp (show ∀ᶠ D : ℕ in atTop,
      2 ≤ D ∧ Dn ≤ D ∧ D55 ≤ D ∧ Dc ≤ D ∧ 2000 ≤ lemma23PaperL D ∧
        20*(1+9*Real.log (lemma23PaperL D)) ≤ lemma23PaperL D ∧
        lemma84ContourTransferConstant C K*lemma23PaperL D^(K+29)*
          Real.exp (-(lemma23PaperL D^(1/10:ℝ))) ≤ lemma23PaperL D^(-6 : ℤ) from by
    filter_upwards [eventually_ge_atTop (2:ℕ),eventually_ge_atTop Dn,eventually_ge_atTop D55,
      eventually_ge_atTop Dc,ht.eventually_ge_atTop 2000,hp,he] with D h2 hn h55 hc hL hp he
    exact ⟨h2,hn,h55,hc,hL,by simpa only [pow_one] using hp,he⟩)
  refine ⟨D₀,(hD₀ D₀ le_rfl).1,?_⟩
  intro D hDD χ hA j μ d r hd hr hcut x hxT hxP
  have hdata := hD₀ D hDD
  obtain ⟨h2,hn,h55D,hcD,hL,hpoly,herr⟩ := hdata
  have hD : 1 < D := by omega
  have hlog0 := Real.log_nonneg (show 1 ≤ lemma23PaperL D by linarith only [hL])
  have hlog : 20*Real.log (lemma23PaperL D) ≤ lemma23PaperL D := by nlinarith only [hpoly,hlog0]
  have hsmall : c*lemma44PaperAlpha D*lemma23PaperL D ≤ 1/10 := by
    have hh := hcsmall D hcD
    nlinarith only [hh]
  obtain ⟨ρ,hρ,hclose,hzero,hsimple,hunique⟩ := h55 χ h55D hD hA
  apply (lemma84_actual_sum_circle_polynomial χ hD hL hlog hρ hclose hzero hsimple hunique
    c j μ d r K hd hr hcut hK hxT hxP hC.le ?_).trans herr
  intro s hs
  exact hnum χ hn hA c hc hsmall j d r K hd hr hcut hK (by linarith only [hL]) hlog s hs

end ZhangLS.Spec
