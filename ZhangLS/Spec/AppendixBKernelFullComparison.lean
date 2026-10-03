import ZhangLS.Spec.AppendixBKernelBoundaryIntegrals
import ZhangLS.Spec.Lemma84InfiniteContourAlgebra
import ZhangLS.Spec.Lemma84ContourErrorBudget
import ZhangLS.Spec.Lemma84ActualBoundaryBounds

/-! Genuine full-kernel comparison. The remainder is a proved explicit budget,
not an analytic hypothesis and not a newly chosen alpha₁. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace ZhangLS.Spec
open Complex MeasureTheory Set Filter

noncomputable def appendixBContourBudget (D : ℕ) : ℝ :=
  appendixBContourMajorant D*Real.pi*lemma23PaperL D*
      Real.exp (-(lemma23PaperL D^(1/10 : ℝ)))+
    8*appendixBContourMajorant D*Real.exp (6*Real.pi)*
      (6*lemma44PaperAlpha D+1/lemma23PaperL D)/(appendixBContourHeight D)^2+
    8*(2+1/(6*lemma44PaperAlpha D))^2*Real.exp (6*Real.pi)/appendixBContourHeight D

/-- Unconditional comparison of the original strict full sum with its exact
finite-D residue model. The threshold is before all shifts and l₁. -/
theorem appendixB_full_kernel_quantitative :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      2000≤lemma23PaperL D ∧ ∀ β γ : ℂ,
      β.re=0 → ‖β‖≤3*lemma44PaperAlpha D →
      γ.re=0 → γ≠0 → ‖γ‖≤3*lemma44PaperAlpha D →
      ∀ X : ℝ, 1<X → ∀ l₁ : ℕ, 0<l₁ →
      lemma56PaperT D<X/l₁ → X/l₁<lemma23PaperP D →
      ‖appendixBFullKernelSum X β γ l₁-appendixBModelLeading X (X/l₁) β γ‖≤
        (appendixBContourBudget D+275*Real.exp (5*Real.pi))/Real.log X := by
  obtain ⟨N,hN,hrect⟩ := appendixB_actual_rectangle_circle
  obtain ⟨M,hM,hbound⟩ := appendixB_actual_contour_ratio_bound
  refine ⟨max N M,hN.trans (le_max_left _ _),?_⟩
  intro D hD
  obtain ⟨hL,hrectD⟩ := hrect D ((le_max_left _ _).trans hD)
  have hboundD := (hbound D ((le_max_right _ _).trans hD)).2
  refine ⟨hL,?_⟩
  intro β γ hβre hβ hγre hγ0 hγ X hX l₁ hl hxT hxP
  let x := X/(l₁ : ℝ)
  let b := 6*lemma44PaperAlpha D
  let Y := appendixBContourHeight D
  let F := appendixBZetaIntegrand x β γ
  let R := ∫ t : ℝ in -Y..Y, F ((b : ℂ)+I*(t : ℂ))
  let L := ∫ t : ℝ in -Y..Y, F ((-1/lemma23PaperL D : ℝ)+I*(t : ℂ))
  let lo := ∫ σ : ℝ in (-1/lemma23PaperL D)..b, F ((σ : ℂ)-I*(Y : ℂ))
  let hi := ∫ σ : ℝ in (-1/lemma23PaperL D)..b, F ((σ : ℂ)+I*(Y : ℂ))
  let tl := ∫ t : ℝ in Iic (-Y), F ((b : ℂ)+I*(t : ℂ))
  let tr := ∫ t : ℝ in Ioi Y, F ((b : ℂ)+I*(t : ℂ))
  let P := (2*Real.pi : ℂ)⁻¹*(∫ t : ℝ, F ((b : ℂ)+I*(t : ℂ)))
  let C := (2*Real.pi*I : ℂ)⁻¹*circleIntegral F 0 (5*lemma44PaperAlpha D)
  have hLp : 0<lemma23PaperL D := by linarith
  have hD2 : 1<D := by have := hN.trans ((le_max_left _ _).trans hD); omega
  have hα := lemma83_alpha_small (by linarith only [hL] : 100≤lemma23PaperL D)
  have hb : 0<b := by dsimp [b]; positivity [hα.1]
  have hY : 0<Y := div_pos (proposition71_zeta_aux_height_pos D) (by norm_num)
  have hx : 0<x := div_pos (by linarith) (Nat.cast_pos.mpr hl)
  have hT1 : 1≤lemma56PaperT D := Real.one_le_exp (Real.rpow_nonneg hLp.le _)
  have hx1 : 1≤x := (hT1.trans_lt hxT).le
  have hlog : 0<Real.log X := Real.log_pos hX
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hscale : lemma44PaperAlpha D*Real.log x≤Real.pi := lemma84_alpha_log_x_le_pi hLp hx hxP
  have hM0 : 0≤appendixBContourMajorant D := by unfold appendixBContourMajorant; positivity
  have hnum := fun s hs => (hboundD β hβre hβ s hs).2
  have hper : appendixBFullKernelSum X β γ l₁=P/(Real.log X : ℂ) := by
    rw [appendixB_full_kernel_perron (by linarith : 0<X) hlog.ne' hb hβre hγre hl]
    dsimp [P,F,x]
    congr 2
    apply integral_congr_ae
    filter_upwards [] with t
    unfold appendixBZetaIntegrand
    ring
  have hP : P=(2*Real.pi : ℂ)⁻¹*(tl+R+tr) := by
    dsimp [P,tl,R,tr]
    rw [lemma84_integral_split_three _ (appendixB_right_line_integrable hb hx hβre hγre) hY.le]
  have hC : C=(2*Real.pi : ℂ)⁻¹*(R-L)+(2*Real.pi*I : ℂ)⁻¹*(lo-hi) := by
    have hrect' := hrectD β γ hβre hβ hγ0 hγ x hx
    change lemma44GeneralRectangleBoundaryIntegral F (-1/lemma23PaperL D) b Y = _ at hrect'
    dsimp [C]
    rw [←hrect']
    unfold lemma44GeneralRectangleBoundaryIntegral
    dsimp [R,L,lo,hi]
    simp only [mul_comm (I : ℂ)]
    field_simp
    ring
  have hmain := lemma84_normalized_boundary_error P C R L lo hi tl tr hP hC
  have hleft := appendixB_left_boundary_bound hLp hx hM0 β γ hγre hnum
  have hleft' : ‖L‖≤appendixBContourMajorant D*Real.pi*lemma23PaperL D*
      Real.exp (-(lemma23PaperL D^(1/10 : ℝ))) := by
    apply hleft.trans
    have he := mul_le_mul_of_nonneg_left (lemma84_paper_left_exponential hLp hxT)
      (show 0≤appendixBContourMajorant D*Real.pi*lemma23PaperL D by positivity)
    nlinarith only [he]
  have hhor := appendixB_horizontal_bound hD2 hL hx1 hscale hM0 β γ hγ hnum
  have hH1 : 1≤proposition71ZetaAuxHeight D :=
    Real.one_le_exp (Real.rpow_nonneg (by change 0≤lemma23PaperL D; linarith) _)
  have hγY : |γ.im|≤Y/2 := by
    have hh := (Complex.abs_im_le_norm γ).trans hγ
    dsimp [Y,appendixBContourHeight]
    linarith [hα.2]
  have htail := appendixB_right_tails hb hx hY hβre hγre hγY
  dsimp only at htail
  have htail' : ‖tr‖+‖tl‖≤8*(2+1/b)^2*Real.exp (6*Real.pi)/Y := by
    apply htail.trans
    apply div_le_div_of_nonneg_right _ hY.le
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    dsimp [b]
    linarith [hscale]
  have hPC : ‖P-C‖≤appendixBContourBudget D := by
    change ‖lo‖+‖hi‖≤_ at hhor
    unfold appendixBContourBudget
    change ‖P-C‖≤_+_+8*(2+1/b)^2*Real.exp (6*Real.pi)/Y
    linarith only [hmain,hleft',hhor,htail']
  have hsumcircle : ‖appendixBFullKernelSum X β γ l₁-
      appendixBZetaCircle X x β γ (5*lemma44PaperAlpha D)‖≤appendixBContourBudget D/Real.log X := by
    rw [hper]
    change ‖P/(Real.log X : ℂ)-C/(Real.log X : ℂ)‖≤_
    rw [←sub_div,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hlog]
    exact div_le_div_of_nonneg_right hPC hlog.le
  have hcircle := appendixB_actual_circle_leading_error hα.1 hα.2 hX hx1 hscale hβ hγ hγ0
  have ht := norm_add_le (appendixBFullKernelSum X β γ l₁-
    appendixBZetaCircle X x β γ (5*lemma44PaperAlpha D))
    (appendixBZetaCircle X x β γ (5*lemma44PaperAlpha D)-appendixBModelLeading X x β γ)
  rw [sub_add_sub_cancel] at ht
  apply ht.trans
  exact (add_le_add hsumcircle hcircle).trans_eq (by rw [add_div])

end ZhangLS.Spec
