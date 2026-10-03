import ZhangLS.Spec.AppendixBTailRightBoundary
import ZhangLS.Spec.AppendixBTailHorizontalBoundary
import ZhangLS.Spec.AppendixBTailGlobalContour
import ZhangLS.Spec.AppendixBTailBudgetDecay

/-! The actual full Gaussian source slice is close to its exact finite-D
residue. All four contour sides and both infinite tails are proved here. -/
set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace ZhangLS.Spec
open Complex MeasureTheory Set Filter

/-- One threshold before beta, gamma, every positive l1<T, and every source z.
This compares the actual convergent Gaussian rho series to the actual residue,
without an assumed contour remainder or any sharp-tail hypothesis. -/
theorem appendixB_source_gaussian_slice_quantitative :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      2000≤lemma23PaperL D ∧ ∀ β γ : ℂ,
      β.re=0 → β≠0 → ‖β‖≤3*lemma44PaperAlpha D →
      γ.re=0 → γ≠0 → ‖γ‖≤3*lemma44PaperAlpha D →
      ∀ l₁ : ℕ, 0<l₁ → (l₁ : ℝ)<lemma56PaperT D →
      ∀ z : ℝ, z∈Icc (0.5 : ℝ) 0.504 →
      ‖appendixBSourceGaussianSlice D (lemma23PaperL D^9) z β γ l₁-
        lemma151ExactTailResidue D (lemma23PaperL D^9) z β γ‖≤appendixBTailContourBudget D := by
  obtain ⟨N,hN,hrect⟩ := appendixB_tail_actual_rectangle_circle
  obtain ⟨M,hM,hbounds⟩ := appendixB_actual_contour_ratio_bound
  obtain ⟨Q,hQ⟩ := eventually_atTop.mp appendixB_source_scales_uniform
  refine ⟨max N (max M Q),hN.trans (le_max_left _ _),?_⟩
  intro D hD
  obtain ⟨hL,hrectD⟩ := hrect D ((le_max_left _ _).trans hD)
  have hMQ : max M Q≤D := (le_max_right _ _).trans hD
  have hboundD := (hbounds D ((le_max_left _ _).trans hMQ)).2
  have hrange := (hQ D ((le_max_right _ _).trans hMQ)).2
  have hD2 : 1<D := by have := hN.trans ((le_max_left _ _).trans hD); omega
  have hLp : 0<lemma23PaperL D := by linarith
  have hα := lemma83_alpha_small (by linarith : 100≤lemma23PaperL D)
  refine ⟨hL,?_⟩
  intro β γ hβre hβ0 hβ hγre hγ0 hγ l₁ hl hlT z hz
  let b := 6*lemma44PaperAlpha D
  let Y := appendixBContourHeight D
  let K := 6*Real.exp 1*lemma23PaperL D^15
  let F := lemma151TailIntegrand D (lemma23PaperL D^9) z β γ l₁
  let R := ∫ t : ℝ in -Y..Y, F ((b : ℂ)+I*(t : ℂ))
  let Li := ∫ t : ℝ in -Y..Y, F ((-1/lemma23PaperL D : ℝ)+I*(t : ℂ))
  let lo := ∫ σ : ℝ in (-1/lemma23PaperL D)..b, F ((σ : ℂ)-I*(Y : ℂ))
  let hi := ∫ σ : ℝ in (-1/lemma23PaperL D)..b, F ((σ : ℂ)+I*(Y : ℂ))
  let tl := ∫ t : ℝ in Iic (-Y), F ((b : ℂ)+I*(t : ℂ))
  let tr := ∫ t : ℝ in Ioi Y, F ((b : ℂ)+I*(t : ℂ))
  let P := (2*Real.pi : ℂ)⁻¹*(∫ t : ℝ, F ((b : ℂ)+I*(t : ℂ)))
  let C := (2*Real.pi*I : ℂ)⁻¹*circleIntegral F 0 (5*lemma44PaperAlpha D)
  have hb : 0<b := by dsimp [b]; positivity [hα.1]
  have hb1 : b≤1 := by dsimp [b]; linarith [hα.2]
  have hY : 0<Y := div_pos (proposition71_zeta_aux_height_pos D) (by norm_num)
  have hK : 0≤K := by dsimp [K]; positivity
  have hM0 : 0≤appendixBContourMajorant D := by unfold appendixBContourMajorant; positivity
  have hsource := appendixB_source_standard_line_mellin hD2 (lemma23PaperL D^9) z hb hβre hγre hl
  have hper : P=appendixBSourceGaussianSlice D (lemma23PaperL D^9) z β γ l₁ := by
    have hh := hsource.2
    rw [integral_mul_const] at hh
    apply Eq.trans _ hh
    dsimp [P,F]
    field_simp
    <;> ring
  have hP : P=(2*Real.pi : ℂ)⁻¹*(tl+R+tr) := by
    dsimp [P,tl,R,tr]
    rw [lemma84_integral_split_three _ hsource.1 hY.le]
  have hC : C=(2*Real.pi : ℂ)⁻¹*(R-Li)+(2*Real.pi*I : ℂ)⁻¹*(lo-hi) := by
    have hh := hrectD β γ hβre hβ hγ (lemma23PaperL D^9) z l₁
    change lemma44GeneralRectangleBoundaryIntegral F (-1/lemma23PaperL D) b Y = _ at hh
    dsimp [C]
    rw [←hh]
    unfold lemma44GeneralRectangleBoundaryIntegral
    dsimp [R,Li,lo,hi]
    simp only [mul_comm (I : ℂ)]
    field_simp
    ring
  have hmain := lemma84_normalized_boundary_error P C R Li lo hi tl tr hP hC
  have hnum := fun s hs => (hboundD β hβre hβ s hs).2
  have hxlow := (hrange l₁ hl hlT (0.5 : ℝ) (by norm_num)).1
  have hxrange := hrange l₁ hl hlT z hz
  have hT1 : 1≤lemma56PaperT D := Real.one_le_exp (Real.rpow_nonneg hLp.le _)
  have hx1 : 1≤Real.exp (0.5*lemma23PaperL D^9)/(l₁ : ℝ) := (hT1.trans_lt hxlow).le
  have hleft := appendixB_tail_left_boundary_bound (by linarith : 1≤lemma23PaperL D)
    (show 0≤lemma23PaperL D^9 by positivity) hz.1 hM0 β hγre hl hnum
  have hleft' : ‖Li‖≤K*(appendixBContourMajorant D*Real.pi*lemma23PaperL D*
      Real.exp (-(lemma23PaperL D^(1/10 : ℝ)))) := by
    apply hleft.trans
    have he := lemma84_paper_left_exponential hLp hxlow
    calc
      _ ≤ K*appendixBContourMajorant D*Real.exp (-(lemma23PaperL D^(1/10 : ℝ)))*Real.pi*lemma23PaperL D := by
        change K*appendixBContourMajorant D*_ *Real.pi*lemma23PaperL D≤_
        gcongr
      _ = _ := by ring
  have hhor := appendixB_tail_horizontal_bound hD2 hL (show 0≤lemma23PaperL D^9 by positivity)
    hz.1 hM0 β hγre hγ hl hx1 hxrange.2.2 hnum
  have hH1 : 1≤proposition71ZetaAuxHeight D := Real.one_le_exp (Real.rpow_nonneg hLp.le _)
  have hγY : |γ.im|≤Y/2 := by
    have hh := (Complex.abs_im_le_norm γ).trans hγ
    dsimp [Y,appendixBContourHeight]
    linarith [hα.2]
  have htail := appendixB_tail_right_tails hD2 (by linarith : 1≤lemma23PaperL D)
    (show 0≤lemma23PaperL D^9 by positivity) hz.1 hb hb1 hY hβre hγre hγY hl
  dsimp only at htail
  have htail' : ‖tr‖+‖tl‖≤K*(8*(2+1/b)^2*Real.exp (6*Real.pi)/Y) := by
    apply htail.trans
    have he : b*Real.log (Real.exp (z*lemma23PaperL D^9)/(l₁ : ℝ))≤6*Real.pi := by
      dsimp [b]
      linarith [hxrange.2.2]
    calc
      _ ≤ 16*(3*Real.exp 1*lemma23PaperL D^15)*(2+1/b)^2*Real.exp (6*Real.pi)/Y := by
        gcongr
      _ = _ := by dsimp [K]; ring
  have hPC : ‖P-C‖≤appendixBTailContourBudget D := by
    change ‖lo‖+‖hi‖≤K*(8*appendixBContourMajorant D*Real.exp (6*Real.pi)*
      (6*lemma44PaperAlpha D+1/lemma23PaperL D)/Y^2) at hhor
    unfold appendixBTailContourBudget appendixBContourBudget
    change ‖P-C‖≤K*(_+_+8*(2+1/b)^2*Real.exp (6*Real.pi)/Y)
    nlinarith only [hmain,hleft',hhor,htail']
  have hc : C=lemma151ExactTailResidue D (lemma23PaperL D^9) z β γ :=
    appendixB_tail_actual_circle_residue D (lemma23PaperL D^9) z hα.1 hα.2 hβ0 hβre hβ hγ0 hγ l₁
  rw [hper,hc] at hPC
  exact hPC

end ZhangLS.Spec
