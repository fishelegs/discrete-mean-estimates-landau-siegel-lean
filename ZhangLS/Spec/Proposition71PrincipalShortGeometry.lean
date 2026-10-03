import ZhangLS.Spec.Proposition71PrincipalContourNumerator
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Set
open scoped Classical Topology
set_option maxHeartbeats 2000000

/-- The genuine β shifts fit with a quarter-height margin in the internal H/2 rectangle. -/
lemma proposition71_short_height_beta_margin {D : ℕ} (hL : 2000≤lemma23PaperL D)
    {c : ℝ} (hc : 0<c) (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10) :
    1≤proposition71ZetaAuxHeight D ∧
      ∀j : Fin 3, ‖lemma83PaperBeta D c j‖≤proposition71ZetaAuxHeight D/4 := by
  have hL3 : 3≤lemma23PaperL D := by linarith
  have hH : 1≤proposition71ZetaAuxHeight D := by
    apply Real.one_le_exp
    exact Real.rpow_nonneg (by change 0≤lemma23PaperL D; linarith) _
  have hLi : 1/lemma23PaperL D≤1/2000 := one_div_le_one_div_of_le (by norm_num) hL
  have hα := (proposition71_zeta_paper_alpha_budget hL3).2.1
  refine ⟨hH,?_⟩
  intro j
  have hb := lemma83_paper_beta_norm hL3 hc hsmall j
  linarith

lemma proposition71_short_rectangle_pole_inside {D : ℕ} (hL : 2000≤lemma23PaperL D)
    {c : ℝ} (hc : 0<c) (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10) (j : Fin 3) :
    1-lemma83PaperBeta D c j ∈
      Ioo (1-1/lemma23PaperL D) (1+lemma44PaperAlpha D) ×ℂ
        Ioo (-proposition71ZetaAuxHeight D/2) (proposition71ZetaAuxHeight D/2) := by
  have hLp : 0<lemma23PaperL D := by linarith
  have hα := (proposition71_zeta_paper_alpha_budget (by linarith : 3≤lemma23PaperL D)).1
  have hH := proposition71_zeta_aux_height_pos D
  have hb := (proposition71_short_height_beta_margin hL hc hsmall).2 j
  have him : |(1-lemma83PaperBeta D c j).im|≤proposition71ZetaAuxHeight D/4 := by
    simpa only [sub_im,one_im,zero_sub,abs_neg] using
      (Complex.abs_im_le_norm (lemma83PaperBeta D c j)).trans hb
  have hre : (1-lemma83PaperBeta D c j).re=1 := by simp [lemma83_beta_re]
  change (1-1/lemma23PaperL D<(1-lemma83PaperBeta D c j).re ∧
    (1-lemma83PaperBeta D c j).re<1+lemma44PaperAlpha D) ∧
    (-proposition71ZetaAuxHeight D/2<(1-lemma83PaperBeta D c j).im ∧
      (1-lemma83PaperBeta D c j).im<proposition71ZetaAuxHeight D/2)
  rw [hre]
  have hip := abs_le.mp him
  have hLi : 0<1/lemma23PaperL D := by positivity
  constructor <;> constructor <;> linarith

/-- Every β-shifted point of the internal closed rectangle stays inside the
proved auxiliary ζ-height, with positive real part and the original width. -/
lemma proposition71_short_rectangle_shift_margin {D : ℕ} (hL : 2000≤lemma23PaperL D)
    {c : ℝ} (hc : 0<c) (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10)
    {s : ℂ} (hs : s∈Icc (1-1/lemma23PaperL D) (1+lemma44PaperAlpha D) ×ℂ
      Icc (-proposition71ZetaAuxHeight D/2) (proposition71ZetaAuxHeight D/2)) :
    0<s.re ∧ s.re≤2 ∧ |s.im|≤proposition71ZetaAuxHeight D ∧
      ∀j : Fin 3, |(s+lemma83PaperBeta D c j).im|≤proposition71ZetaAuxHeight D := by
  have hLi : 1/lemma23PaperL D≤1/2000 := one_div_le_one_div_of_le (by norm_num) hL
  have hα := (proposition71_zeta_paper_alpha_budget (by linarith : 3≤lemma23PaperL D)).2.1
  have hH := proposition71_zeta_aux_height_pos D
  have ht : |s.im|≤proposition71ZetaAuxHeight D/2 := abs_le.mpr ⟨by linarith [hs.2.1],hs.2.2⟩
  refine ⟨by linarith [hs.1.1],by linarith [hs.1.2],by linarith,?_⟩
  intro j
  have hb := (proposition71_short_height_beta_margin hL hc hsmall).2 j
  have him := Complex.abs_im_le_norm (lemma83PaperBeta D c j)
  calc
    |(s+lemma83PaperBeta D c j).im|≤|s.im|+|(lemma83PaperBeta D c j).im| := abs_add_le _ _
    _≤proposition71ZetaAuxHeight D := by linarith

end ZhangLS.Spec
