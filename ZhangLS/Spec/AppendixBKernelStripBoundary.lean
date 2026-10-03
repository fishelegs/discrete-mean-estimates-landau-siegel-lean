import ZhangLS.Spec.AppendixBKernelContour
import ZhangLS.Spec.AppendixBKernelRightLine

/-! Actual zeta quotient bounds on the three displaced sides, with the
unconditional auxiliary height and an explicit L^26 cost. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex Filter

noncomputable def appendixBContourHeight (D : ℕ) : ℝ := proposition71ZetaAuxHeight D/2
noncomputable def appendixBContourMajorant (D : ℕ) : ℝ :=
  81*(Real.exp 1)^2*lemma23PaperL D^26

def AppendixBContourPoint (D : ℕ) (s : ℂ) : Prop :=
  (s.re= -1/lemma23PaperL D ∧ |s.im|≤appendixBContourHeight D) ∨
  (|s.im|=appendixBContourHeight D ∧ -1/lemma23PaperL D≤s.re ∧ s.re≤6*lemma44PaperAlpha D)

lemma appendixB_extended_strip_bounds :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      2000≤lemma23PaperL D ∧ ∀ z : ℂ, z≠1 →
      1-1/lemma23PaperL D≤z.re → z.re≤1+6*lemma44PaperAlpha D →
      |z.im|≤proposition71ZetaAuxHeight D →
      riemannZeta z≠0 ∧ ‖(riemannZeta z)⁻¹‖≤9*Real.exp 1*lemma23PaperL D^17 ∧
      (1/lemma23PaperL D≤‖z-1‖ → ‖riemannZeta z‖≤9*Real.exp 1*lemma23PaperL D^9) := by
  obtain ⟨N,hN,hstrip⟩ := proposition71_zeta_paper_strip_bounds
  have hlog : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨M,hM⟩ := eventually_atTop.mp (hlog.eventually (eventually_ge_atTop (2000 : ℝ)))
  refine ⟨max N M,hN.trans (le_max_left _ _),?_⟩
  intro D hD
  have hL := hM D ((le_max_right _ _).trans hD)
  have hL1 : 1≤lemma23PaperL D := by linarith
  have hL0 : 0≤lemma23PaperL D := by linarith
  have ha := proposition71_zeta_paper_alpha_budget (by linarith only [hL] : 3≤lemma23PaperL D)
  have he : 1≤Real.exp 1 := Real.one_le_exp (by norm_num)
  refine ⟨hL,?_⟩
  intro z hz1 hzlo hzhi hzt
  by_cases hz : z.re≤1+lemma44PaperAlpha D
  · exact (hstrip D ((le_max_left _ _).trans hD)).2 z hz1 hzlo hz hzt
  have hzalpha : lemma44PaperAlpha D<z.re-1 := by linarith
  have hzre : 1<z.re := by linarith [ha.1]
  have hbound : 2+1/(z.re-1)≤3*lemma23PaperL D^9 := by
    have hh := (one_div_le_one_div_of_le ha.1 hzalpha.le)
    linarith [ha.2.2.1]
  have hpow : lemma23PaperL D^9≤lemma23PaperL D^17 := pow_le_pow_right₀ hL1 (by norm_num)
  have hdir : 3*lemma23PaperL D^9≤9*Real.exp 1*lemma23PaperL D^9 := by
    nlinarith only [he,pow_nonneg hL0 9]
  have hinv : 3*lemma23PaperL D^9≤9*Real.exp 1*lemma23PaperL D^17 :=
    hdir.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
  have hr := proposition71_zeta_right_half_bounds hzre
  exact ⟨riemannZeta_ne_zero_of_one_lt_re hzre,hr.2.trans (hbound.trans hinv),
    fun _ => hr.1.trans (hbound.trans hdir)⟩

/-- No contour estimate is an assumption: both zeta factors on the displaced
sides follow from the actual auxiliary-height strip and the Möbius anchor. -/
theorem appendixB_actual_contour_ratio_bound :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      2000≤lemma23PaperL D ∧ ∀ β : ℂ, β.re=0 → ‖β‖≤3*lemma44PaperAlpha D →
      ∀ s : ℂ, AppendixBContourPoint D s →
      riemannZeta (1+s-β)≠0 ∧
        ‖riemannZeta (1+s)/riemannZeta (1+s-β)‖≤appendixBContourMajorant D := by
  obtain ⟨N,hN,hstrip⟩ := appendixB_extended_strip_bounds
  refine ⟨N,hN,?_⟩
  intro D hD
  obtain ⟨hL,hbounds⟩ := hstrip D hD
  have hD2 : 1<D := by have := hN.trans hD; omega
  have hgeom := lemma84_paper_rectangle_geometry hD2 hL
  have ha := lemma83_alpha_small (by linarith only [hL] : 100≤lemma23PaperL D)
  have hLpos : 0<lemma23PaperL D := by linarith
  have hi : 0<1/lemma23PaperL D := by positivity
  have hi2 : 1/lemma23PaperL D≤1/2 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hH : 1≤proposition71ZetaAuxHeight D :=
    Real.one_le_exp (Real.rpow_nonneg (by change 0≤lemma23PaperL D; linarith) _)
  have hY : 1/2≤appendixBContourHeight D := by unfold appendixBContourHeight; linarith
  refine ⟨hL,?_⟩
  intro β hβre hβ s hs
  have hre : -1/lemma23PaperL D≤s.re ∧ s.re≤6*lemma44PaperAlpha D := by
    rcases hs with hs | hs
    · rw [hs.1]
      constructor
      · rfl
      · have hn : -1/lemma23PaperL D<0 := div_neg_of_neg_of_pos (by norm_num) hLpos
        linarith [ha.1]
    · exact hs.2
  have him : |s.im|≤appendixBContourHeight D := by
    rcases hs with hs | hs
    · exact hs.2
    · exact hs.1.le
  have hnorm : 1/lemma23PaperL D≤‖s‖ := by
    rcases hs with hs | hs
    · have hn := Complex.abs_re_le_norm s
      rw [hs.1,abs_div,abs_neg,abs_one,abs_of_pos hLpos] at hn
      exact hn
    · have hn := Complex.abs_im_le_norm s
      rw [hs.1] at hn
      exact hi2.trans (hY.trans hn)
  have hs0 : s≠0 := norm_pos_iff.mp (hi.trans_le hnorm)
  have hsb : s≠β := by
    intro he
    rcases hs with hs | hs
    · rw [he,hβre] at hs
      have hh := hs.1
      have hn : -1/lemma23PaperL D<0 := div_neg_of_neg_of_pos (by norm_num) hLpos
      linarith
    · have hh := hs.1
      rw [he] at hh
      have hn := (Complex.abs_im_le_norm β).trans hβ
      linarith [ha.2]
  have hz1 : 1+s≠1 := by intro he; apply hs0; linear_combination he
  have hzb1 : 1+s-β≠1 := by intro he; apply hsb; linear_combination he
  have hlo : 1-1/lemma23PaperL D≤(1+s).re := by
    simp only [add_re,one_re]
    have hh := hre.1
    rw [neg_div] at hh
    linarith
  have hup : (1+s).re≤1+6*lemma44PaperAlpha D := by simpa using add_le_add_left hre.2 1
  have hheight : |(1+s).im|≤proposition71ZetaAuxHeight D := by
    simp only [add_im,one_im,zero_add]
    unfold appendixBContourHeight at him
    linarith
  have hheightβ : |(1+s-β).im|≤proposition71ZetaAuxHeight D := by
    simp only [sub_im,add_im,one_im,zero_add]
    have hh : |s.im-β.im|≤|s.im|+|β.im| := by
      simpa only [sub_eq_add_neg,abs_neg] using abs_add_le s.im (-β.im)
    have hbi := (Complex.abs_im_le_norm β).trans hβ
    unfold appendixBContourHeight at him
    linarith [ha.2]
  have hn := hbounds (1+s) hz1 hlo hup hheight
  have hd := hbounds (1+s-β) hzb1 (by simpa [hβre] using hlo)
    (by simpa [hβre] using hup) hheightβ
  refine ⟨hd.1,?_⟩
  rw [div_eq_mul_inv,norm_mul]
  have hm := mul_le_mul (hn.2.2 (by simpa using hnorm)) hd.2.1 (norm_nonneg _) (by positivity : 0≤9*Real.exp 1*lemma23PaperL D^9)
  apply hm.trans_eq
  unfold appendixBContourMajorant
  ring

end ZhangLS.Spec
