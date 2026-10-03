import ZhangLS.Spec.AppendixBKernelOriginalPhases

/-! The explicit error is a genuine asymptotic error. The auxiliary contour
height is exp(L^(1/10))/2 and is independent of the local phase bound pi. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace ZhangLS.Spec
open Filter Topology

noncomputable def appendixBContourPolynomialConstant : ℝ :=
  81*(Real.exp 1)^2*Real.pi+5184*(Real.exp 1)^2*Real.exp (6*Real.pi)+144*Real.exp (6*Real.pi)

lemma appendixB_contour_budget_nonneg {D : ℕ} (hL : 0<lemma23PaperL D) :
    0≤appendixBContourBudget D := by
  have hα : 0<lemma44PaperAlpha D := by
    unfold lemma44PaperAlpha lemma23PaperP
    rw [Real.log_exp]
    positivity [Real.pi_pos]
  have hY := proposition71_zeta_aux_height_pos D
  unfold appendixBContourBudget appendixBContourMajorant appendixBContourHeight
  positivity

lemma appendixB_contour_budget_polynomial {D : ℕ} (hL : 2000≤lemma23PaperL D) :
    appendixBContourBudget D≤appendixBContourPolynomialConstant*lemma23PaperL D^27*
      Real.exp (-(lemma23PaperL D^(1/10:ℝ))) := by
  let L := lemma23PaperL D
  let E := Real.exp (-(L^(1/10:ℝ)))
  have hLp : 0<L := by dsimp [L]; linarith only [hL]
  have hL1 : 1≤L := by dsimp [L]; linarith only [hL]
  have hE : 0<E := Real.exp_pos _
  have hE1 : E≤1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.rpow_nonneg hLp.le _))
  have hα := lemma83_alpha_small (by linarith only [hL] : 100≤lemma23PaperL D)
  have hαp := hα.1
  have hαeq : lemma44PaperAlpha D=Real.pi/L^9 := by
    unfold lemma44PaperAlpha lemma23PaperP
    rw [Real.log_exp]
  have hY : 1/appendixBContourHeight D=2*E := by
    unfold appendixBContourHeight proposition71ZetaAuxHeight E L lemma23PaperL
    rw [Real.exp_neg]
    ring
  have hY2 : 1/(appendixBContourHeight D)^2≤4*E := by
    rw [one_div,←inv_pow,show (appendixBContourHeight D)⁻¹=2*E from by simpa only [one_div] using hY]
    nlinarith only [mul_le_mul_of_nonneg_left hE1 hE.le]
  have hwidth : 6*lemma44PaperAlpha D+1/L≤2 := by
    have hi : 1/L≤1 := (div_le_one hLp).mpr hL1
    linarith only [hi,hα.2]
  have hinv : 1/(6*lemma44PaperAlpha D)≤L^9 := by
    rw [hαeq]
    apply (div_le_iff₀ (by positivity : 0<6*(Real.pi/L^9))).mpr
    have hp : (L^9)* (6*(Real.pi/L^9))=6*Real.pi := by field_simp
    rw [hp]
    linarith [Real.two_le_pi]
  have hW : (2+1/(6*lemma44PaperAlpha D))^2≤9*L^18 := by
    have hbase : 2+1/(6*lemma44PaperAlpha D)≤3*L^9 := by
      linarith only [hinv,one_le_pow₀ hL1 (n:=9)]
    have hh := pow_le_pow_left₀ (by positivity : 0≤2+1/(6*lemma44PaperAlpha D)) hbase 2
    simpa only [mul_pow,←pow_mul,show (3:ℝ)^2=9 by norm_num,show 9*2=18 by norm_num] using hh
  have hp26 : L^26≤L^27 := pow_le_pow_right₀ hL1 (by norm_num)
  have hp18 : L^18≤L^27 := pow_le_pow_right₀ hL1 (by norm_num)
  have hleft : appendixBContourMajorant D*Real.pi*L*E=
      81*(Real.exp 1)^2*Real.pi*L^27*E := by
    unfold appendixBContourMajorant
    change 81*(Real.exp 1)^2*L^26*Real.pi*L*E=_
    ring
  have hhor : 8*appendixBContourMajorant D*Real.exp (6*Real.pi)*
      (6*lemma44PaperAlpha D+1/L)/(appendixBContourHeight D)^2≤
      5184*(Real.exp 1)^2*Real.exp (6*Real.pi)*L^27*E := by
    calc
      _ = (8*(81*(Real.exp 1)^2)*Real.exp (6*Real.pi))*L^26*
          (6*lemma44PaperAlpha D+1/L)*(1/(appendixBContourHeight D)^2) := by
        unfold appendixBContourMajorant
        change 8*(81*(Real.exp 1)^2*L^26)*_*(6*lemma44PaperAlpha D+1/L)/_=_
        ring
      _ ≤ (8*(81*(Real.exp 1)^2)*Real.exp (6*Real.pi))*L^27*2*(4*E) := by
        gcongr
      _ = _ := by ring
  have htail : 8*(2+1/(6*lemma44PaperAlpha D))^2*Real.exp (6*Real.pi)/appendixBContourHeight D≤
      144*Real.exp (6*Real.pi)*L^27*E := by
    rw [div_eq_mul_one_div,hY]
    calc
      _ ≤ 8*(9*L^18)*Real.exp (6*Real.pi)*(2*E) := by gcongr
      _ ≤ 8*(9*L^27)*Real.exp (6*Real.pi)*(2*E) := by gcongr
      _ = _ := by ring
  unfold appendixBContourBudget appendixBContourPolynomialConstant
  change appendixBContourMajorant D*Real.pi*L*E+_+_≤_*L^27*E
  rw [hleft]
  nlinarith only [hhor,htail]

lemma appendixB_contour_budget_eventually :
    ∀ᶠ D : ℕ in atTop, 0≤appendixBContourBudget D ∧ appendixBContourBudget D≤1 := by
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hC : 0<appendixBContourPolynomialConstant := by
    unfold appendixBContourPolynomialConstant
    positivity [Real.pi_pos]
  have he := ht.eventually (lemma84_stretched_exponential_absorption _ hC 27 0)
  filter_upwards [ht.eventually_ge_atTop 2000,he] with D hL he
  refine ⟨appendixB_contour_budget_nonneg (by linarith only [hL]),?_⟩
  exact (appendixB_contour_budget_polynomial hL).trans (by simpa using he)

lemma appendixB_original_error_eventual_bound {c : ℝ} (hc : 0<c) :
    ∀ᶠ D : ℕ in atTop,
      0≤appendixBOriginalError D c ∧
      appendixBOriginalError D c≤
        (4*(1+275*Real.exp (5*Real.pi))+(5*Real.pi+40)*c+
          (412+960/Real.pi+132*Real.pi))*lemma23PaperL D^(-79/10:ℝ) := by
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [ht.eventually_ge_atTop 1,appendixB_contour_budget_eventually] with D hL hB
  have hLp : 0<lemma23PaperL D := lt_of_lt_of_le zero_lt_one hL
  have hT : 1≤Real.log (lemma56PaperT D) := by
    rw [lemma56PaperT,Real.log_exp]
    exact Real.one_le_rpow hL (by norm_num)
  have hLT : lemma23PaperL D≤Real.log (lemma56PaperT D) := by
    rw [lemma56PaperT,Real.log_exp]
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (1:ℝ)≤11/10)
  have hcoef : 0≤412+960/Real.pi+132*Real.pi := by positivity [Real.pi_pos]
  have hratio : Real.log (lemma56PaperT D)/lemma23PaperL D^9=lemma23PaperL D^(-79/10:ℝ) := by
    rw [lemma56PaperT,Real.log_exp,←Real.rpow_natCast,←Real.rpow_sub hLp]
    norm_num
  refine ⟨?_,?_⟩
  · unfold appendixBOriginalError
    have hB0 := hB.1
    have hT0 : 0≤Real.log (lemma56PaperT D) := by linarith only [hT]
    positivity
  · unfold appendixBOriginalError
    rw [←hratio,←mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (pow_nonneg hLp.le 9)
    have h₁ := mul_le_mul_of_nonneg_left hT (by positivity : 0≤4*(1+275*Real.exp (5*Real.pi)))
    have h₂ := mul_le_mul_of_nonneg_left hLT (by positivity : 0≤(5*Real.pi+40)*c)
    nlinarith only [hB.2,h₁,h₂]

/-- No alpha1 is invented: this explicitly proved error tends to zero, at least
at the displayed L^(-79/10) rate for each fixed positive original c-prime. -/
theorem appendixB_original_error_tendsto_zero {c : ℝ} (hc : 0<c) :
    Tendsto (fun D : ℕ => appendixBOriginalError D c) atTop (𝓝 0) := by
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hp := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<79/10)).comp ht
  have hb := hp.const_mul (4*(1+275*Real.exp (5*Real.pi))+(5*Real.pi+40)*c+
    (412+960/Real.pi+132*Real.pi))
  apply squeeze_zero' ((appendixB_original_error_eventual_bound hc).mono
    (fun _ h => h.1)) ((appendixB_original_error_eventual_bound hc).mono (fun _ h => h.2))
  simpa only [neg_div,mul_zero] using hb

end ZhangLS.Spec
