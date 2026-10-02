import ZhangLS.Spec.Lemma52
import ZhangLS.Spec.Lemma59

/-! # Actual kernel replacement in the proof of Lemma 8.1

This bounded component proves the page-43 replacement of the actual normalized
M-quotient by the actual three-shift L-quotient on the right contour. It is not
claimed to be the complete discrete-mean identity. No quotient estimate,
critical-line zero assertion, or inverse gamma-factor bound is assumed.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Set
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

/-- Exactly C(s, ψ) in (7.1), including the prime-dependent phase. -/
noncomputable def lemma81ActualC {p : ℕ} [NeZero p]
    (D : ℕ) (c : ℝ) (ψ : DirichletCharacter ℂ p) (s : ℂ) : ℂ :=
  -I * (((p : ℝ) * lemma51PaperT0 D : ℝ) : ℂ) ^ lemma52PaperBetaThree D c *
    (lemma23DirichletZ ψ s)⁻¹ *
    (ψ.LFunction (s + lemma52PaperBetaOne D c) *
      ψ.LFunction (s + lemma52PaperBetaTwo D c) *
      ψ.LFunction (s + lemma52PaperBetaThree D c) / ψ.LFunction s)

/-- Exactly C̃(s, ψ) on page 42, for an actual branch Y. -/
noncomputable def lemma81ActualCtilde {p : ℕ} [NeZero p]
    (D : ℕ) (c : ℝ) (ψ : DirichletCharacter ℂ p) (Y : ℂ → ℂ) (s : ℂ) : ℂ :=
  -I * (lemma23DirichletNormalizedM ψ Y (s + lemma52PaperBetaOne D c) *
    lemma23DirichletNormalizedM ψ Y (s + lemma52PaperBetaTwo D c) *
    lemma23DirichletNormalizedM ψ Y (s + lemma52PaperBetaThree D c)) /
      lemma23DirichletNormalizedM ψ Y s

/-- The right-hand segment J(α), including its endpoints. -/
def Lemma81OnRightSegment (D : ℕ) (s : ℂ) : Prop :=
  s.re = 1 / 2 + lemma44PaperAlpha D ∧
    |s.im - (lemma23PaperCenter D).im| ≤ lemma23PaperL D ^ 405

theorem lemma81_inverse_Z_norm_bound {D N : ℕ} [NeZero N]
    (θ : DirichletCharacter ℂ N) (hθ : θ.IsPrimitive) (hN : N ≠ 1)
    (hlogN : Real.log (N : ℝ) ≤ 2 * lemma23PaperL D ^ 9)
    {s : ℂ} (hL : 3 ≤ lemma23PaperL D) (hs : Lemma51InExtendedRegion D s) :
    ‖(lemma23DirichletZ θ s)⁻¹‖ ≤ Real.exp (600 * Real.pi) := by
  have hh := lemma51_extended_region_data hL hs
  have hT : 0 < lemma51PaperT0 D := by unfold lemma51PaperT0; positivity
  have ht : 0 < s.im := hT.trans_le hh.2.2.1
  obtain ⟨H, hHnorm, hHd⟩ := lemma44_exists_horizontal_log_modulus
    (f := lemma23DirichletZ θ)
    (fun z hz => lemma23DirichletZ_differentiableAt_of_im_ne_zero θ (ne_of_gt hz))
    (fun z hz => lemma23DirichletZ_ne_zero_of_im_pos θ hθ hN hz) ht
  have hzero : H (1 / 2) = 0 := by
    have hn := lemma23DirichletZ_norm_eq_one_on_critical_line θ hθ hN
      (s := ((1 / 2 : ℝ) : ℂ) + I * (s.im : ℂ)) (by simp)
    apply Real.exp_injective
    rw [hHnorm, hn, Real.exp_zero]
  have hregion (x : ℝ) (hx : x ∈ uIcc (1 / 2) s.re) :
      Lemma51InExtendedRegion D ((x : ℂ) + I * (s.im : ℂ)) := by
    have ha := (lemma44_alpha_pos_le_one hL).1.le
    have hr := abs_le.mp hs.1
    have hlo : 1 / 2 - lemma44PaperAlpha D ≤ min (1 / 2) s.re :=
      le_min (by linarith) (by linarith)
    have hhi : max (1 / 2) s.re ≤ 1 / 2 + lemma44PaperAlpha D :=
      max_le (by linarith) (by linarith)
    have hxlo := hlo.trans hx.1
    have hxhi := hx.2.trans hhi
    simp only [Lemma51InExtendedRegion, add_re, ofReal_re, mul_re, I_re,
      ofReal_im, mul_zero, I_im, zero_mul, sub_zero, add_zero, add_im, mul_im, one_mul, zero_add]
    exact ⟨abs_le.mpr ⟨by linarith, by linarith⟩, hs.2⟩
  have hn (x : ℝ) (hx : x ∈ uIcc (1 / 2) s.re) :
      ‖(logDeriv (lemma23DirichletZ θ) ((x : ℂ) + I * (s.im : ℂ))).re‖ ≤
        600 * lemma23PaperL D ^ 9 := by
    rw [Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm _).trans
      (lemma51_DirichletZ_logDeriv_norm θ hθ hN hlogN hL (hregion x hx))
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (hHd x).hasDerivWithinAt) hn (convex_uIcc (1 / 2) s.re)
    left_mem_uIcc right_mem_uIcc
  rw [hzero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at hb
  have hmul := mul_le_mul_of_nonneg_left hs.1
    (by positivity : 0 ≤ 600 * lemma23PaperL D ^ 9)
  have he : lemma23PaperL D ^ 9 * lemma44PaperAlpha D = Real.pi := by
    simp only [lemma44PaperAlpha, lemma23PaperP, Real.log_exp]
    field_simp
  have hupper : -H s.re ≤ 600 * Real.pi := by
    have ha := neg_le_abs (H s.re)
    have hmul' : 600 * lemma23PaperL D ^ 9 * lemma44PaperAlpha D = 600 * Real.pi := by
      rw [mul_assoc, he]
    rw [hmul'] at hmul
    linarith
  have hsEq : (s.re : ℂ) + I * (s.im : ℂ) = s := by apply Complex.ext <;> simp
  have hhNorm := hHnorm s.re
  rw [hsEq] at hhNorm
  rw [norm_inv, ← hhNorm, ← Real.exp_neg]
  exact Real.exp_le_exp.mpr hupper


/-- The right contour is uniformly separated from every actual L-zero.
Criticality is obtained from Proposition 2.2, including for nearby zeros
outside the smaller strict zero window. -/
theorem lemma81_right_segment_zero_separation :
    ∃ D₀ : ℕ, ∀ {D p : ℕ} [NeZero p]
      (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p),
      D₀ ≤ D → Lemma23InPsi1 χ ψ → ∀ {s : ℂ},
      Lemma81OnRightSegment D s → Lemma59ZeroSeparated (D := D) ψ s 1 := by
  obtain ⟨C, hC, N, hprop⟩ := proposition22_proved
  refine ⟨max N lemma23SectionFourModulusThreshold, ?_⟩
  intro D p _ χ ψ hD hψ s hs ρ hz
  have hDN : N ≤ D := (le_max_left _ _).trans hD
  have hsection : lemma23SectionFourModulusThreshold ≤ D :=
    (le_max_right _ _).trans hD
  have hL := (lemma44_parameters_at_explicit_threshold hsection).1
  have ha := lemma44_alpha_pos_le_one hL
  have haquarter := lemma51_alpha_le_quarter hL
  simp only [one_mul]
  by_contra hsep
  have hnear : ‖s - ρ‖ < lemma44PaperAlpha D := lt_of_not_ge hsep
  have hre : |ρ.re - s.re| ≤ ‖s - ρ‖ := by
    simpa only [sub_re, abs_sub_comm] using Complex.abs_re_le_norm (s - ρ)
  have him : |ρ.im - s.im| ≤ ‖s - ρ‖ := by
    simpa only [sub_im, abs_sub_comm] using Complex.abs_im_le_norm (s - ρ)
  have hsre : |s.re - 1 / 2| = lemma44PaperAlpha D := by
    rw [hs.1]
    simpa using abs_of_nonneg ha.1.le
  have hρre : |ρ.re - 1 / 2| < 1 / 2 := by
    have ht := abs_add_le (ρ.re - s.re) (s.re - 1 / 2)
    rw [sub_add_sub_cancel, hsre] at ht
    linarith only [ht, hre, hnear, haquarter]
  have hρim : |ρ.im - (lemma23PaperCenter D).im| <
      lemma23PaperL D ^ 405 + 2 := by
    have ht := abs_add_le (ρ.im - s.im) (s.im - (lemma23PaperCenter D).im)
    rw [sub_add_sub_cancel] at ht
    linarith only [ht, him, hs.2, hnear, haquarter]
  have hzero : lemma48ActualProduct χ ψ ρ = 0 := by
    simp only [lemma48ActualProduct, hz, zero_mul]
  have hcritical := (hprop χ ψ hDN hψ).1 ρ ⟨hρre,hρim⟩ hzero
  have hr := Complex.abs_re_le_norm (s - ρ)
  rw [sub_re, hs.1, hcritical.1] at hr
  have he : 1 / 2 + lemma44PaperAlpha D - 1 / 2 = lemma44PaperAlpha D := by ring
  rw [he, abs_of_nonneg ha.1.le] at hr
  exact (not_lt_of_ge hr) hnear

/-- The exact algebraic branch product in Lemma 5.2 multiplies C by 1+e. -/
theorem lemma81_Ctilde_eq_C_mul_relative_error {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (Y : ℂ → ℂ) (c : ℝ) (s e : ℂ)
    (he : Y (s + lemma52PaperBetaOne D c) * Y (s + lemma52PaperBetaTwo D c) *
      Y (s + lemma52PaperBetaThree D c) / Y s =
      (((p : ℝ) * lemma51PaperT0 D : ℝ) : ℂ) ^ lemma52PaperBetaThree D c *
        (lemma23DirichletZ ψ s)⁻¹ * (1 + e)) :
    lemma81ActualCtilde D c ψ Y s = lemma81ActualC D c ψ s * (1 + e) := by
  calc
    _ = -I * (Y (s + lemma52PaperBetaOne D c) * Y (s + lemma52PaperBetaTwo D c) *
        Y (s + lemma52PaperBetaThree D c) / Y s) *
      (ψ.LFunction (s + lemma52PaperBetaOne D c) *
        ψ.LFunction (s + lemma52PaperBetaTwo D c) *
        ψ.LFunction (s + lemma52PaperBetaThree D c) / ψ.LFunction s) := by
      simp only [lemma81ActualCtilde, lemma23DirichletNormalizedM, lemma23NormalizedM,
        div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by rw [he]; unfold lemma81ActualC; ring

/-- The original replacement estimate on J(α). Both the constant and the
threshold are uniform over Ψ₁, all actual branches, and the whole closed
segment. The L-quotient estimate is proved in Lemma 5.9 and its all-zero
separation hypothesis is discharged above. -/
theorem lemma81_uniform_actual_kernel_replacement {c : ℝ} (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∃ D₀ : ℕ, ∀ {D p : ℕ} [NeZero p]
      (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p),
      D₀ ≤ D → Lemma23InPsi1 χ ψ → ∀ Y : ℂ → ℂ,
      Lemma23ActualBranch ψ Y → ∀ {s : ℂ}, Lemma81OnRightSegment D s →
      ‖lemma81ActualCtilde D c ψ Y s - lemma81ActualC D c ψ s‖ ≤
        K * lemma23PaperL D ^ (-114 : ℤ) *
          ‖ψ.LFunction (s + lemma52PaperBetaTwo D c) *
            ψ.LFunction (s + lemma52PaperBetaThree D c)‖ := by
  obtain ⟨Nsep,hsep⟩ := lemma81_right_segment_zero_separation
  obtain ⟨N52,h52⟩ := lemma52_for_every_positive_constant hc
  obtain ⟨CQ,hCQ,N59,h59⟩ := lemma59_proved c hc 1 (by norm_num)
  let K := lemma52ErrorConstant * Real.exp (600 * Real.pi) * CQ
  have hK : 0 < K := mul_pos
    (mul_pos lemma52_error_constant_pos (Real.exp_pos _)) hCQ
  refine ⟨K, hK,
    max (max Nsep N52) (max N59 lemma23SectionFourModulusThreshold), ?_⟩
  intro D p _ χ ψ hD hψ Y hY s hs
  have hDsep : Nsep ≤ D := (le_max_left _ _).trans ((le_max_left _ _).trans hD)
  have hD52 : N52 ≤ D := (le_max_right _ _).trans ((le_max_left _ _).trans hD)
  have hD59 : N59 ≤ D := (le_max_left _ _).trans ((le_max_right _ _).trans hD)
  have hsection : lemma23SectionFourModulusThreshold ≤ D :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hD)
  have hL := (lemma44_parameters_at_explicit_threshold hsection).1
  have hLp : 0 < lemma23PaperL D := by linarith only [hL]
  have ha := lemma44_alpha_pos_le_one hL
  have hsre : |s.re - 1 / 2| ≤ lemma44PaperAlpha D := by
    rw [hs.1]
    simpa using (abs_of_nonneg ha.1.le).le
  have hs51 : Lemma51InRegion D s := ⟨hsre, by linarith only [hs.2]⟩
  have hs59 : Lemma59InRegion D s := ⟨hsre, by linarith only [hs.2]⟩
  have hsExt : Lemma51InExtendedRegion D s := ⟨hsre, by
    linarith only [hs.2, pow_nonneg hLp.le 405]⟩
  have hlog := (lemma51_family_conductor_logs χ ψ hL hψ.1).1
  have hZ := lemma81_inverse_Z_norm_bound ψ hψ.1.2.1 hψ.1.1.ne_one hlog hL hsExt
  have hQ := h59 χ ψ hD59 hψ hs59 (hsep χ ψ hDsep hψ hs)
  obtain ⟨e,he,hfactor⟩ := (h52 D p ψ hD52 hψ.1).2 Y hY s hs51
  have hphase : ‖(((p : ℝ) * lemma51PaperT0 D : ℝ) : ℂ) ^
      lemma52PaperBetaThree D c‖ = 1 := by
    have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
    have hT : 0 < lemma51PaperT0 D := by unfold lemma51PaperT0; positivity
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (mul_pos hp hT)]
    simp [lemma52PaperBetaThree]
  have hC : ‖lemma81ActualC D c ψ s‖ ≤
      Real.exp (600 * Real.pi) * (CQ * lemma23PaperL D ^ 9) *
        ‖ψ.LFunction (s + lemma52PaperBetaTwo D c) *
          ψ.LFunction (s + lemma52PaperBetaThree D c)‖ := by
    have hEq : lemma81ActualC D c ψ s =
      -I * (((p : ℝ) * lemma51PaperT0 D : ℝ) : ℂ) ^ lemma52PaperBetaThree D c *
        (lemma23DirichletZ ψ s)⁻¹ *
        (ψ.LFunction (s + lemma52PaperBetaOne D c) / ψ.LFunction s) *
        (ψ.LFunction (s + lemma52PaperBetaTwo D c) *
          ψ.LFunction (s + lemma52PaperBetaThree D c)) := by
      unfold lemma81ActualC
      ring
    rw [hEq, norm_mul, norm_mul, norm_mul, norm_mul, norm_neg, norm_I, hphase,
      one_mul, one_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply mul_le_mul hZ _ (norm_nonneg _) (Real.exp_pos _).le
    simpa only [lemma52PaperBetaOne,lemma23PaperP,Real.log_exp] using hQ
  have hEq := lemma81_Ctilde_eq_C_mul_relative_error ψ Y c s e hfactor
  rw [hEq, show lemma81ActualC D c ψ s * (1 + e) - lemma81ActualC D c ψ s =
    lemma81ActualC D c ψ s * e by ring, norm_mul]
  apply (mul_le_mul hC he (norm_nonneg _) (by positivity)).trans_eq
  have hscale : lemma23PaperL D ^ 9 * lemma23PaperL D ^ (-123 : ℤ) =
      lemma23PaperL D ^ (-114 : ℤ) := by
    rw [← zpow_natCast (lemma23PaperL D) 9, ← zpow_add₀ hLp.ne']
    norm_num
  calc
    _ = K * (lemma23PaperL D ^ 9 * lemma23PaperL D ^ (-123 : ℤ)) *
      ‖ψ.LFunction (s + lemma52PaperBetaTwo D c) *
        ψ.LFunction (s + lemma52PaperBetaThree D c)‖ := by dsimp [K]; ring
    _ = _ := by rw [hscale]

end ZhangLS.Spec
