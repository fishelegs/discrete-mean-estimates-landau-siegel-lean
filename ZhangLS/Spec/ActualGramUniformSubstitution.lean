import ZhangLS.Spec.ActualGramUniformGeometry
import ZhangLS.Spec.ActualGramUniformEnvelopes

/-! A single threshold substitutes proved actual arithmetic estimates into
all four slots of the weighted profile assembly. Fixed profile data and
bounds precede the threshold; D, character, j and the finite indices follow it. -/
set_option autoImplicit false
set_option maxHeartbeats 3500000
namespace ZhangLS.Spec
open Complex Set Finset
open scoped Classical Interval

noncomputable def actualGramUniformFirstNorm (D : ℕ) (C : ℝ) : ℝ :=
  C*lemma84CompanionConstant*lemma23PaperL D^3 / Real.log (lemma23PaperP D)

noncomputable def actualGramUniformFirstError (D : ℕ) (C : ℝ) : ℝ :=
  C*actualGramUniformFirstBoundaryConstant*(Real.log (lemma56PaperT D))^3 /
      (Real.log (lemma23PaperP D))^2 +
    C*lemma82ErrorConstant*lemma23PaperL D^(-6:ℤ) / Real.log (lemma23PaperP D)

noncomputable def actualGramUniformSecondError (D : ℕ) (C : ℝ) : ℝ :=
  C*actualGramUniformSecondBoundaryConstant*(1+9*Real.log (lemma23PaperL D))^actualGramUniformExponent*
      (Real.log (lemma56PaperT D))^5 / (Real.log (lemma23PaperP D))^2 +
    C*3*lemma23PaperL D^(-5:ℤ) / Real.log (lemma23PaperP D)

noncomputable def actualGramUniformSecondMain (D : ℕ) (C : ℝ) : ℝ :=
  C*actualGramUniformMainConstant*(1+9*Real.log (lemma23PaperL D))^actualGramUniformExponent*
    lemma23PaperL D^2 / Real.log (lemma23PaperP D)

lemma actualGramUniform_envelopes_nonneg {D : ℕ} (hL : 1 ≤ lemma23PaperL D)
    {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ actualGramUniformFirstNorm D C ∧ 0 ≤ actualGramUniformFirstError D C ∧
    0 ≤ actualGramUniformSecondError D C ∧ 0 ≤ actualGramUniformSecondMain D C := by
  have hB : 0 ≤ Real.log (lemma23PaperP D) := by
    rw [lemma23PaperP,Real.log_exp]
    positivity
  have hR := (actualGramUniform_scale_bounds hL).1
  have hH := (actualGramUniform_scale_bounds hL).2.1
  unfold actualGramUniformFirstNorm actualGramUniformFirstError
    actualGramUniformSecondError actualGramUniformSecondMain
  exact ⟨by positivity [lemma84_companion_constant_pos],
    by positivity [actualGramUniform_first_boundary_constant_pos,lemma82_error_constant_pos],
    by positivity [actualGramUniform_second_boundary_constant_pos],
    by positivity [actualGramUniform_main_constant_pos]⟩

theorem actualGramUniform_four_bounds (c : ℝ) (hc : 0 < c)
    (f f' f'' g g' g'' : ℝ → ℂ) (b C : ℝ)
    (hb0 : 0 ≤ b) (hb : b ≤ 201/400) (hC : 0 ≤ C)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'' : Continuous f'') (hfz : ∀ v, b ≤ v → f v = 0) (hft : f' b = 0)
    (hg : ∀ x, HasDerivAt g (g' x) x) (hg' : ∀ x, HasDerivAt g' (g'' x) x)
    (hg'' : Continuous g'') (hgz : ∀ v, b ≤ v → g v = 0) (hgt : g' b = 0)
    (hfd : ∀ v, ‖actualGramRampDensity (3*I*(Real.pi : ℂ)/2) f f' f'' v‖ ≤ C)
    (hgd : ∀ v, ‖actualGramRampDensity (-(3*I*(Real.pi : ℂ)/2)) g g' g'' v‖ ≤ C)
    (hg0 : ∀ v, ‖g v‖ ≤ C) (hg1 : ∀ v, ‖g' v‖ ≤ C) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ D : ℕ, N ≤ D → 2000 ≤ lemma23PaperL D ∧
      ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ → ∀ j : Fin 3,
      ∀ dr ∈ actualGramUniformPairs D (Real.log (lemma23PaperP D)) b,
      (‖actualGramFirst χ c j (fun n => f (Real.log n / Real.log (lemma23PaperP D)))
          (dr.1*dr.2)‖ ≤ actualGramUniformFirstNorm D C) ∧
      (‖actualGramFirst χ c j (fun n => f (Real.log n / Real.log (lemma23PaperP D)))
          (dr.1*dr.2) - actualGramFirstProfileMain χ c j (Real.log (lemma23PaperP D))
            f f' (dr.1*dr.2)‖ ≤ actualGramUniformFirstError D C) ∧
      (‖actualGramSecond χ c j (fun n => g (Real.log n / Real.log (lemma23PaperP D)))
          dr.1 dr.2 - actualGramSecondProfileMain χ c j (Real.log (lemma23PaperP D))
            b g g' dr.1 dr.2‖ ≤ actualGramUniformSecondError D C) ∧
      (‖actualGramSecondProfileMain χ c j (Real.log (lemma23PaperP D))
          b g g' dr.1 dr.2‖ ≤ actualGramUniformSecondMain D C) := by
  obtain ⟨NF,hNF,hF⟩ := actualGram_first_profile_norm_uniform c hc
  obtain ⟨NE,hNE,hE⟩ := actualGram_first_profile_error_uniform c hc
  obtain ⟨NG,hNG,hG⟩ := actualGram_second_profile_error_uniform c hc
  obtain ⟨NP,hNP,hP⟩ := lemma82_uniform_threshold c hc
  refine ⟨max (max NF NE) (max NG NP), hNF.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro D hDN
  have hDF : NF ≤ D := (le_max_left _ _).trans ((le_max_left _ _).trans hDN)
  have hDE : NE ≤ D := (le_max_right _ _).trans ((le_max_left _ _).trans hDN)
  have hDG : NG ≤ D := (le_max_left _ _).trans ((le_max_right _ _).trans hDN)
  have hDP : NP ≤ D := (le_max_right _ _).trans ((le_max_right _ _).trans hDN)
  have hp := hP D hDP
  have hL : 2000 ≤ lemma23PaperL D := hp.2.1
  have hD : 1 < D := by omega
  have hB : 0 < Real.log (lemma23PaperP D) := actualGram_original_log_scale_pos hD
  have hL1 : 1 ≤ lemma23PaperL D := by linarith
  have hL100 : 100 ≤ lemma23PaperL D := by linarith
  have hH := (actualGramUniform_scale_bounds hL1).2.1
  have hR := (actualGramUniform_scale_bounds hL1).1
  have hb1 : b ≤ 1 := by linarith
  refine ⟨hL, ?_⟩
  intro χ hA j dr hdr
  obtain ⟨hd,hr,ht0,htb,hq⟩ := actualGramUniform_pair_geometry D hB dr hdr
  have hceil := actualGramUniform_support_ceiling (by linarith : 3 ≤ lemma23PaperL D) hb
  have hcut := actualGram_profile_inner_cutoffs D hB hceil (dr.1*dr.2) (Nat.mul_pos hd hr) htb
  have hprod : (dr.1*dr.2 : ℝ) < lemma23PaperP D*lemma56PaperT D^(-2:ℤ) := by
    simpa only [Nat.cast_mul,lemma81Cutoff] using hcut.1
  have hlen : b-Real.log (dr.1*dr.2 : ℕ)/Real.log (lemma23PaperP D) ≤ 1 := by linarith
  have hcut' := fun v hv => (hcut.2 v hv).2
  have hFn := hF D hDF χ hA j (dr.1*dr.2) (Nat.mul_pos hd hr)
    f f' f'' b C hC hf hf' hf'' hfz hft htb (fun v _ => hfd v) hcut'
  have hFe := hE D hDE χ hA j (dr.1*dr.2) (Nat.mul_pos hd hr)
    f f' f'' b C hC hf hf' hf'' hfz hft htb (fun v _ => hfd v) hcut'
  have hGe := hG D hDG χ hA j dr.1 dr.2 hd hr hprod
    g g' g'' b C hC hg hg' hg'' hgz hgt htb (fun v _ => hgd v) hcut'
  have hGm := actualGram_second_profile_main_norm χ hD hL hc hp.2.2.1 j dr.1 dr.2
    g g' ht0 htb hb1 hC (fun v _ => hg0 v) (hg1 _)
  have hFb := actualGramUniform_first_boundary_bound hL1
  have hGb := actualGramUniform_second_boundary_bound χ hL100 dr.1 dr.2 hd hr hprod
  have hPi := actualGramUniform_pi_bound χ hL100 dr.1 dr.2 hd hr hprod
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply hFn.trans
    unfold actualGramUniformFirstNorm
    exact div_le_div_of_nonneg_right
      ((mul_le_mul_of_nonneg_left hlen (by positivity [lemma84_companion_constant_pos])).trans_eq (by ring)) hB.le
  · change ‖_ - (LDerivAtOne χ / (Real.log (lemma23PaperP D) : ℂ))*
      (-f' _-(Real.log (lemma23PaperP D) : ℂ)*lemma83PaperBeta D c j*f _)‖ ≤ _
    apply hFe.trans
    have hbound := add_le_add
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hFb hC)
        (div_nonneg (show 0 ≤ Real.log (lemma56PaperT D) by linarith) hB.le))
      (mul_le_mul_of_nonneg_left hlen (show 0 ≤ C*lemma82ErrorConstant*lemma23PaperL D^(-6:ℤ) by positivity [lemma82_error_constant_pos]))
    apply (div_le_div_of_nonneg_right hbound hB.le).trans_eq
    unfold actualGramUniformFirstError
    field_simp [hB.ne'] <;> ring
  · change ‖_ - (LDerivAtOne χ*lemma83Pi χ dr.1 dr.2 / (Real.log (lemma23PaperP D) : ℂ))*
      (-g' _ + ((Real.log (lemma23PaperP D) : ℂ)*lemma83PaperBeta D c (j+1)+
        (Real.log (lemma23PaperP D) : ℂ)*lemma83PaperBeta D c (j+2))*g _+
        ((Real.log (lemma23PaperP D) : ℂ)*lemma83PaperBeta D c (j+1))*
        ((Real.log (lemma23PaperP D) : ℂ)*lemma83PaperBeta D c (j+2))*
        (∫ u in Real.log (dr.1*dr.2 : ℕ)/Real.log (lemma23PaperP D)..b, g u))‖ ≤ _
    apply hGe.trans
    have hbound := add_le_add
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hGb hC)
        (div_nonneg (show 0 ≤ Real.log (lemma56PaperT D) by linarith) hB.le))
      (mul_le_mul_of_nonneg_left hlen (show 0 ≤ C*3*lemma23PaperL D^(-5:ℤ) by positivity))
    apply (div_le_div_of_nonneg_right hbound hB.le).trans_eq
    unfold actualGramUniformSecondError
    field_simp [hB.ne'] <;> ring
  · change ‖(LDerivAtOne χ*lemma83Pi χ dr.1 dr.2 / (Real.log (lemma23PaperP D) : ℂ))*
      (-g' _ + ((Real.log (lemma23PaperP D) : ℂ)*lemma83PaperBeta D c (j+1)+
        (Real.log (lemma23PaperP D) : ℂ)*lemma83PaperBeta D c (j+2))*g _+
        ((Real.log (lemma23PaperP D) : ℂ)*lemma83PaperBeta D c (j+1))*
        ((Real.log (lemma23PaperP D) : ℂ)*lemma83PaperBeta D c (j+2))*
        (∫ u in Real.log (dr.1*dr.2 : ℕ)/Real.log (lemma23PaperP D)..b, g u))‖ ≤ _
    apply hGm.trans
    have hbound := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hPi (show 0 ≤ 16*Real.exp 1*lemma23PaperL D^2 by positivity)) hB.le)
      (show 0 ≤ C*(1+8*Real.pi+16*Real.pi^2) by positivity)
    apply hbound.trans_eq
    unfold actualGramUniformSecondMain actualGramUniformMainConstant
    ring

end ZhangLS.Spec
