import ZhangLS.Spec.Lemma81WideCoarseBounds

/-! # Coarse actual shifted-L quotient on the wide deformation strip

The exact finite local zero product, proved simple-zero structure and actual
zero-removed logarithmic bound give an exponential-in-L^9 bound. This is
sufficient on Gaussian-suppressed edges, without extending sharp Lemma 5.9.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Set
open scoped Real Classical
set_option maxHeartbeats 2000000

lemma lemma81_section_log_hundred {D : ℕ} (hD : lemma23SectionFourModulusThreshold ≤ D) :
    100 ≤ lemma23PaperL D := by
  have hp := lemma23_sectionFour_parameters_at_explicit_threshold hD
  have hh := Real.log_le_self (by linarith only [hp.1] : 0 ≤ lemma23PaperL D)
  linarith only [hp.2,hh]

lemma lemma81_wide_shift_path_near_center {D : ℕ} (hL : 100 ≤ lemma23PaperL D)
    {s : ℂ} (hs : Lemma81WideStrip D s) {δ x : ℝ}
    (hδ : 0 ≤ δ) (hδhi : δ ≤ lemma44PaperAlpha D) (hx : x ∈ Icc (0 : ℝ) 1) :
    ‖s+(x : ℂ)*(I*(δ : ℂ))-lemma55JensenCenter s.im‖ ≤ (25/16 : ℝ) := by
  have ha := lemma59_alpha_bounds hL
  have hi : (lemma23PaperL D)⁻¹ ≤ 1/100 := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 100) hL
  have ha100 : lemma44PaperAlpha D ≤ 1/100 := ha.2.le.trans hi
  have hre : |s.re-2| ≤ 3/2+lemma44PaperAlpha D := by
    apply abs_le.mpr
    constructor <;> linarith only [hs.1,hs.2.1,ha.1]
  have hxd : x*δ ≤ lemma44PaperAlpha D :=
    (mul_le_mul_of_nonneg_right hx.2 hδ).trans (by simpa using hδhi)
  have hn := Complex.norm_le_abs_re_add_abs_im
    (s+(x : ℂ)*(I*(δ : ℂ))-lemma55JensenCenter s.im)
  simp only [lemma55JensenCenter,sub_re,sub_im,add_re,add_im,mul_re,mul_im,I_re,I_im,
    ofReal_re,ofReal_im,zero_mul,mul_zero,one_mul,mul_one,sub_zero,add_zero,zero_add] at hn
  norm_num at hn
  rw [abs_of_nonneg hx.1,abs_of_nonneg hδ] at hn
  change ‖s+(x : ℂ)*(I*(δ : ℂ))-(2+(s.im : ℂ)*I)‖ ≤ (25/16 : ℝ)
  linarith only [hn,hre,hxd,ha100]

/-- Actual first-shift quotient on the wider contour-deformation strip. -/
theorem lemma81_uniform_wide_actual_quotient {c : ℝ} (hc : 0 < c) :
    ∃ N : ℕ, lemma23SectionFourModulusThreshold ≤ N ∧
      ∀ {D p : ℕ} [NeZero p] (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p),
      N ≤ D → Lemma23InPsi1 χ ψ → ∀ {s : ℂ}, Lemma81WideStrip D s →
      Lemma59ZeroSeparated (D := D) ψ s (1/4) →
      ‖ψ.LFunction (s+lemma52PaperBetaOne D c)/ψ.LFunction s‖ ≤
        Real.exp (166550*lemma23PaperL D^9) := by
  obtain ⟨cz,hcz,Nz,hzeros⟩ := lemma59_uniform_actual_local_zero_structure
  obtain ⟨Nc,hcount⟩ := lemma59_uniform_actual_local_zero_bound
  obtain ⟨Ns,hsection,hsmall⟩ := lemma52_exists_shift_threshold hc
  refine ⟨max Nz (max Nc Ns),hsection.trans ((le_max_right Nc Ns).trans (le_max_right Nz _)),?_⟩
  intro D p _ χ ψ hD hψ s hs hsep
  have hDz := (le_max_left Nz (max Nc Ns)).trans hD
  have hDc := (le_max_left Nc Ns).trans ((le_max_right Nz (max Nc Ns)).trans hD)
  have hDs := (le_max_right Nc Ns).trans ((le_max_right Nz (max Nc Ns)).trans hD)
  have hL := lemma81_section_log_hundred (hsection.trans hDs)
  have hL3 : 3 ≤ lemma23PaperL D := by linarith only [hL]
  have hLp : 0 < lemma23PaperL D := by linarith only [hL]
  have ha := (lemma44_alpha_pos_le_one hL3).1
  have hθ := lemma59_family_character_nonprincipal ψ hψ.1
  let S := lemma59LocalZeroFinset ψ s.im
  let δ := lemma23PaperOffsetOne D c
  have hb : 0 < δ ∧ δ ≤ lemma44PaperAlpha D :=
    lemma59_paper_offset_one_bounds hL hc (by nlinarith only [hsmall D hDs])
  have hδ1 : δ ≤ 1 := hb.2.trans (lemma44_alpha_pos_le_one hL3).2
  have hw : ‖I*(δ : ℂ)‖ = δ := by
    rw [norm_mul,norm_I,Complex.norm_real,Real.norm_of_nonneg hb.1.le,one_mul]
  have hz := hzeros χ ψ hDz hψ (t := s.im) (by linarith only [hs.2.2])
  have hcard : (S.card : ℝ) ≤ 30*lemma23PaperL D^9 :=
    (hcount χ ψ hDc hψ (t := s.im) (by linarith only [hs.2.2])).2
  have hterm (ρ : ℂ) (hρ : ρ ∈ S) : ‖(s+I*(δ : ℂ)-ρ)/(s-ρ)‖ ≤ 5 := by
    have hzero := ((lemma59_mem_actual_local_zero_finset ψ hθ s.im ρ).mp hρ).2
    have hd := hsep ρ hzero
    have hdp : 0 < ‖s-ρ‖ := by nlinarith only [hd,ha]
    rw [norm_div]
    apply (div_le_iff₀ hdp).mpr
    have he : s+I*(δ : ℂ)-ρ = (s-ρ)+I*(δ : ℂ) := by ring
    rw [he]
    have hn := norm_add_le (s-ρ) (I*(δ : ℂ))
    rw [hw] at hn
    nlinarith only [hn,hd,hb.2]
  have hprod : ‖∏ ρ ∈ S, ((s+I*(δ : ℂ)-ρ)/(s-ρ)) ^ analyticOrderNatAt ψ.LFunction ρ‖ ≤
      Real.exp (150*lemma23PaperL D^9) := by
    rw [norm_prod]
    calc
      _ = ∏ ρ ∈ S, ‖(s+I*(δ : ℂ)-ρ)/(s-ρ)‖ := by
        apply Finset.prod_congr rfl
        intro ρ hρ
        rw [(hz.2.2 ρ hρ).2.1,pow_one]
      _ ≤ ∏ _ρ ∈ S, (5 : ℝ) := Finset.prod_le_prod (fun _ _ => norm_nonneg _) hterm
      _ = (5 : ℝ)^S.card := by simp
      _ = Real.exp ((S.card : ℝ)*Real.log 5) := by
        simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 5)] using
          (Real.exp_nat_mul (Real.log 5) S.card).symm
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hh := mul_le_mul_of_nonneg_left (Real.log_le_self (by norm_num : (0 : ℝ) ≤ 5))
          (Nat.cast_nonneg S.card : (0 : ℝ) ≤ S.card)
        nlinarith only [hh,hcard]
  have hQ := lemma59_actual_zero_removed_shift_norm_bound ψ hθ
    (fun x hx => lemma81_wide_shift_path_near_center hL hs hb.1.le hb.2 hx)
  have hlog : lemma59JensenLogSize ψ s.im ≤ 2*lemma23PaperL D^9 :=
    lemma59_family_large_disk_log_budget ψ hL hψ.1 (by linarith only [hs.2.2])
  have hQbound : ‖lemma59ZeroRemovedL ψ s.im (s+I*(δ : ℂ))/lemma59ZeroRemovedL ψ s.im s‖ ≤
      Real.exp (166400*lemma23PaperL D^9) := by
    apply hQ.trans
    rw [hw]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul hlog hδ1 hb.1.le (by positivity : 0 ≤ 2*lemma23PaperL D^9)
    nlinarith only [hh]
  change ‖ψ.LFunction (s+I*(δ : ℂ))/ψ.LFunction s‖ ≤ _
  rw [lemma59_actual_L_quotient_factorization ψ hθ s.im s (I*(δ : ℂ)),
    lemma59_actual_zero_factor_ratio_eq_product ψ hθ s.im s (I*(δ : ℂ)),norm_mul]
  apply (mul_le_mul hprod hQbound (norm_nonneg _) (Real.exp_nonneg _)).trans_eq
  rw [← Real.exp_add]
  congr 1
  ring

end ZhangLS.Spec
