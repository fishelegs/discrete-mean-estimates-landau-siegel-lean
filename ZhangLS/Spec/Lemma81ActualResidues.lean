import ZhangLS.Spec.Lemma81IntegrandAnalytic

/-! # Actual simple-zero principal parts and residues in Lemma 8.1

The actual C*(ρ,ψ) is recovered from the actual derivative of M. Its residue
identity is proved, not supplied as an assumption. The pole-removed local
remainder is proved analytic using divided differences.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex ComplexConjugate Set MeasureTheory Filter
open scoped Real Topology
set_option maxHeartbeats 2000000

lemma lemma81_analyticAt_dslope_same {f : ℂ → ℂ} {ρ : ℂ} (hf : AnalyticAt ℂ f ρ) :
    AnalyticAt ℂ (dslope f ρ) ρ := by
  obtain ⟨p,hp⟩ := hf
  exact ⟨p.fslope,hp.has_fpower_series_dslope_fslope⟩

noncomputable def lemma81SimplePoleRegularPart (N M : ℂ → ℂ) (ρ : ℂ) : ℂ → ℂ :=
  dslope (fun s => N s / dslope M ρ s) ρ

lemma lemma81_simple_pole_regular_part_analytic {N M : ℂ → ℂ} {ρ : ℂ}
    (hN : AnalyticAt ℂ N ρ) (hM : AnalyticAt ℂ M ρ) (hd : deriv M ρ ≠ 0) :
    AnalyticAt ℂ (lemma81SimplePoleRegularPart N M ρ) ρ := by
  apply lemma81_analyticAt_dslope_same
  exact hN.div (lemma81_analyticAt_dslope_same hM) (by simpa only [dslope_same] using hd)

lemma lemma81_simple_zero_div_eq {N M : ℂ → ℂ} {ρ s : ℂ} (hzero : M ρ = 0) :
    N s / M s = (N s / dslope M ρ s) / (s-ρ) := by
  have he := sub_smul_dslope M ρ s
  simp only [smul_eq_mul,hzero,sub_zero] at he
  rw [← he]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

lemma lemma81_simple_zero_principal_part {N M : ℂ → ℂ} {ρ s : ℂ}
    (hzero : M ρ = 0) (hs : s ≠ ρ) :
    N s / M s = (N ρ / deriv M ρ) / (s-ρ) + lemma81SimplePoleRegularPart N M ρ s := by
  rw [lemma81_simple_zero_div_eq hzero]
  unfold lemma81SimplePoleRegularPart
  rw [dslope_of_ne (fun z => N z / dslope M ρ z) hs,slope_def_field,dslope_same]
  ring

lemma lemma81_simple_zero_residue_tendsto {N M : ℂ → ℂ} {ρ : ℂ}
    (hN : ContinuousAt N ρ) (hM : HasDerivAt M (deriv M ρ) ρ)
    (hzero : M ρ = 0) (hd : deriv M ρ ≠ 0) :
    Tendsto (fun s => (s-ρ) * (N s / M s)) (𝓝[≠] ρ) (𝓝 (N ρ / deriv M ρ)) := by
  have hl := (hN.tendsto.mono_left nhdsWithin_le_nhds).div hM.tendsto_slope hd
  have he : (fun s => N s / slope M ρ s) = (fun s => (s-ρ) * (N s / M s)) := by
    funext s
    simp only [slope_def_field,hzero,sub_zero,div_eq_mul_inv,mul_inv_rev,inv_inv]
    ring
  change Tendsto (fun s => N s / slope M ρ s) (𝓝[≠] ρ) (𝓝 (N ρ / deriv M ρ)) at hl
  rw [he] at hl
  exact hl

noncomputable def lemma81ActualLocalRegularPart {p : ℕ} [NeZero p]
    (D : ℕ) (c : ℝ) (ψ : DirichletCharacter ℂ p) (Y : ℂ → ℂ)
    (a₁ a₂ : ℕ → ℂ) (ρ : ℂ) : ℂ → ℂ :=
  lemma81SimplePoleRegularPart (lemma81TildeNumerator D c ψ Y a₁ a₂)
    (lemma23DirichletNormalizedM ψ Y) ρ

noncomputable def lemma81ActualResidueWeight {p : ℕ} [NeZero p]
    (D : ℕ) (c : ℝ) (ψ : DirichletCharacter ℂ p) (Y : ℂ → ℂ)
    (a₁ a₂ : ℕ → ℂ) (ρ : ℂ) : ℂ :=
  lemma23ActualCoefficient ψ Y D c ρ * lemma81Polynomial D a₁ ψ ρ *
    lemma81Polynomial D a₂ ψ⁻¹ (1-ρ) * lemma81Omega D ρ

/-- The actual derivative quotient is exactly the original weighted C*,
including the Y-factor in M′(ρ) and all three original shifts. -/
lemma lemma81_actual_numerator_div_deriv {p : ℕ} [NeZero p]
    (D : ℕ) (c : ℝ) (ψ : DirichletCharacter ℂ p) (Y : ℂ → ℂ)
    (a₁ a₂ : ℕ → ℂ) (ρ : ℂ) :
    lemma81TildeNumerator D c ψ Y a₁ a₂ ρ / deriv (lemma23DirichletNormalizedM ψ Y) ρ =
      lemma81ActualResidueWeight D c ψ Y a₁ a₂ ρ := by
  unfold lemma81TildeNumerator lemma81ActualResidueWeight lemma23ActualCoefficient
    lemma23ComplexCoefficient criticalLinePoint lemma52PaperBetaOne lemma52PaperBetaTwo
    lemma52PaperBetaThree
  ring

/-- Uniform actual residue/principal-part theorem at every original zero.
All zeros and derivatives are genuine; simplicity is discharged from the
proved compatible Lemma 2.3 constant, not included in the hypotheses. -/
theorem lemma81_uniform_actual_simple_zero_residues :
    ∃ c : ℝ, 0 < c ∧ Lemma52CompatibleConstant c ∧ ∃ N : ℕ,
      ∀ {D p : ℕ} [NeZero p] (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p),
      N ≤ D → Lemma23InPsi1 χ ψ → ∀ Y : ℂ → ℂ, Lemma23ActualBranch ψ Y →
      ∀ a₁ a₂ : ℕ → ℂ, ∀ ρ ∈ lemma81ZeroFinset D ψ,
      AnalyticAt ℂ (lemma81ActualLocalRegularPart D c ψ Y a₁ a₂ ρ) ρ ∧
      Tendsto (fun s => (s-ρ) * lemma81TildeIntegrand D c ψ Y a₁ a₂ s)
        (𝓝[≠] ρ) (𝓝 (lemma81ActualResidueWeight D c ψ Y a₁ a₂ ρ)) ∧
      ∀ s : ℂ, s ≠ ρ → lemma81TildeIntegrand D c ψ Y a₁ a₂ s =
        lemma81ActualResidueWeight D c ψ Y a₁ a₂ ρ / (s-ρ) +
          lemma81ActualLocalRegularPart D c ψ Y a₁ a₂ ρ s := by
  obtain ⟨c,hc,hcompatible,_⟩ := lemma52_proved
  obtain ⟨Ncomp,hcomp⟩ := hcompatible
  obtain ⟨Nshift,hsection,hsmall⟩ := lemma52_exists_shift_threshold hc
  refine ⟨c,hc,⟨Ncomp,hcomp⟩,max Ncomp Nshift,?_⟩
  intro D p _ χ ψ hD hψ Y hY a₁ a₂ ρ hρ
  have hDcomp := (le_max_left Ncomp Nshift).trans hD
  have hDshift := (le_max_right Ncomp Nshift).trans hD
  have hL := (lemma44_parameters_at_explicit_threshold (hsection.trans hDshift)).1
  have hz := (lemma81_mem_original_zero_finset ψ
    (lemma59_family_character_nonprincipal ψ hψ.1) ρ).mp hρ
  have hρpos := lemma48_omega_height_pos hL (lemma23_zero_window_subset_omega hz.1)
  have hb := lemma52_offset_bounds hL hc (hsmall D hDshift)
  have h₁ : 0 < ρ.im + lemma23PaperOffsetOne D c := by linarith only [hρpos,hb.1.1]
  have h₂ : 0 < ρ.im + lemma23PaperOffsetTwo D c := by linarith only [hρpos,hb.2.1.1]
  have h₃ : 0 < ρ.im + lemma23PaperOffsetThree D c := by linarith only [hρpos,hb.2.2.1]
  have hN := lemma81_actual_tilde_numerator_analyticAt c ψ hψ.1.2.1 hψ.1.1.ne_one Y hY a₁ a₂ h₁ h₂ h₃
  have hM := lemma81_actual_M_analytic ψ hψ.1.2.1 hψ.1.1.ne_one Y hY ρ hρpos
  have hMd := ((hcomp χ ψ hDcomp hψ).2.2 Y hY ρ hz.1 hz.2).1
  have hMzero : lemma23DirichletNormalizedM ψ Y ρ = 0 := by
    simp only [lemma23DirichletNormalizedM,lemma23NormalizedM,hz.2,mul_zero]
  refine ⟨lemma81_simple_pole_regular_part_analytic hN hM hMd,?_,?_⟩
  · have ht := lemma81_simple_zero_residue_tendsto hN.continuousAt hM.differentiableAt.hasDerivAt hMzero hMd
    simpa only [← lemma81_tilde_integrand_eq_numerator_div,lemma81_actual_numerator_div_deriv] using ht
  · intro s hs
    rw [lemma81_tilde_integrand_eq_numerator_div,
      lemma81_simple_zero_principal_part hMzero hs,lemma81_actual_numerator_div_deriv]
    rfl

end ZhangLS.Spec
