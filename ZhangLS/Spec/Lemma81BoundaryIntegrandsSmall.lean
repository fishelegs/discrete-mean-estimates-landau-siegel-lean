import ZhangLS.Spec.Lemma81GaussianBoundaryDecay

/-! # Uniformly negligible actual boundary integrands

The original Gaussian suppresses the proved actual wide/normalized kernels
and the original bounded-coefficient polynomials. Every constant is uniform
before epsilon and the D-threshold; no boundary estimate is assumed.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Set
open scoped Real Classical
set_option maxHeartbeats 2000000

lemma lemma81_boundary_integrand_envelope {D p : ℕ} {B₁ B₂ K : ℝ}
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hL : 3 ≤ lemma23PaperL D)
    (a₁ a₂ : ℕ → ℂ) (ha₁ : Lemma81AdmissibleSequence D B₁ a₁)
    (ha₂ : Lemma81AdmissibleSequence D B₂ a₂) (ψ : DirichletCharacter ℂ p)
    {s z : ℂ} (hr : |s.re-1/2| ≤ 1)
    (ht : lemma23PaperL D^405-1 ≤ |s.im-(lemma23PaperCenter D).im|)
    (hz : ‖z‖ ≤ Real.exp (K*lemma23PaperL D^9)) :
    ‖z*lemma81Polynomial D a₁ ψ s*lemma81Polynomial D a₂ ψ⁻¹ (1-s)*lemma81Omega D s‖ ≤
      (B₁*B₂)*Real.exp ((K+4)*lemma23PaperL D^9)*(2*Real.exp (-(lemma23PaperL D^10)/32)) := by
  have hA := lemma81_actual_A_product_coarse_bound hB₁ hB₂ hL a₁ a₂ ha₁ ha₂ ψ
    (by linarith only [(abs_le.mp hr).1] : -1 ≤ s.re)
    (by linarith only [(abs_le.mp hr).2] : s.re ≤ 2)
  have hΩ := lemma81_gaussian_boundary_decay_at hL hr ht
  have he : z*lemma81Polynomial D a₁ ψ s*lemma81Polynomial D a₂ ψ⁻¹ (1-s)*lemma81Omega D s =
      z*(lemma81Polynomial D a₁ ψ s*lemma81Polynomial D a₂ ψ⁻¹ (1-s))*lemma81Omega D s := by ring
  rw [he,norm_mul,norm_mul]
  apply (mul_le_mul (mul_le_mul hz hA (norm_nonneg _) (Real.exp_nonneg _)) hΩ
    (norm_nonneg _) (by positivity)).trans_eq
  have hP4 : lemma23PaperP D^4 = Real.exp (4*lemma23PaperL D^9) := by
    simpa only [lemma23PaperP,Nat.cast_ofNat] using (Real.exp_nat_mul (lemma23PaperL D^9) 4).symm
  rw [hP4]
  have hexp : Real.exp ((K+4)*lemma23PaperL D^9) =
      Real.exp (K*lemma23PaperL D^9)*Real.exp (4*lemma23PaperL D^9) := by
    rw [add_mul,Real.exp_add]
  rw [hexp]
  ring

/-- Both genuine integrands are uniformly tiny on their original Gaussian
boundary bands; the normal kernel also covers the whole strip to J(1). -/
theorem lemma81_uniform_actual_boundary_integrands_small {c : ℝ} (hc : 0 < c)
    {B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, lemma23SectionFourModulusThreshold ≤ N ∧
      ∀ {D p : ℕ} [NeZero p] (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p),
      N ≤ D → Lemma23InPsi1 χ ψ → ∀ a₁ a₂ : ℕ → ℂ,
      Lemma81AdmissibleSequence D B₁ a₁ → Lemma81AdmissibleSequence D B₂ a₂ →
      ∀ s : ℂ, Lemma81WideStrip D s → Lemma59ZeroSeparated (D := D) ψ s (1/4) →
      lemma23PaperL D^405-1 ≤ |s.im-(lemma23PaperCenter D).im| →
      ‖lemma81CIntegrand D c ψ a₁ a₂ s‖ ≤ ε ∧
      ∀ Y : ℂ → ℂ, Lemma23ActualBranch ψ Y → |s.re-1/2| ≤ lemma44PaperAlpha D →
        ‖lemma81TildeIntegrand D c ψ Y a₁ a₂ s‖ ≤ ε := by
  obtain ⟨Nc,hNc,hC⟩ := lemma81_uniform_wide_actual_C_growth hc
  obtain ⟨Nt,hNt,hT⟩ := lemma81_uniform_thin_actual_Ctilde_growth hc
  obtain ⟨Ne,hE⟩ := lemma81_uniform_boundary_envelope_small (mul_nonneg hB₁ hB₂)
    (by linarith only [lemma81_boundary_growth_constant_pos] : 0 ≤ lemma81BoundaryGrowthConstant+4) ε hε
  refine ⟨max Nc (max Nt Ne),hNc.trans (le_max_left _ _),?_⟩
  intro D p _ χ ψ hD hψ a₁ a₂ ha₁ ha₂ s hs hsep hband
  have hDc := (le_max_left Nc (max Nt Ne)).trans hD
  have hDt := (le_max_left Nt Ne).trans ((le_max_right Nc (max Nt Ne)).trans hD)
  have hDe := (le_max_right Nt Ne).trans ((le_max_right Nc (max Nt Ne)).trans hD)
  have hL := (lemma44_parameters_at_explicit_threshold (hNc.trans hDc)).1
  have hLp : 0 < lemma23PaperL D := by linarith only [hL]
  have hparam := lemma81_wide_strip_parameters hL hs
  have hCG : ‖lemma81ActualC D c ψ s‖ ≤ Real.exp (lemma81BoundaryGrowthConstant*lemma23PaperL D^9) := by
    apply (hC χ ψ hDc hψ hs hsep).trans
    apply Real.exp_le_exp.mpr
    have hk : 170000 ≤ lemma81BoundaryGrowthConstant := by
      unfold lemma81BoundaryGrowthConstant
      linarith only [lemma52_error_constant_pos]
    exact mul_le_mul_of_nonneg_right hk (pow_nonneg hLp.le 9)
  constructor
  · exact (lemma81_boundary_integrand_envelope hB₁ hB₂ hL a₁ a₂ ha₁ ha₂ ψ hparam.2.1 hband hCG).trans
      (hE D hDe)
  · intro Y hY hthin
    have hTG := hT χ ψ hDt hψ Y hY hthin hs.2.2 hsep
    exact (lemma81_boundary_integrand_envelope hB₁ hB₂ hL a₁ a₂ ha₁ ha₂ ψ hparam.2.1 hband hTG).trans
      (hE D hDe)

end ZhangLS.Spec
