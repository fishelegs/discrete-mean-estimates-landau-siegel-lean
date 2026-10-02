import ZhangLS.Spec.Lemma48ZeroRegion

/-! # Critical-line location, simplicity and separation in the full Ω

The closed-boundary version of Lemma 4.6 is applied after the actual
product reflection and thin-slab localization. Simplicity is transferred
from the normalized function to the actual Dirichlet L-product.
-/

namespace ZhangLS.Spec

open Complex ComplexConjugate

set_option maxHeartbeats 1000000

theorem proposition22_actual_product_analyticAt {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ (lemma48ActualProduct χ ψ) s := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  exact (lemma46_LFunction_analyticAt ψ hs).mul
    (lemma46_LFunction_analyticAt (lemma44CharacterTwist χ ψ) hs)

/-- All three local conclusions are about the actual product in the full
original Ω, including its left half and the closed thin-slab endpoints. -/
theorem proposition22_actual_zero_analysis {m c : ℝ}
    (hm : 0 < m) (hc : 0 < c) (hcmp : lemma46ModelErrorConstant < m * c)
    (hmodel : ∀ z : ℂ, 1 / 2 ≤ ‖z‖ → ‖z‖ ≤ 1 →
      m * (1 - ‖z‖) ≤ ‖lemma23ExponentialGapModel Real.pi z‖)
    {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    (hsmall : c * lemma44PaperAlpha D * lemma23PaperL D ≤ 1 / 2)
    {ρ : ℂ} (hρ : Lemma48InOmega D ρ) (hzero : lemma48ActualProduct χ ψ ρ = 0) :
    ρ.re = 1 / 2 ∧ deriv (lemma48ActualProduct χ ψ) ρ ≠ 0 ∧
      ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < lemma46InnerRadius D c →
        lemma48ActualProduct χ ψ (ρ + w) ≠ 0 := by
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have hslab := lemma48_actual_zero_in_thin_slab χ ψ hD hψ hρ hzero
  have hA : lemma45ActualA χ ψ ρ = 0 := by
    change lemma48ActualProduct χ ψ ρ / _ = 0
    rw [hzero, zero_div]
  have hbeta : ρ.re = 1 / 2 := by
    by_cases hre : 1 / 2 ≤ ρ.re
    · exact (lemma46_zero_analysis_at_contraction_closed hm hc hcmp hmodel χ ψ hD hψ
        hsmall hre (by linarith [(abs_le.mp hslab).2]) hρ.2 hA).1
    · have hrΩ := lemma48_omega_reflection hρ
      have hrP := lemma48_actual_product_reflected_zero χ ψ hL hψ.1
        (lemma48_omega_height_pos hL hρ) hzero
      have hrA : lemma45ActualA χ ψ (1 - conj ρ) = 0 := by
        change lemma48ActualProduct χ ψ (1 - conj ρ) / _ = 0
        rw [hrP, zero_div]
      have hr := lemma46_zero_analysis_at_contraction_closed hm hc hcmp hmodel χ ψ hD hψ
        hsmall (ρ := 1 - conj ρ)
        (by simp only [sub_re, one_re, conj_re]; linarith)
        (by simp only [sub_re, one_re, conj_re]; linarith [(abs_le.mp hslab).1])
        hrΩ.2 hrA
      have he := hr.1
      simp only [sub_re, one_re, conj_re] at he
      linarith
  have ha := (lemma46_alpha_parameters hD).1
  have hz := lemma46_zero_analysis_at_contraction_closed hm hc hcmp hmodel χ ψ hD hψ
    hsmall (by rw [hbeta]) (by rw [hbeta]; linarith [sq_nonneg (lemma44PaperAlpha D)]) hρ.2 hA
  have hreg := lemma48_thin_slab_regions hD hρ hslab
  have hF := lemma23_omega1_F_ne_zero χ ψ ρ hL hψ.2 hreg.2.1
  have hρne : ρ ≠ 1 := by intro he; rw [he] at hbeta; norm_num at hbeta
  have hpd := (proposition22_actual_product_analyticAt χ ψ hρne).differentiableAt
  have hfd := lemma44_short_polynomial_differentiable χ ψ ρ
  have hderiv : deriv (lemma45ActualA χ ψ) ρ =
      (deriv (lemma48ActualProduct χ ψ) ρ *
        lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p)) ρ -
        lemma48ActualProduct χ ψ ρ *
          deriv (lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p))) ρ) /
      lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p)) ρ ^ 2 :=
    deriv_div hpd hfd hF
  refine ⟨hbeta, ?_, ?_⟩
  · intro hd
    apply hz.2.1
    rw [hderiv, hd, hzero]
    simp
  · intro w hw hwR hzw
    have hcenter : (1 / 2 : ℂ) + I * (ρ.im : ℂ) = ρ := by
      apply Complex.ext <;> simp [hbeta]
    apply hz.2.2 w hw hwR
    rw [hcenter]
    change lemma48ActualProduct χ ψ (ρ + w) / _ = 0
    rw [hzw, zero_div]

end ZhangLS.Spec
