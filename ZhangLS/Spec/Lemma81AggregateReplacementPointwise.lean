import ZhangLS.Spec.Lemma81GaussianMass
import ZhangLS.Spec.Lemma81ContourIntegrability

/-! # Actual aggregate kernel replacement before integration

Both original page-43 moments and the proved actual kernel replacement are
assembled over the genuine finite good-character family. The bound has the
required P²L^-78 scale and retains the original Gaussian weight.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Set
open scoped Real Classical
set_option maxHeartbeats 2000000

lemma lemma81_integrand_difference_factor {p : ℕ} [NeZero p]
    (D : ℕ) (c : ℝ) (ψ : DirichletCharacter ℂ p) (Y : ℂ → ℂ)
    (a₁ a₂ : ℕ → ℂ) (s : ℂ) :
    lemma81TildeIntegrand D c ψ Y a₁ a₂ s - lemma81CIntegrand D c ψ a₁ a₂ s =
      (lemma81ActualCtilde D c ψ Y s-lemma81ActualC D c ψ s) *
        (lemma81Polynomial D a₁ ψ s*lemma81Polynomial D a₂ ψ⁻¹ (1-s))*lemma81Omega D s := by
  unfold lemma81TildeIntegrand lemma81CIntegrand
  ring

/-- Uniform genuine-family replacement at every point of J(α). -/
theorem lemma81_uniform_aggregate_replacement_pointwise {c : ℝ} (hc : 0 < c)
    {B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ D : ℕ, N ≤ D →
      ∀ (χ : RealPrimitiveCharacter D) (a₁ a₂ : ℕ → ℂ),
      Lemma81AdmissibleSequence D B₁ a₁ → Lemma81AdmissibleSequence D B₂ a₂ →
      ∀ Y : (ψ : lemma33CharacterIndex D) → ℂ → ℂ,
      (∀ ψ ∈ lemma81GoodFamily χ, Lemma23ActualBranch ψ.2 (Y ψ)) →
      ∀ s : ℂ, Lemma81OnRightSegment D s →
      (∑ ψ ∈ lemma81GoodFamily χ,
        ‖lemma81TildeIntegrand D c ψ.2 (Y ψ) a₁ a₂ s-lemma81CIntegrand D c ψ.2 a₁ a₂ s‖) ≤
        C*lemma23PaperP D^2*lemma23PaperL D^(-78 : ℤ)*‖lemma81Omega D s‖ := by
  obtain ⟨K,hK,Nk,hkernel⟩ := lemma81_uniform_actual_kernel_replacement hc
  obtain ⟨CL,hCL,Nm,hmoment⟩ := lemma81_uniform_actual_shifted_L_product_moment hc
  let J := CL+lemma81FourthMomentConstant*B₁^2*B₂^2
  have hJ : 0 < J := by
    have hKp := lemma81_fourth_moment_constant_pos
    dsimp [J]
    positivity
  refine ⟨K*J,mul_pos hK hJ,max Nk (max Nm lemma23SectionFourModulusThreshold),?_⟩
  intro D hD χ a₁ a₂ ha₁ ha₂ Y hY s hs
  have hDk := (le_max_left Nk (max Nm lemma23SectionFourModulusThreshold)).trans hD
  have hDm := (le_max_left Nm lemma23SectionFourModulusThreshold).trans
    ((le_max_right Nk (max Nm lemma23SectionFourModulusThreshold)).trans hD)
  have hsection := (le_max_right Nm lemma23SectionFourModulusThreshold).trans
    ((le_max_right Nk (max Nm lemma23SectionFourModulusThreshold)).trans hD)
  have hL := (lemma44_parameters_at_explicit_threshold hsection).1
  have hLp : 0 < lemma23PaperL D := by linarith only [hL]
  have hσ : |s.re-1/2| ≤ lemma44PaperAlpha D := by
    rw [hs.1]
    simpa using (abs_of_pos (lemma44_alpha_pos_le_one hL).1).le
  let F := lemma81GoodFamily χ
  let U : lemma33CharacterIndex D → ℂ := fun ψ =>
    ψ.2.LFunction (s+lemma52PaperBetaTwo D c)*ψ.2.LFunction (s+lemma52PaperBetaThree D c)
  let V : lemma33CharacterIndex D → ℂ := fun ψ =>
    lemma81Polynomial D a₁ ψ.2 s*lemma81Polynomial D a₂ ψ.2⁻¹ (1-s)
  have hU : (∑ ψ ∈ F, ‖U ψ‖^2) ≤ CL*lemma23PaperP D^2*lemma23PaperL D^36 :=
    hmoment D hDm χ s hs
  have hV : (∑ ψ ∈ F, ‖V ψ‖^2) ≤
      lemma81FourthMomentConstant*B₁^2*B₂^2*lemma23PaperP D^2*lemma23PaperL D^36 :=
    lemma81_actual_A_product_second_moment hB₁ hB₂ hL χ a₁ a₂ ha₁ ha₂ hσ
  have hpoint (ψ : lemma33CharacterIndex D) (hψ : ψ ∈ F) :
      ‖lemma81TildeIntegrand D c ψ.2 (Y ψ) a₁ a₂ s-lemma81CIntegrand D c ψ.2 a₁ a₂ s‖ ≤
        (K*lemma23PaperL D^(-114 : ℤ)) * (‖U ψ‖^2+‖V ψ‖^2) * ‖lemma81Omega D s‖ := by
    have hg := (lemma81_mem_good_family χ ψ).mp hψ
    have hk := hkernel χ ψ.2 hDk hg (Y ψ) (hY ψ hψ) hs
    have huv : ‖U ψ‖*‖V ψ‖ ≤ ‖U ψ‖^2+‖V ψ‖^2 := by
      nlinarith only [sq_nonneg (‖U ψ‖-‖V ψ‖),sq_nonneg (‖U ψ‖+‖V ψ‖)]
    rw [lemma81_integrand_difference_factor,norm_mul,norm_mul]
    calc
      _ ≤ ((K*lemma23PaperL D^(-114 : ℤ))*‖U ψ‖)*‖V ψ‖*‖lemma81Omega D s‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hk (norm_nonneg _)) (norm_nonneg _)
      _ = (K*lemma23PaperL D^(-114 : ℤ))*(‖U ψ‖*‖V ψ‖)*‖lemma81Omega D s‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left huv (by positivity)) (norm_nonneg _)
  have hscale : lemma23PaperL D^(-114 : ℤ)*lemma23PaperL D^36 = lemma23PaperL D^(-78 : ℤ) := by
    rw [← zpow_natCast (lemma23PaperL D) 36,← zpow_add₀ hLp.ne']
    norm_num
  calc
    _ ≤ ∑ ψ ∈ F, (K*lemma23PaperL D^(-114 : ℤ))*(‖U ψ‖^2+‖V ψ‖^2)*‖lemma81Omega D s‖ :=
      Finset.sum_le_sum hpoint
    _ = (K*lemma23PaperL D^(-114 : ℤ))*
        ((∑ ψ ∈ F, ‖U ψ‖^2)+(∑ ψ ∈ F, ‖V ψ‖^2))*‖lemma81Omega D s‖ := by
      rw [← Finset.sum_mul,← Finset.mul_sum,Finset.sum_add_distrib]
    _ ≤ (K*lemma23PaperL D^(-114 : ℤ))*
        (CL*lemma23PaperP D^2*lemma23PaperL D^36+
          lemma81FourthMomentConstant*B₁^2*B₂^2*lemma23PaperP D^2*lemma23PaperL D^36)*‖lemma81Omega D s‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add hU hV) (by positivity)) (norm_nonneg _)
    _ = (K*J)*lemma23PaperP D^2*(lemma23PaperL D^(-114 : ℤ)*lemma23PaperL D^36)*‖lemma81Omega D s‖ := by
      dsimp [J]
      ring
    _ = _ := by rw [hscale]

end ZhangLS.Spec
