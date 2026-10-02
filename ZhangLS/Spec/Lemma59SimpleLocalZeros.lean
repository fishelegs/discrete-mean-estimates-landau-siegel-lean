import ZhangLS.Spec.Lemma59ExtendedActualZeros

/-! # Full original actual L-function quotient for Lemma 5.9

Original Psi1, actual objects, original closed boundaries and all-zero
separation are retained. The final module proves the unchanged Lemma59Target.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Metric Set Filter MeromorphicOn Finset
open scoped ArithmeticFunction.zeta Interval Real Topology
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

lemma lemma59_actual_L_simple_of_product_simple {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) {ρ : ℂ}
    (hρ : ρ ≠ 1) (hz : DirichletCharacter.LFunction ψ ρ = 0)
    (hd : deriv (lemma48ActualProduct χ ψ) ρ ≠ 0) :
    deriv (DirichletCharacter.LFunction ψ) ρ ≠ 0 ∧
      analyticOrderNatAt (DirichletCharacter.LFunction ψ) ρ = 1 := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  have ha := lemma46_LFunction_analyticAt ψ hρ
  have hb := lemma46_LFunction_analyticAt (lemma44CharacterTwist χ ψ) hρ
  have he : deriv (lemma48ActualProduct χ ψ) ρ =
      deriv (DirichletCharacter.LFunction ψ) ρ * DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) ρ +
      DirichletCharacter.LFunction ψ ρ * deriv (DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ)) ρ :=
    deriv_mul ha.differentiableAt hb.differentiableAt
  have hn : deriv (DirichletCharacter.LFunction ψ) ρ ≠ 0 := by
    intro hh
    apply hd
    rw [he,hh,hz]
    simp
  refine ⟨hn,?_⟩
  simp [analyticOrderNatAt,ha.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hz hn]

lemma lemma59_uniform_actual_local_zero_structure :
    ∃ c : ℝ, 0 < c ∧ ∃ D₀ : ℕ,
    ∀ {D p : ℕ} [NeZero p] (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p),
    D₀ ≤ D → Lemma23InPsi1 χ ψ → ∀ {t : ℝ},
    |t - (lemma23PaperCenter D).im| ≤ lemma23PaperL D ^ 405 + 10 →
    lemma44PaperAlpha D / 2 ≤ lemma46InnerRadius D c ∧ 0 < lemma46InnerRadius D c ∧
    ∀ ρ ∈ lemma59LocalZeroFinset ψ t,
      ρ.re = 1 / 2 ∧ analyticOrderNatAt (DirichletCharacter.LFunction ψ) ρ = 1 ∧
      ∀ σ ∈ lemma59LocalZeroFinset ψ t, σ ≠ ρ → lemma46InnerRadius D c ≤ ‖σ - ρ‖ := by
  obtain ⟨c,hc,D₀,h⟩ := lemma59_uniform_extended_actual_product_zeros
  refine ⟨c,hc,D₀,?_⟩
  intro D p _ χ ψ hD hψ t ht
  have hθ := lemma59_family_character_nonprincipal ψ hψ.1
  have hall := h χ ψ hD hψ
  refine ⟨hall.1,hall.2.1,?_⟩
  intro ρ hρ
  have hm := (lemma59_mem_actual_local_zero_finset ψ hθ t ρ).mp hρ
  have hΩ := lemma59_actual_local_zeros_in_extended_region ψ hθ ht hρ
  have hp : lemma48ActualProduct χ ψ ρ = 0 := by
    change DirichletCharacter.LFunction ψ ρ * _ = 0
    rw [hm.2,zero_mul]
  have ha := hall.2.2 hΩ hp
  have hρ1 : ρ ≠ 1 := by intro he; rw [he] at ha; norm_num at ha
  have hs := lemma59_actual_L_simple_of_product_simple χ ψ hρ1 hm.2 ha.2.1
  refine ⟨ha.1,hs.2,?_⟩
  intro σ hσ hne
  by_contra hh
  have hw : 0 < ‖σ - ρ‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hz := ha.2.2 (σ - ρ) hw (lt_of_not_ge hh)
  have hmσ := (lemma59_mem_actual_local_zero_finset ψ hθ t σ).mp hσ
  apply hz
  rw [add_sub_cancel]
  change DirichletCharacter.LFunction ψ σ * _ = 0
  rw [hmσ.2,zero_mul]

lemma lemma59_critical_line_norm_eq_im_distance {ρ σ : ℂ}
    (hρ : ρ.re = 1 / 2) (hσ : σ.re = 1 / 2) : ‖σ - ρ‖ = |σ.im - ρ.im| := by
  apply le_antisymm
  · have h := Complex.norm_le_abs_re_add_abs_im (σ - ρ)
    simpa only [Complex.sub_re,Complex.sub_im,hσ,hρ,sub_self,abs_zero,zero_add] using h
  · simpa only [Complex.sub_im] using Complex.abs_im_le_norm (σ - ρ)

end ZhangLS.Spec
