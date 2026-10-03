import ZhangLS.Spec.Proposition26EnergyObjects
import ZhangLS.Spec.Lemma34WeightedCauchy
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! The exact Gaussian/logarithmic cost of the original E₂ transfer.
Every polynomial, zero weight and interval is the original source object.
No arithmetic mean estimate is assumed or claimed. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex MeasureTheory Set Finset
open scoped Classical

noncomputable def proposition26ErrorGaussian (D : ℕ) (v : ℝ) : ℝ :=
  Real.exp (-(v^2)/(4*lemma23PaperL D^30))

lemma proposition26_error_gaussian_continuous (D : ℕ) :
    Continuous (proposition26ErrorGaussian D) := by
  unfold proposition26ErrorGaussian
  fun_prop

lemma proposition26_error_gaussian_integrable {D : ℕ} (hL : 0<lemma23PaperL D) :
    Integrable (proposition26ErrorGaussian D) := by
  convert integrable_exp_neg_mul_sq (show 0<(4*lemma23PaperL D^30)⁻¹ by positivity) using 1
  funext v
  unfold proposition26ErrorGaussian
  congr 1
  ring

lemma proposition26_error_gaussian_mass {D : ℕ} (hL : 0<lemma23PaperL D) :
    (∫ v : ℝ, proposition26ErrorGaussian D v) =
      2*Real.sqrt Real.pi*lemma23PaperL D^15 := by
  have he : proposition26ErrorGaussian D =
      (fun v : ℝ => Real.exp (-(4*lemma23PaperL D^30)⁻¹*v^2)) := by
    funext v
    unfold proposition26ErrorGaussian
    congr 1
    ring
  rw [he,integral_gaussian,div_inv_eq_mul,Real.sqrt_mul Real.pi_pos.le]
  have hs : Real.sqrt (4*lemma23PaperL D^30) = 2*lemma23PaperL D^15 := by
    rw [show 4*lemma23PaperL D^30 = (2*lemma23PaperL D^15)^2 by ring,
      Real.sqrt_sq (by positivity)]
  rw [hs]
  ring

lemma proposition26_error_finite_gaussian_mass {D : ℕ} (hL : 0<lemma23PaperL D) :
    (∫ v in (-(lemma23PaperL D^20))..(lemma23PaperL D^20),
      proposition26ErrorGaussian D v) ≤ 2*Real.sqrt Real.pi*lemma23PaperL D^15 := by
  rw [intervalIntegral.integral_of_le (neg_le_self (pow_nonneg hL.le 20))]
  exact (setIntegral_le_integral (proposition26_error_gaussian_integrable hL)
    (Filter.Eventually.of_forall (fun v => (Real.exp_pos _).le))).trans_eq
      (proposition26_error_gaussian_mass hL)

/-- Sharp Gaussian mass, with no floor term: the true E₂ square costs
2√π L⁻¹²¹ times the Gaussian-weighted square of the true short polynomial. -/
theorem proposition26_actual_E2_square {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ)
    (hL : 0<lemma23PaperL D) :
    lemma112ActualE2 χ ψ s ^ 2 ≤
      (2*Real.sqrt Real.pi*lemma23PaperL D^(-121:ℤ)) *
        (∫ v in (-(lemma23PaperL D^20))..(lemma23PaperL D^20),
          ‖lemma112ShortPolynomial χ ψ (s+I*(v:ℂ))‖^2 *
            proposition26ErrorGaussian D v) := by
  let H := lemma23PaperL D^20
  let μ := volume.restrict (Ioc (-H) H)
  let f := fun v : ℝ => ‖lemma112ShortPolynomial χ ψ (s+I*(v:ℂ))‖
  let w := proposition26ErrorGaussian D
  have hH : 0<H := pow_pos hL 20
  have hwc : Continuous w := proposition26_error_gaussian_continuous D
  have hfc : Continuous f := by
    dsimp [f]
    have hc := (lemma112_short_polynomial_differentiable χ ψ).continuous
    fun_prop
  have hw : Integrable w μ := (hwc.intervalIntegrable (-H) H).1
  have hfw : Integrable (fun v => f v*w v) μ := ((hfc.mul hwc).intervalIntegrable (-H) H).1
  have hf2w : Integrable (fun v => f v^2*w v) μ :=
    (((hfc.pow 2).mul hwc).intervalIntegrable (-H) H).1
  have hW : 0<∫ v, w v ∂μ := by
    rw [← intervalIntegral.integral_of_le (neg_le_self hH.le)]
    exact intervalIntegral.intervalIntegral_pos_of_pos (hwc.intervalIntegrable (-H) H)
      (fun v => Real.exp_pos _) (by linarith only [hH])
  have hc := lemma34_weighted_integral_cauchy μ f w hw hfw hf2w
    (Filter.Eventually.of_forall (fun v => (Real.exp_pos _).le)) hW
  have hm := proposition26_error_finite_gaussian_mass hL
  rw [intervalIntegral.integral_of_le (neg_le_self hH.le)] at hm
  have hsq : 0≤∫ v, f v^2*w v ∂μ :=
    integral_nonneg (fun v => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
  have hc' := hc.trans (mul_le_mul_of_nonneg_right hm hsq)
  have he : (lemma23PaperL D^(-68:ℤ))^2 *
      (2*Real.sqrt Real.pi*lemma23PaperL D^15) =
      2*Real.sqrt Real.pi*lemma23PaperL D^(-121:ℤ) := by
    simp only [zpow_neg,zpow_ofNat]
    field_simp [hL.ne']
  unfold lemma112ActualE2
  rw [mul_pow,intervalIntegral.integral_of_le (neg_le_self hH.le),
    intervalIntegral.integral_of_le (neg_le_self hH.le)]
  calc
    _ ≤ (lemma23PaperL D^(-68:ℤ))^2 *
        ((2*Real.sqrt Real.pi*lemma23PaperL D^15)*(∫ v, f v^2*w v ∂μ)) :=
      mul_le_mul_of_nonneg_left hc' (sq_nonneg _)
    _ = _ := by rw [← mul_assoc,he]

/-- Finite sum/integral interchange for the genuine weighted zero energy.
Weights are independent of the integration variable; no positivity or
arithmetic estimate is needed for this exact identity. -/
theorem proposition26_short_energy_integral {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (Y : (ψ : lemma33CharacterIndex D) → ℂ → ℂ) :
    (∑ ψ ∈ lemma81GoodFamily χ, ∑ ρ ∈ lemma81ZeroFinset D ψ.2,
      proposition26Weight c Y ψ ρ *
        (∫ v in (-(lemma23PaperL D^20))..(lemma23PaperL D^20),
          ‖lemma112ShortPolynomial χ ψ.2 (ρ+I*(v:ℂ))‖^2 *
            proposition26ErrorGaussian D v)) =
      ∫ v in (-(lemma23PaperL D^20))..(lemma23PaperL D^20),
        proposition26Energy χ c Y
          (fun ψ ρ => lemma112ShortPolynomial χ ψ.2 (ρ+I*(v:ℂ))) *
            proposition26ErrorGaussian D v := by
  have hf (ψ : lemma33CharacterIndex D) (ρ : ℂ) :
      Continuous (fun v : ℝ => proposition26Weight c Y ψ ρ *
        (‖lemma112ShortPolynomial χ ψ.2 (ρ+I*(v:ℂ))‖^2 *
          proposition26ErrorGaussian D v)) := by
    have hc := (lemma112_short_polynomial_differentiable χ ψ.2).continuous
    have hg := proposition26_error_gaussian_continuous D
    fun_prop
  simp only [proposition26Energy, Finset.sum_mul, mul_assoc]
  rw [intervalIntegral.integral_finsetSum]
  · apply sum_congr rfl
    intro ψ hψ
    rw [intervalIntegral.integral_finsetSum]
    · apply sum_congr rfl
      intro ρ hρ
      rw [intervalIntegral.integral_const_mul]
    · intro ρ hρ
      exact (hf ψ ρ).intervalIntegrable _ _
  · intro ψ hψ
    exact (continuous_finsetSum _ (fun ρ _ => hf ψ ρ)).intervalIntegrable _ _

/-- The actual E₂ mean is reduced with its proved full Gaussian/log cost.
The only extra input is positivity of the source weights, established
uniformly from the compatible c by proposition26_actual_weight_data. -/
theorem proposition26_actual_E2_energy {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (Y : (ψ : lemma33CharacterIndex D) → ℂ → ℂ)
    (hL : 0<lemma23PaperL D)
    (hw : ∀ ψ ∈ lemma81GoodFamily χ, ∀ ρ ∈ lemma81ZeroFinset D ψ.2,
      0≤proposition26Weight c Y ψ ρ) :
    (∑ ψ ∈ lemma81GoodFamily χ, ∑ ρ ∈ lemma81ZeroFinset D ψ.2,
      proposition26Weight c Y ψ ρ * lemma112ActualE2 χ ψ.2 ρ^2) ≤
      (2*Real.sqrt Real.pi*lemma23PaperL D^(-121:ℤ)) *
        (∫ v in (-(lemma23PaperL D^20))..(lemma23PaperL D^20),
          proposition26Energy χ c Y
            (fun ψ ρ => lemma112ShortPolynomial χ ψ.2 (ρ+I*(v:ℂ))) *
              proposition26ErrorGaussian D v) := by
  rw [← proposition26_short_energy_integral χ c Y]
  simp only [Finset.mul_sum]
  apply sum_le_sum
  intro ψ hψ
  apply sum_le_sum
  intro ρ hρ
  exact (mul_le_mul_of_nonneg_left (proposition26_actual_E2_square χ ψ.2 ρ hL)
    (hw ψ hψ ρ hρ)).trans_eq (by ring)

/-- The smoothed defect in exactly (11.6), using the real twist and the
inverse character evaluated at 1-s. -/
noncomputable def proposition26SmoothedDefect {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ) : ℂ :=
  letI : NeZero (D*p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  lemma112JtildeOne χ ψ s-lemma23DirichletZ (lemma44CharacterTwist χ ψ) s*
    lemma112JtildeTwo χ ψ⁻¹ (1-s)

/-- Complete analytic half of the (11.6) transfer: both the original L11.2
estimate and positivity are proved dependencies. Only the explicitly shown
actual polynomial-energy integral remains to be bounded arithmetically. -/
theorem proposition26_smoothed_energy_transfer :
    ∃ C : ℝ, 0<C ∧ ∀ c : ℝ, Lemma52CompatibleConstant c →
      ∃ N : ℕ, ∀ D : ℕ, N≤D → ∀ χ : RealPrimitiveCharacter D,
        ∀ Y : (ψ : lemma33CharacterIndex D) → ℂ → ℂ,
          (∀ ψ ∈ lemma81GoodFamily χ, Lemma23ActualBranch ψ.2 (Y ψ)) →
          proposition26Energy χ c Y (fun ψ s => proposition26SmoothedDefect χ ψ.2 s) ≤
            C*lemma23PaperL D^(-121:ℤ)*
              (∫ v in (-(lemma23PaperL D^20))..(lemma23PaperL D^20),
                proposition26Energy χ c Y
                  (fun ψ ρ => lemma112ShortPolynomial χ ψ.2 (ρ+I*(v:ℂ))) *
                    proposition26ErrorGaussian D v) := by
  obtain ⟨C,hC,N11,h11⟩ := lemma112_proved
  refine ⟨C^2*(2*Real.sqrt Real.pi),by positivity,?_⟩
  intro c hcompat
  obtain ⟨Nw,hw⟩ := proposition26_actual_weight_data hcompat
  refine ⟨max N11 (max Nw lemma23SectionFourModulusThreshold),?_⟩
  intro D hD χ Y hY
  have hD11 := (le_max_left _ _).trans hD
  have hDN := (le_max_right _ _).trans hD
  have hDw := (le_max_left _ _).trans hDN
  have hsection := (le_max_right _ _).trans hDN
  have hL : 0 < lemma23PaperL D := by
    linarith only [(lemma44_parameters_at_explicit_threshold hsection).1]
  have hdata := hw D hDw χ Y hY
  have he := proposition26_actual_E2_energy χ c Y hL
    (fun ψ hψ ρ hρ => (hdata ψ hψ ρ hρ).2.1)
  calc
    _ ≤ C^2*(∑ ψ∈lemma81GoodFamily χ, ∑ ρ∈lemma81ZeroFinset D ψ.2,
        proposition26Weight c Y ψ ρ*lemma112ActualE2 χ ψ.2 ρ^2) := by
      unfold proposition26Energy
      simp only [Finset.mul_sum]
      apply sum_le_sum
      intro ψ hψ
      apply sum_le_sum
      intro ρ hρ
      have hg := (lemma81_mem_good_family χ ψ).mp hψ
      have hz := (lemma81_mem_original_zero_finset ψ.2
        (lemma33_primitive_nonprincipal hg.1.1 ψ.2 hg.1.2.1) ρ).mp hρ
      have hr : Lemma112InRegion D ρ := ⟨(hdata ψ hψ ρ hρ).1,hz.1.2⟩
      have ha := h11 χ ψ.2 hD11 hg.1 hr
      have hsq := pow_le_pow_left₀ (norm_nonneg _) ha 2
      rw [mul_pow] at hsq
      exact (mul_le_mul_of_nonneg_left hsq (hdata ψ hψ ρ hρ).2.1).trans_eq (by ring)
    _ ≤ _ := by
      exact (mul_le_mul_of_nonneg_left he (sq_nonneg C)).trans_eq (by ring)

end ZhangLS.Spec
