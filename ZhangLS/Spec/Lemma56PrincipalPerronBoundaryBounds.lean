import ZhangLS.Spec.Lemma56PrincipalPerronContour
import ZhangLS.Spec.Lemma56ZetaOffRealLogDerivative

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set Metric
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

lemma lemma56_actual_principal_perron_arithmetic_eq (B x : ℝ) (s : ℂ) :
    lemma56PrincipalPerronArithmeticIntegrand B x s =
      lemma56PerronArithmeticIntegrand (1 : DirichletCharacter ℂ 1) B x 0 s := by
  simp only [lemma56PrincipalPerronArithmeticIntegrand, lemma56PerronComplexKernel,
    lemma56PerronArithmeticIntegrand, DirichletCharacter.LFunction_modOne_eq,
    ofReal_zero, zero_mul, sub_zero]

theorem lemma56_uniform_principal_perron_left_bound :
    ∃ D₀ : ℕ, ∀ {D : ℕ} (χ : RealPrimitiveCharacter D),
      D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
      ∀ {B x H : ℝ}, 0 < B → 0 < x → 0 ≤ H → H ≤ D →
        let a := 1 - 1 / Real.log (D : ℝ)
        ‖∫ t : ℝ in -H..H, lemma56PrincipalPerronArithmeticIntegrand B x ((a : ℂ) + (t : ℂ) * I)‖ ≤
          6 * (18 * Real.log (D : ℝ) ^ 2 + 21601 * Real.log (D : ℝ)) *
            x ^ a * Real.exp (a ^ 2 / (4 * B ^ 2)) * Real.log (1 + H) := by
  obtain ⟨Dz, hz⟩ := lemma56_uniform_zeta_left_logDeriv_bound
  obtain ⟨Dr, hr⟩ := lemma55_uniform_repulsion_modulus_threshold
  refine ⟨max Dz Dr, ?_⟩
  intro D χ hDN hD hA B x H hB hx hH hHD
  have hL := (hr D ((le_max_right _ _).trans hDN)).1
  have hLp : 0 < Real.log (D : ℝ) := by linarith only [hL]
  have hinv : 1 / Real.log (D : ℝ) ≤ (1 / 2 : ℝ) := by
    apply (div_le_div_iff₀ hLp (by norm_num)).mpr
    linarith only [hL]
  simp_rw [lemma56_actual_principal_perron_arithmetic_eq]
  apply lemma56_perron_vertical_integral_bound (1 : DirichletCharacter ℂ 1) hB hx hH
    (by positivity : 0 ≤ 18 * Real.log (D : ℝ) ^ 2 + 21601 * Real.log (D : ℝ))
    (by linarith only [hinv]) 0
  intro t ht
  simpa only [DirichletCharacter.LFunction_modOne_eq, ofReal_zero, zero_mul, sub_zero] using
    hz χ ((le_max_left _ _).trans hDN) hD hA t (ht.trans hHD)

theorem lemma56_uniform_principal_perron_horizontal_bound :
    ∃ D₀ : ℕ, ∀ {D : ℕ} (χ : RealPrimitiveCharacter D),
      D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
      ∀ {B x H t : ℝ}, 0 < B → 1 ≤ x → 1 ≤ H → H ≤ D → |t| = H →
        let a := 1 - 1 / Real.log (D : ℝ)
        ‖∫ σ : ℝ in a..2, lemma56PrincipalPerronArithmeticIntegrand B x ((σ : ℂ) + (t : ℂ) * I)‖ ≤
          2 * (18 * Real.log (D : ℝ) ^ 2 + 21601 * Real.log (D : ℝ)) *
            x ^ 2 * Real.exp (1 / B ^ 2 - H ^ 2 / (4 * B ^ 2)) / H := by
  obtain ⟨Dz, hz⟩ := lemma56_uniform_zeta_off_real_logDeriv_bound
  obtain ⟨Dr, hr⟩ := lemma55_uniform_repulsion_modulus_threshold
  refine ⟨max Dz Dr, ?_⟩
  intro D χ hDN hD hA B x H t hB hx hH hHD ht
  have hL := (hr D ((le_max_right _ _).trans hDN)).1
  have hLp : 0 < Real.log (D : ℝ) := by linarith only [hL]
  have hp : 0 < 1 / Real.log (D : ℝ) := by positivity
  have hinv : 1 / Real.log (D : ℝ) ≤ (1 / 2 : ℝ) := by
    apply (div_le_div_iff₀ hLp (by norm_num)).mpr
    linarith only [hL]
  simp_rw [lemma56_actual_principal_perron_arithmetic_eq]
  apply lemma56_perron_horizontal_integral_bound (1 : DirichletCharacter ℂ 1) hB hx
    (by linarith only [hH])
    (by positivity : 0 ≤ 18 * Real.log (D : ℝ) ^ 2 + 21601 * Real.log (D : ℝ))
    (by linarith only [hinv]) (by linarith only [hp]) (by rw [ht]) 0
  intro σ hσ hσ2
  have hn := hz χ ((le_max_left _ _).trans hDN) hD hA
    ((σ : ℂ) + (t : ℂ) * I) (by simpa using hσ) (by simpa using hσ2)
    (by simpa [ht] using hHD) (by simpa [ht] using hH)
  simpa only [DirichletCharacter.LFunction_modOne_eq, ofReal_zero, zero_mul, sub_zero] using hn

end ZhangLS.Spec
