import ZhangLS.Spec.Lemma56PrincipalPerronMellin
import ZhangLS.Spec.Lemma56PrimeMassNormalization
import ZhangLS.Spec.Lemma56ZetaLogDerivativeLeft

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Metric Set MeasureTheory Finset
open scoped Real
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096


example (D : ℕ) :
    lemma23PaperP D * (lemma56PaperPrimes D).card ≤
        ∑ p ∈ lemma56PaperPrimes D, (p : ℝ) ∧
      (∑ p ∈ lemma56PaperPrimes D, (p : ℝ)) ≤
        lemma56PrimeUpper D * (lemma56PaperPrimes D).card := by
  simpa only [lemma56PrimeMass] using lemma56_actual_prime_mass_card_bounds D

example {D : ℕ} (hL : 2000 ≤ lemma23PaperL D) {c : ℝ}
    (hlogmass : c * lemma23PaperP D / lemma23PaperL D ^ 68 ≤
      ∑ p ∈ lemma56PaperPrimes D, Real.log (p : ℝ)) :
    (c / 2) * (lemma23PaperP D) ^ 2 / lemma23PaperL D ^ 77 ≤
      ∑ p ∈ lemma56PaperPrimes D, (p : ℝ) := by
  simpa only [lemma56PrimeMass, lemma56PaperPrimeLogMass] using
    lemma56_actual_prime_mass_log_reduction hL hlogmass

example : (2000 : ℝ) ^ 77 *
    Real.exp (-((7 / 6 : ℝ) * (2000 : ℝ) ^ (9 / 2 : ℝ))) ≤
      Real.exp (-((2000 : ℝ) ^ (9 / 2 : ℝ))) :=
  lemma56_prime_mass_polynomial_absorption (by norm_num)

example {c : ℝ} (hc : 0 < c) (Dm : ℕ)
    (hmass : ∀ D : ℕ, Dm ≤ D → c * (lemma23PaperP D) ^ 2 / lemma23PaperL D ^ 77 ≤
      ∑ p ∈ lemma56PaperPrimes D, (p : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℕ, ∀ {D q : ℕ} [NeZero q]
      (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ q),
      D₀ ≤ D → 1 < D → NormalizedAssumptionA χ → θ.IsPrimitive → 1 < q →
      (q : ℝ) < lemma56PaperT D →
      (fun n : ℕ => θ (n : ZMod q)) ≠ (fun n : ℕ => χ.chi (n : ZMod D)) →
      ∀ τ : ℝ, |τ| ≤ D →
        ‖∑ p ∈ lemma56PaperPrimes D, θ (p : ZMod q) * (p : ℂ) ^ (1 + I * (τ : ℂ))‖ ≤
          C * (∑ p ∈ lemma56PaperPrimes D, (p : ℝ)) *
            Real.exp (-(lemma23PaperL D ^ (9 / 2 : ℝ))) := by
  simpa only [lemma56PrimeMass, lemma56PrimeSum, lemma56Decay] using
    lemma56_uniform_primitive_prime_window_normalized_of_mass_lower hc Dm hmass


example : ∃ D₀ : ℕ, ∀ {D : ℕ} (χ : RealPrimitiveCharacter D),
    D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
    ∀ ρ : ℂ, 1 - 2 / Real.log (D : ℝ) < ρ.re →
      |ρ.im| ≤ 2 * (D : ℝ) →
      (((ρ - 1) * (completedRiemannZeta₀ ρ - ρ⁻¹) + 1) * (Gammaℝ ρ)⁻¹) ≠ 0 := by
  obtain ⟨D₀, h⟩ := lemma56_uniform_zeta_pole_removed_zero_exclusion
  refine ⟨D₀, ?_⟩
  intro D χ hDN hD hA ρ hre ht
  have hn := h χ hDN hD hA ρ hre ht
  simpa only [zetaPoleRemoved] using hn

example : ∃ D₀ : ℕ, ∀ {D : ℕ} (χ : RealPrimitiveCharacter D),
    D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
    ∀ σ : ℝ, 1 - 2 / Real.log (D : ℝ) < σ →
      riemannZeta ((σ : ℂ) + (2 * (D : ℝ) : ℝ) * I) ≠ 0 := by
  obtain ⟨D₀, h⟩ := lemma56_uniform_riemann_zeta_zero_exclusion
  refine ⟨D₀, ?_⟩
  intro D χ hDN hD hA σ hre
  apply h χ hDN hD hA
  · simpa using hre
  · simp

example : ∃ D₀ : ℕ, ∀ {D : ℕ} (χ : RealPrimitiveCharacter D),
    D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
    ∀ σ : ℝ, 1 - 2 / Real.log (D : ℝ) < σ →
      riemannZeta ((σ : ℂ) - (2 * (D : ℝ) : ℝ) * I) ≠ 0 := by
  obtain ⟨D₀, h⟩ := lemma56_uniform_riemann_zeta_zero_exclusion
  refine ⟨D₀, ?_⟩
  intro D χ hDN hD hA σ hre
  apply h χ hDN hD hA
  · simpa using hre
  · simp

example : zetaPoleRemoved (1 : ℂ) ≠ 0 := by
  rw [lemma55_actual_zeta_pole_removed_at_one]
  exact one_ne_zero


example : ∃ D₀ : ℕ, ∀ {D : ℕ} (χ : RealPrimitiveCharacter D),
    D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
    ∀ t : ℝ, |t| ≤ D →
      ‖deriv riemannZeta (((1 - 1 / Real.log (D : ℝ) : ℝ) : ℂ) + (t : ℂ) * I) /
        riemannZeta (((1 - 1 / Real.log (D : ℝ) : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
        18 * Real.log (D : ℝ) ^ 2 + 21601 * Real.log (D : ℝ) := by
  simpa only [logDeriv_apply] using lemma56_uniform_zeta_left_logDeriv_bound

example : ∃ D₀ : ℕ, ∀ {D : ℕ} (χ : RealPrimitiveCharacter D),
    D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
    ‖logDeriv riemannZeta (((1 - 1 / Real.log (D : ℝ) : ℝ) : ℂ) + (D : ℂ) * I)‖ ≤
      18 * Real.log (D : ℝ) ^ 2 + 21601 * Real.log (D : ℝ) := by
  obtain ⟨D₀, h⟩ := lemma56_uniform_zeta_left_logDeriv_bound
  refine ⟨D₀, ?_⟩
  intro D χ hDN hD hA
  exact h χ hDN hD hA (D : ℝ) (by simp)

example : ∃ D₀ : ℕ, ∀ {D : ℕ} (χ : RealPrimitiveCharacter D),
    D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
    ‖logDeriv riemannZeta (((1 - 1 / Real.log (D : ℝ) : ℝ) : ℂ) - (D : ℂ) * I)‖ ≤
      18 * Real.log (D : ℝ) ^ 2 + 21601 * Real.log (D : ℝ) := by
  obtain ⟨D₀, h⟩ := lemma56_uniform_zeta_left_logDeriv_bound
  refine ⟨D₀, ?_⟩
  intro D χ hDN hD hA
  have hn := h χ hDN hD hA (-(D : ℝ)) (by simp)
  simpa only [Complex.ofReal_neg, neg_mul, sub_eq_add_neg] using hn

example : ∃ D₀ : ℕ, ∀ {D : ℕ} (χ : RealPrimitiveCharacter D),
    D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
    ‖logDeriv zetaPoleRemoved ((2 : ℂ) + (D : ℂ) * I)‖ ≤
      18 * Real.log (D : ℝ) ^ 2 + 21600 * Real.log (D : ℝ) := by
  obtain ⟨D₀, h⟩ := lemma56_uniform_zeta_removed_logDeriv_bound
  obtain ⟨Dr, hr⟩ := lemma55_uniform_repulsion_modulus_threshold
  refine ⟨max D₀ Dr, ?_⟩
  intro D χ hDN hD hA
  have hL := (hr D ((le_max_right _ _).trans hDN)).1
  have hLp : 0 < Real.log (D : ℝ) := by linarith only [hL]
  apply h χ ((le_max_left _ _).trans hDN) hD hA
  · have hp : 0 < 1 / Real.log (D : ℝ) := by positivity
    simpa using (by linarith only [hp] : 1 - 1 / Real.log (D : ℝ) ≤ (2 : ℝ))
  · simp
  · simp

example {x a H : ℝ} (hx : 0 < x) (ha0 : 0 < a) (ha1 : a < 1) (hH : 0 < H) (B : ℝ) :
    lemma44GeneralRectangleBoundaryIntegral
      (fun s : ℂ => ((x : ℂ) ^ s * Complex.exp (s ^ 2 / (4 * (B : ℂ) ^ 2)) / s) / (s - 1)) a 2 H =
        2 * (Real.pi : ℂ) * I * ((x * Real.exp (1 / (4 * B ^ 2)) : ℝ) : ℂ) := by
  simpa only [lemma56PerronComplexKernel] using lemma56_actual_perron_pole_rectangle hx ha0 ha1 hH B

example {L x H : ℝ} (hL : 2000 ≤ L) (hx : 0 < x) (hH : 0 < H) (B : ℝ) :
    lemma44GeneralRectangleBoundaryIntegral
      (fun s : ℂ => lemma56PerronComplexKernel B x s / (s - 1)) (1 - 1 / L) 2 H =
        2 * (Real.pi : ℂ) * I * ((x * Real.exp (1 / (4 * B ^ 2)) : ℝ) : ℂ) := by
  have hLp : 0 < L := by linarith only [hL]
  have hp : 0 < 1 / L := by positivity
  have hi : 1 / L ≤ (1 / 2 : ℝ) := by
    apply (div_le_div_iff₀ hLp (by norm_num)).mpr
    linarith only [hL]
  exact lemma56_actual_perron_pole_rectangle hx (by linarith only [hi]) (by linarith only [hp]) hH B

example {B x : ℝ} (hB : 0 < B) (hx : 0 < x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
      -(deriv riemannZeta ((2 : ℂ) + (t : ℂ) * I) / riemannZeta ((2 : ℂ) + (t : ℂ) * I)) *
        ((x : ℂ) ^ ((2 : ℂ) + (t : ℂ) * I) *
          Complex.exp (((2 : ℂ) + (t : ℂ) * I) ^ 2 / (4 * (B : ℂ) ^ 2)) /
          ((2 : ℂ) + (t : ℂ) * I)) =
        lemma56PerronMangoldtSum (1 : DirichletCharacter ℂ 1) B x 0 := by
  simpa only [logDeriv_apply, lemma56PerronKernel] using
    lemma56_actual_principal_perron_mellin_identity hB hx

example {L H : ℝ} (hL : 2000 ≤ L) (hH : 0 < H) :
    lemma44GeneralRectangleBoundaryIntegral (fun w : ℂ => w⁻¹) (-1 / L) 1 H =
      2 * (Real.pi : ℂ) * I := by
  have hLp : 0 < L := by linarith only [hL]
  exact lemma56_positive_right_rectangle_inv (div_neg_of_neg_of_pos (by norm_num) hLp) (by norm_num) hH


#print axioms lemma56_paper_prime_log_mass_nonneg
#print axioms lemma56_actual_prime_mass_card_bounds
#print axioms lemma56_actual_prime_mass_from_logmass
#print axioms lemma56_paper_prime_log_upper
#print axioms lemma56_actual_prime_mass_log_reduction
#print axioms lemma56_prime_mass_polynomial_absorption
#print axioms lemma56_actual_prime_mass_normalization
#print axioms lemma56_uniform_primitive_prime_window_normalized_of_mass_lower
#print axioms lemma56_actual_zeta_zero_own_disk
#print axioms lemma56_actual_zeta_inverse_square_lower
#print axioms lemma56_actual_zeta_zero_four_detected
#print axioms lemma56_actual_zeta_zero_exclusion
#print axioms lemma56_uniform_zeta_pole_removed_zero_exclusion
#print axioms lemma56_uniform_riemann_zeta_zero_exclusion
#print axioms lemma56_actual_zeta_removed_logDeriv_near_center_bound
#print axioms lemma56_actual_zeta_logDeriv_bound_of_local_zero_gap
#print axioms lemma56_actual_zeta_logDeriv_rectangular_bound
#print axioms lemma56_uniform_zeta_removed_logDeriv_bound
#print axioms lemma56_uniform_zeta_left_logDeriv_bound

#print axioms lemma56_positive_right_rectangle_inv
#print axioms lemma56_positive_right_simple_pole_rectangle
#print axioms lemma56_perron_complex_kernel_at_line
#print axioms lemma56_perron_complex_kernel_analytic
#print axioms lemma56_perron_complex_kernel_at_one
#print axioms lemma56_rectangle_translation_one
#print axioms lemma56_actual_perron_pole_rectangle
#print axioms lemma56_actual_principal_perron_mellin_identity

end ZhangLS.Spec
