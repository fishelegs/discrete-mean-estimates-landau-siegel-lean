import ZhangLS.Spec.Lemma56PrincipalPerronMainError


set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set Metric
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096


example : ∃ D₀ : ℕ, ∀ {D : ℕ} (χ : RealPrimitiveCharacter D),
    D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
    ∀ {B x H : ℝ}, 0 < B → 1 ≤ x → 1 ≤ H → H ≤ D →
      let L := Real.log (D : ℝ)
      let a := 1 - 1 / L
      let M := 18 * L ^ 2 + 21601 * L
      ‖(∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) *
          (lemma56PerronWeight B (x / (n : ℝ)) : ℂ)) -
        ((x * Real.exp (1 / (4 * B ^ 2)) : ℝ) : ℂ)‖ ≤
        6 * M * x ^ a * Real.exp (a ^ 2 / (4 * B ^ 2)) * Real.log (1 + H) +
          (4 * M + 4 * lemma56GaussianRightConstant * B ^ 2) *
            x ^ 2 * Real.exp (1 / B ^ 2 - H ^ 2 / (4 * B ^ 2)) / H := by
  simpa only [lemma56PerronMangoldtSum, lemma56PerronMangoldtTerm, lemma56GaussianPhase,
    lemma56Mangoldt, ofReal_zero, zero_mul, Complex.cpow_zero,
    lemma56_principal_one_apply_nat, one_mul] using
      lemma56_uniform_principal_perron_smoothed_main_error

example : ∃ D₀ : ℕ, ∀ {D : ℕ} (χ : RealPrimitiveCharacter D),
    D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
    ∀ {x H : ℝ}, 0 < x → 0 < H → H ≤ D → ∀ B : ℝ,
      let a := 1 - 1 / Real.log (D : ℝ)
      lemma44GeneralRectangleBoundaryIntegral
        (fun s : ℂ => -(deriv riemannZeta s / riemannZeta s) *
          ((x : ℂ) ^ s * Complex.exp (s ^ 2 / (4 * (B : ℂ) ^ 2)) / s)) a 2 H =
            2 * (Real.pi : ℂ) * I * ((x * Real.exp (1 / (4 * B ^ 2)) : ℝ) : ℂ) := by
  obtain ⟨D₀, h⟩ := lemma56_uniform_principal_perron_rectangle_shift
  refine ⟨D₀, ?_⟩
  intro D χ hDN hD hA x H hx hH hHD B
  have hs := h χ hDN hD hA hx hH hHD B
  dsimp only at hs
  have hb : lemma44GeneralRectangleBoundaryIntegral (lemma56PrincipalPerronArithmeticIntegrand B x)
      (1 - 1 / Real.log (D : ℝ)) 2 H =
        2 * (Real.pi : ℂ) * I * ((x * Real.exp (1 / (4 * B ^ 2)) : ℝ) : ℂ) := by
    unfold lemma44GeneralRectangleBoundaryIntegral
    linear_combination hs
  simpa only [lemma56PrincipalPerronArithmeticIntegrand, lemma56PerronComplexKernel, logDeriv_apply] using hb

example : ∃ D₀ : ℕ, ∀ {D : ℕ} (χ : RealPrimitiveCharacter D),
    D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
      let L := Real.log (D : ℝ)
      let B := Real.exp (L / 3)
      let a := 1 - 1 / L
      let M := 18 * L ^ 2 + 21601 * L
      ‖lemma56PerronMangoldtSum (1 : DirichletCharacter ℂ 1) B (lemma23PaperP D) 0 -
        ((lemma23PaperP D * Real.exp (1 / (4 * B ^ 2)) : ℝ) : ℂ)‖ ≤
        6 * M * (lemma23PaperP D) ^ a * Real.exp (a ^ 2 / (4 * B ^ 2)) * Real.log (1 + (D : ℝ) / 2) +
          (4 * M + 4 * lemma56GaussianRightConstant * B ^ 2) *
            (lemma23PaperP D) ^ 2 * Real.exp (1 / B ^ 2 - ((D : ℝ) / 2) ^ 2 / (4 * B ^ 2)) / ((D : ℝ) / 2) := by
  obtain ⟨D₀, h⟩ := lemma56_uniform_principal_perron_smoothed_main_error
  obtain ⟨Dr, hr⟩ := lemma55_uniform_repulsion_modulus_threshold
  refine ⟨max D₀ Dr, ?_⟩
  intro D χ hDN hD hA
  have hL := (hr D ((le_max_right _ _).trans hDN)).1
  have hLp : 0 ≤ Real.log (D : ℝ) := by linarith only [hL]
  have hD2 : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hx : 1 ≤ lemma23PaperP D := by
    unfold lemma23PaperP lemma23PaperL
    exact (Real.one_le_exp_iff).mpr (by positivity)
  exact h χ ((le_max_left _ _).trans hDN) hD hA
    (Real.exp_pos _) hx (by linarith only [hD2]) (by linarith only [hD2])

example : ∃ D₀ : ℕ, ∀ {D : ℕ} (χ : RealPrimitiveCharacter D),
    D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
    ∀ {B x : ℝ}, 0 < B → 1 ≤ x →
      let L := Real.log (D : ℝ)
      let a := 1 - 1 / L
      ‖∫ σ : ℝ in a..2, lemma56PrincipalPerronArithmeticIntegrand B x ((σ : ℂ) - (D : ℂ) * I)‖ ≤
        2 * (18 * L ^ 2 + 21601 * L) * x ^ 2 *
          Real.exp (1 / B ^ 2 - (D : ℝ) ^ 2 / (4 * B ^ 2)) / D := by
  obtain ⟨D₀, h⟩ := lemma56_uniform_principal_perron_horizontal_bound
  refine ⟨D₀, ?_⟩
  intro D χ hDN hD hA B x hB hx
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD.le
  have hn := h χ hDN hD hA (B := B) (x := x) (H := (D : ℝ)) (t := -(D : ℝ))
    hB hx hD1 (le_refl _) (by simp)
  simpa only [ofReal_neg, neg_mul, sub_eq_add_neg] using hn

#print axioms lemma56_perron_rectangle_edges_mem
#print axioms lemma56_perron_rectangle_edges_integrable
#print axioms lemma56_perron_rectangle_boundary_add
#print axioms lemma56_perron_rectangle_boundary_congr
#print axioms lemma56_actual_principal_regular_perron_analytic
#print axioms lemma56_actual_principal_perron_pole_split
#print axioms lemma56_actual_principal_perron_rectangle_boundary
#print axioms lemma56_actual_principal_perron_rectangle_shift
#print axioms lemma56_uniform_principal_perron_rectangle_shift
#print axioms lemma56_actual_principal_perron_arithmetic_eq
#print axioms lemma56_uniform_zeta_off_real_logDeriv_bound
#print axioms lemma56_uniform_principal_perron_left_bound
#print axioms lemma56_uniform_principal_perron_horizontal_bound
#print axioms lemma56_uniform_principal_perron_smoothed_main_error

end ZhangLS.Spec
