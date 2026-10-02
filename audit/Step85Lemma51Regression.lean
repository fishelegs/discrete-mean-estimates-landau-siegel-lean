import ZhangLS.Spec.Lemma51

/-! The four paper inequalities, with all region and scale abbreviations expanded. -/

open Complex
open ZhangLS.Spec

set_option maxHeartbeats 1000000

example : ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℕ,
    ∀ (D p : ℕ) [NeZero p] (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p),
      D₀ ≤ D → Lemma23InPsi (D := D) ψ →
      ∀ (s w : ℂ), |s.re - 1 / 2| ≤ Real.pi / Real.log (Real.exp ((Real.log D) ^ 9)) →
      |s.im - 2 * Real.pi * (Real.log D) ^ 519| < (Real.log D) ^ 405 + 2 →
      w.re = 0 → |w.im| < (Real.log D) ^ 20 →
      letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
      ‖(lemma23DirichletZ ψ (s + w) - lemma23DirichletZ ψ s *
          (((p : ℝ) * (Real.log D) ^ 519 : ℝ) : ℂ) ^ (-w)) / w‖ ≤
            C * (Real.log D) ^ (-114 : ℤ) ∧
      ‖(lemma23DirichletZ ψ (s + w) - lemma23DirichletZ ψ s *
          ((Real.exp ((Real.log D) ^ 9) * (Real.log D) ^ 519 : ℝ) : ℂ) ^ (-w)) / w‖ ≤
            C * (Real.log D) ^ (-68 : ℤ) ∧
      ‖(lemma23DirichletZ (lemma44CharacterTwist χ ψ) (s + w) -
          lemma23DirichletZ (lemma44CharacterTwist χ ψ) s *
          ((((D * p : ℕ) : ℝ) * (Real.log D) ^ 519 : ℝ) : ℂ) ^ (-w)) / w‖ ≤
            C * (Real.log D) ^ (-114 : ℤ) ∧
      ‖(lemma23DirichletZ (lemma44CharacterTwist χ ψ) (s + w) -
          lemma23DirichletZ (lemma44CharacterTwist χ ψ) s *
          (((D : ℝ) * Real.exp ((Real.log D) ^ 9) * (Real.log D) ^ 519 : ℝ) : ℂ) ^ (-w)) / w‖ ≤
            C * (Real.log D) ^ (-68 : ℤ) := by
  obtain ⟨C, hC, D₀, h⟩ := lemma51_proved
  refine ⟨C, hC, D₀, ?_⟩
  intro D p hp χ ψ hD hψ s w hre him hwre hwim
  exact h D p χ ψ hD hψ s w ⟨hre, him⟩ hwre hwim

-- The closed real-strip boundary has no extra strictness assumption.
example {D p : ℕ} [NeZero p] (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi (D := D) ψ)
    {s w : ℂ} (hre : |s.re - 1 / 2| = lemma44PaperAlpha D)
    (him : |s.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 2)
    (hwre : w.re = 0) (hwim : |w.im| < lemma23PaperL D ^ 20) :
    Lemma51Estimates χ ψ s w lemma51ErrorConstant :=
  lemma51_actual_shift_estimates χ ψ hD hψ ⟨hre.le, him⟩ hwre hwim

example {D p : ℕ} [NeZero p] (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hs : Lemma51InRegion D s) :
    Lemma51Estimates χ ψ s 0 lemma51ErrorConstant := by
  apply lemma51_actual_shift_estimates χ ψ hD hψ hs (by simp)
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  simp only [Complex.zero_im, abs_zero]
  positivity

#print axioms lemma51_Gamma_logDeriv_eq_Euler
#print axioms lemma51_Gamma_logDeriv_sub_log_bound
#print axioms lemma51_DirichletZ_logDeriv_sharp
#print axioms lemma51_height_log_error
#print axioms lemma51_DirichletZ_logDeriv_at_T0
#print axioms lemma51_DirichletZ_norm_bound
#print axioms lemma51_vertical_transport
#print axioms lemma51_actual_shift_at_real_conductor
#print axioms lemma51_actual_shift_estimates
#print axioms lemma51_proved
