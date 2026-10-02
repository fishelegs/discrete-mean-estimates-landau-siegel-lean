import ZhangLS.Spec.Lemma56TwistedGaussianHorizontal

/-! # Actual oscillatory Gaussian estimates for Lemma 5.6

The original sharp prime-window target remains a separate obligation.
-/

namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Real
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

theorem lemma56_uniform_primitive_twisted_gaussian_paper_left_bound :
    ∃ D₀ : ℕ, ∀ {D q : ℕ} [NeZero q] (χ : RealPrimitiveCharacter D)
      (θ : DirichletCharacter ℂ q), D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
      θ.IsPrimitive → 1 < q → (q : ℝ) < lemma56PaperT D →
      (fun n : ℕ => θ (n : ZMod q)) ≠ (fun n : ℕ => χ.chi (n : ZMod D)) →
      ∀ {B H τ : ℝ}, 1 ≤ B → 0 ≤ H →
        H ≤ Real.exp (2 * lemma23PaperL D ^ (9 / 2 : ℝ)) / 2 → |τ| ≤ D →
        let a := 1 - 1 / ((3 / 4 : ℝ) * lemma23PaperL D ^ (9 / 2 : ℝ))
        (1 / (2 * Real.pi)) *
          ‖∫ t : ℝ in -H..H,
            lemma56TwistedGaussianArithmeticIntegrand θ B (lemma23PaperP D) τ
              ((a : ℂ) + (t : ℂ) * I)‖ ≤
          (4150656 * Real.exp (1 / 4 : ℝ)) * lemma23PaperP D *
            Real.exp (-((7 / 6 : ℝ) * lemma23PaperL D ^ (9 / 2 : ℝ))) := by
  obtain ⟨Dleft, hleft⟩ := lemma56_uniform_primitive_twisted_gaussian_left_bound
  obtain ⟨Drep, hrep⟩ := lemma56_uniform_repulsion_modulus_threshold
  refine ⟨max Dleft Drep, ?_⟩
  intro D q _ χ θ hDN hD hA hθ hq1 hqT hne B H τ hB hH hHmax hτ
  have hL := (hrep D ((le_max_right _ _).trans hDN)).1
  have hBpos : 0 < B := by linarith only [hB]
  have hbound := (hleft χ θ ((le_max_left _ _).trans hDN) hD hA hθ hq1 hqT hne
    (x := lemma23PaperP D) hBpos (Real.exp_pos _) hH hHmax hτ).2
  have hbudget := lemma56_paper_left_gaussian_budget hL hB
  have hpi : 0 < 2 * Real.pi := by positivity
  dsimp only
  have hdiv (c y : ℝ) : (1 / c) * y = y / c := by ring
  rw [hdiv]
  apply (div_le_iff₀ hpi).mpr
  calc
    _ ≤ (24 * ((3 / 4 : ℝ) * lemma23PaperL D ^ (9 / 2 : ℝ)) ^ 2 +
        28800 * ((3 / 4 : ℝ) * lemma23PaperL D ^ (9 / 2 : ℝ))) *
        (2 * Real.pi * (lemma23PaperP D) ^
          (1 - 1 / ((3 / 4 : ℝ) * lemma23PaperL D ^ (9 / 2 : ℝ))) *
          Real.exp ((1 - 1 / ((3 / 4 : ℝ) * lemma23PaperL D ^ (9 / 2 : ℝ))) ^ 2 /
            (4 * B ^ 2))) := hbound
    _ ≤ ((4150656 * Real.exp (1 / 4 : ℝ)) * lemma23PaperP D *
        Real.exp (-((7 / 6 : ℝ) * lemma23PaperL D ^ (9 / 2 : ℝ)))) *
          (2 * Real.pi) := by
      simp only [lemma23PaperP, lemma23PaperL]
      convert mul_le_mul_of_nonneg_right hbudget hpi.le using 1 <;> ring


end ZhangLS.Spec
