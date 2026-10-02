import ZhangLS.Spec.Lemma56PerronWindowBudget

/-! # Actual cumulative Perron estimates for Lemma 5.6

The full original sharp prime-window target remains a separate obligation.
-/

namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Real
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

theorem lemma56_uniform_primitive_perron_window_left_bound :
    ∃ D₀ : ℕ, ∀ {D q : ℕ} [NeZero q] (χ : RealPrimitiveCharacter D)
      (θ : DirichletCharacter ℂ q), D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
      θ.IsPrimitive → 1 < q → (q : ℝ) < lemma56PaperT D →
      (fun n : ℕ => θ (n : ZMod q)) ≠ (fun n : ℕ => χ.chi (n : ZMod D)) →
      ∀ {B H τ x : ℝ}, 1 ≤ x → x ≤ 2 * lemma23PaperP D → 1 ≤ B → 0 ≤ H →
        H ≤ Real.exp (2 * lemma23PaperL D ^ (9 / 2 : ℝ)) / 2 → |τ| ≤ D →
        let a := 1 - 1 / ((3 / 4 : ℝ) * lemma23PaperL D ^ (9 / 2 : ℝ))
        (1 / (2 * Real.pi)) * ‖∫ t : ℝ in -H..H,
          lemma56PerronArithmeticIntegrand θ B x τ ((a : ℂ) + (t : ℂ) * I)‖ ≤
            (2 * (2017218816 * Real.exp (1 / 4 : ℝ))) * lemma23PaperP D *
              Real.exp (-((7 / 6 : ℝ) * lemma23PaperL D ^ (9 / 2 : ℝ))) := by
  obtain ⟨Dleft, hleft⟩ := lemma56_uniform_primitive_perron_left_bound
  obtain ⟨Drep, hrep⟩ := lemma56_uniform_repulsion_modulus_threshold
  refine ⟨max Dleft Drep, ?_⟩
  intro D q _ χ θ hDN hD hA hθ hq1 hqT hne B H τ x hx hxmax hB hH hHmax hτ
  have hL := (hrep D ((le_max_right _ _).trans hDN)).1
  have hBpos : 0 < B := by linarith only [hB]
  have hxp : 0 < x := by linarith only [hx]
  have hbound := (hleft χ θ ((le_max_left _ _).trans hDN) hD hA hθ hq1 hqT hne
    (x := x) hBpos hxp hH hHmax hτ).2
  have hbudget := lemma56_perron_paper_window_left_budget hL hB hH hHmax hxp hxmax
  have hpi : 1 ≤ 2 * Real.pi := by linarith only [Real.two_le_pi]
  have hnorm : 0 ≤ ‖∫ t : ℝ in -H..H,
    lemma56PerronArithmeticIntegrand θ B x τ
      (((1 - 1 / ((3 / 4 : ℝ) * lemma23PaperL D ^ (9 / 2 : ℝ))) : ℝ) + (t : ℂ) * I)‖ :=
    norm_nonneg _
  have hcoef : 1 / (2 * Real.pi) ≤ 1 :=
    (div_le_iff₀ (by positivity)).mpr (by simpa using hpi)
  dsimp only
  calc
    _ ≤ ‖∫ t : ℝ in -H..H,
      lemma56PerronArithmeticIntegrand θ B x τ
        (((1 - 1 / ((3 / 4 : ℝ) * lemma23PaperL D ^ (9 / 2 : ℝ))) : ℝ) + (t : ℂ) * I)‖ := by
      exact (mul_le_mul_of_nonneg_right hcoef hnorm).trans_eq (one_mul _)
    _ ≤ _ := hbound.trans hbudget

end ZhangLS.Spec
