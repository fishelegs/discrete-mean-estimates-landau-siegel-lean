import ZhangLS.Spec.Lemma56PerronUnsmoothingError

/-! # Actual smoothing removal and prime-log estimates for Lemma 5.6

The original prime-window target and its principal boundary remain separate obligations.
-/

namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Real
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

theorem lemma56_uniform_primitive_sharp_mangoldt_window_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℕ, ∀ {D q : ℕ} [NeZero q]
      (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ q),
      D₀ ≤ D → 1 < D → NormalizedAssumptionA χ → θ.IsPrimitive → 1 < q →
      (q : ℝ) < lemma56PaperT D →
      (fun n : ℕ => θ (n : ZMod q)) ≠ (fun n : ℕ => χ.chi (n : ZMod D)) →
      ∀ {x τ : ℝ}, 1 ≤ x → x ≤ 2 * lemma23PaperP D → |τ| ≤ D →
        let U := lemma23PaperL D ^ (9 / 2 : ℝ)
        ‖lemma56SharpMangoldtSum θ x τ‖ ≤
          C * lemma23PaperP D * Real.exp (-((7 / 6 : ℝ) * U)) := by
  obtain ⟨Cm, hCm, Ds, hs⟩ := lemma56_uniform_primitive_perron_mangoldt_window_bound
  obtain ⟨Dr, hr⟩ := lemma56_uniform_repulsion_modulus_threshold
  refine ⟨Cm + lemma56PerronUnsmoothingConstant,
    add_pos hCm lemma56_perron_unsmoothing_constant_pos, max Ds Dr, ?_⟩
  intro D q _ χ θ hDN hD hA hθ hq1 hqT hne x τ hx hxmax hτ
  have hL : 2000 ≤ lemma23PaperL D := (hr D ((le_max_right _ _).trans hDN)).1
  have hscale := lemma56_high_scale_strict_margin hL
  let U := lemma23PaperL D ^ (9 / 2 : ℝ)
  have hU : 2000 ≤ U := by
    have hh : 2000 ≤ (3 / 4 : ℝ) * U := hscale.2.2.1
    linarith only [hh]
  have hP : Real.exp (U ^ 2) = lemma23PaperP D := by
    dsimp [U, lemma23PaperP]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith only [hL] : 0 ≤ lemma23PaperL D)]
    norm_num
  have he := lemma56_actual_perron_paper_smoothing_error θ hU hx
    (by simpa only [hP] using hxmax) τ
  rw [hP] at he
  have hm := hs χ θ ((le_max_left _ _).trans hDN) hD hA hθ hq1 hqT hne hx hxmax hτ
  have ht : ‖lemma56SharpMangoldtSum θ x τ‖ ≤
      ‖lemma56PerronMangoldtSum θ (Real.exp ((3 / 2 : ℝ) * U)) x τ‖ +
      ‖lemma56PerronMangoldtSum θ (Real.exp ((3 / 2 : ℝ) * U)) x τ -
        lemma56SharpMangoldtSum θ x τ‖ := by
    simpa only [sub_sub_cancel] using
      norm_sub_le (lemma56PerronMangoldtSum θ (Real.exp ((3 / 2 : ℝ) * U)) x τ)
        (lemma56PerronMangoldtSum θ (Real.exp ((3 / 2 : ℝ) * U)) x τ -
          lemma56SharpMangoldtSum θ x τ)
  change ‖lemma56SharpMangoldtSum θ x τ‖ ≤
    (Cm + lemma56PerronUnsmoothingConstant) * lemma23PaperP D * Real.exp (-((7 / 6 : ℝ) * U))
  change ‖lemma56PerronMangoldtSum θ (Real.exp ((3 / 2 : ℝ) * U)) x τ‖ ≤
    Cm * lemma23PaperP D * Real.exp (-((7 / 6 : ℝ) * U)) at hm
  nlinarith only [hm, he, ht]

end ZhangLS.Spec
