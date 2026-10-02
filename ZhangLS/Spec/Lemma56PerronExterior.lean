import ZhangLS.Spec.Lemma56PerronHorizontalBudget

/-! # Actual cumulative Perron estimates for Lemma 5.6

The full original sharp prime-window target remains a separate obligation.
-/

namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Real
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

theorem lemma56_uniform_primitive_perron_paper_exterior_bounds :
    ∃ D₀ : ℕ, ∀ {D q : ℕ} [NeZero q] (χ : RealPrimitiveCharacter D)
      (θ : DirichletCharacter ℂ q), D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
      θ.IsPrimitive → 1 < q → (q : ℝ) < lemma56PaperT D →
      (fun n : ℕ => θ (n : ZMod q)) ≠ (fun n : ℕ => χ.chi (n : ZMod D)) →
      ∀ {x τ : ℝ}, 1 ≤ x → x ≤ 2 * lemma23PaperP D → |τ| ≤ D →
        let U := lemma23PaperL D ^ (9 / 2 : ℝ)
        let B := Real.exp ((3 / 2 : ℝ) * U)
        let H := Real.exp (2 * U) / 2
        let a := 1 - 1 / ((3 / 4 : ℝ) * U)
        let E := 1844736 * lemma23PaperP D * Real.exp (-3 * U)
        (‖∫ σ : ℝ in a..2, lemma56PerronArithmeticIntegrand θ B x τ
          ((σ : ℂ) + (H : ℂ) * I)‖ ≤ E) ∧
        (‖∫ σ : ℝ in a..2, lemma56PerronArithmeticIntegrand θ B x τ
          ((σ : ℂ) - (H : ℂ) * I)‖ ≤ E) ∧
        (‖(∫ t : ℝ, lemma56PerronArithmeticIntegrand θ B x τ ((2 : ℂ) + (t : ℂ) * I)) -
          (∫ t : ℝ in -H..H, lemma56PerronArithmeticIntegrand θ B x τ ((2 : ℂ) + (t : ℂ) * I))‖ ≤
            32 * lemma56GaussianRightConstant * lemma23PaperP D * Real.exp (-3 * U)) := by
  obtain ⟨Dld, hld⟩ := lemma56_uniform_primitive_margin_logDeriv_bound
  obtain ⟨Drep, hrep⟩ := lemma56_uniform_repulsion_modulus_threshold
  refine ⟨max Dld Drep, ?_⟩
  intro D q _ χ θ hDN hD hA hθ hq1 hqT hne x τ hx hxmax hτ
  have hLD := hld χ θ ((le_max_left _ _).trans hDN) hD hA hθ hq1 hqT hne
  have hL := (hrep D ((le_max_right _ _).trans hDN)).1
  have hs := lemma56_high_scale_strict_margin hL
  let U := lemma23PaperL D ^ (9 / 2 : ℝ)
  let V := (3 / 4 : ℝ) * U
  let B := Real.exp ((3 / 2 : ℝ) * U)
  let H := Real.exp (2 * U) / 2
  let a := 1 - 1 / V
  let M := 24 * V ^ 2 + 28800 * V
  have hV2 : 2000 ≤ V := hs.2.2.1
  have hU2 : 2000 ≤ U := by dsimp [V] at hV2; linarith only [hV2]
  have hB : 0 < B := by dsimp [B]; positivity
  have hH : 0 < H := by dsimp [H]; positivity
  have hxp : 0 < x := by linarith only [hx]
  have hVp : 0 < V := by linarith only [hV2]
  have hInv : 0 < 1 / V := by positivity
  have hInv1 : 1 / V ≤ 1 := (div_le_iff₀ hVp).mpr (by linarith only [hV2])
  have ha0 : 0 ≤ a := by dsimp [a]; linarith only [hInv1]
  have ha2 : a ≤ 2 := by dsimp [a]; linarith only [hInv]
  have hDmax := lemma56_margin_height_contains_modulus hD hL
  have hp : U ^ 2 = (lemma23PaperL D) ^ 9 := by
    dsimp [U]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (show 0 ≤ lemma23PaperL D from (by norm_num : (0 : ℝ) ≤ 2000).trans hL)]
    norm_num
  have hP : Real.exp (U ^ 2) = lemma23PaperP D := by rw [hp]; rfl
  have hlocalLD (t : ℝ) (ht : |t| ≤ H) (σ : ℝ) (hσa : a ≤ σ) (hσ2 : σ ≤ 2) :
      ‖logDeriv (DirichletCharacter.LFunction θ)
        ((σ : ℂ) + (t : ℂ) * I - (τ : ℂ) * I)‖ ≤ M := by
    apply hLD
    · simpa only [add_re, sub_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
        mul_zero, zero_mul, mul_one, zero_sub, sub_zero, add_zero] using hσa
    · simpa using hσ2
    · have hh := abs_sub t τ
      have hheight : |t - τ| ≤ Real.exp (2 * U) := by
        dsimp [H] at ht
        change 2 * (D : ℝ) ≤ Real.exp (2 * U) at hDmax
        linarith only [hh, ht, hτ, hDmax]
      simpa using hheight
  have hb := lemma56_perron_paper_horizontal_budget hU2 hxp (by simpa only [hP] using hxmax)
  rw [hP] at hb
  have htop := lemma56_perron_horizontal_integral_bound θ hB hx hH
    (by dsimp [M]; positivity) ha0 ha2 (t := H) (le_abs_self H) τ
      (hlocalLD H (by rw [abs_of_pos hH]))
  have hbot := lemma56_perron_horizontal_integral_bound θ hB hx hH
    (by dsimp [M]; positivity) ha0 ha2 (t := -H) (by rw [abs_neg]; exact le_abs_self H) τ
      (hlocalLD (-H) (by rw [abs_neg, abs_of_pos hH]))
  have ht := lemma56_actual_perron_right_truncation θ hB hxp hH τ
  have htb := lemma56_perron_paper_right_budget hU2 lemma56_gaussian_right_constant_nonneg hxp
    (by simpa only [hP] using hxmax)
  rw [hP] at htb
  dsimp only
  refine ⟨htop.trans hb, ?_, ht.trans htb⟩
  have he (σ : ℝ) : (σ : ℂ) + ((-H : ℝ) : ℂ) * I = (σ : ℂ) - (H : ℂ) * I := by push_cast; ring
  simpa only [he] using hbot.trans hb

end ZhangLS.Spec
