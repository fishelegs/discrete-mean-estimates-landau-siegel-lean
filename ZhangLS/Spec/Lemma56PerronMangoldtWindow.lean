import ZhangLS.Spec.Lemma56PerronRectangleNorm

/-! # Actual cumulative Perron estimates for Lemma 5.6

The full original sharp prime-window target remains a separate obligation.
-/

namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Real
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

theorem lemma56_uniform_primitive_perron_mangoldt_window_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℕ, ∀ {D q : ℕ} [NeZero q]
      (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ q),
      D₀ ≤ D → 1 < D → NormalizedAssumptionA χ → θ.IsPrimitive → 1 < q →
      (q : ℝ) < lemma56PaperT D →
      (fun n : ℕ => θ (n : ZMod q)) ≠ (fun n : ℕ => χ.chi (n : ZMod D)) →
      ∀ {x τ : ℝ}, 1 ≤ x → x ≤ 2 * lemma23PaperP D → |τ| ≤ D →
        let U := lemma23PaperL D ^ (9 / 2 : ℝ)
        ‖lemma56PerronMangoldtSum θ (Real.exp ((3 / 2 : ℝ) * U)) x τ‖ ≤
          C * lemma23PaperP D * Real.exp (-((7 / 6 : ℝ) * U)) := by
  let C := 2 * (2017218816 * Real.exp (1 / 4 : ℝ)) +
    32 * lemma56GaussianRightConstant + 3689472
  have hCr := lemma56_gaussian_right_constant_nonneg
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨Ds, hs⟩ := lemma56_uniform_primitive_perron_rectangle_shift
  obtain ⟨Dl, hl⟩ := lemma56_uniform_primitive_perron_window_left_bound
  obtain ⟨De, he⟩ := lemma56_uniform_primitive_perron_paper_exterior_bounds
  obtain ⟨Dr, hr⟩ := lemma56_uniform_repulsion_modulus_threshold
  refine ⟨C, hC, max (max Ds Dl) (max De Dr), ?_⟩
  intro D q _ χ θ hDN hD hA hθ hq1 hqT hne x τ hx hxmax hτ
  have hL := (hr D ((le_max_right _ _).trans ((le_max_right _ _).trans hDN))).1
  have hscale := lemma56_high_scale_strict_margin hL
  let U := lemma23PaperL D ^ (9 / 2 : ℝ)
  let B := Real.exp ((3 / 2 : ℝ) * U)
  let H := Real.exp (2 * U) / 2
  let a := 1 - 1 / ((3 / 4 : ℝ) * U)
  let N : ℝ := 1 / (2 * Real.pi)
  let A : ℝ := lemma23PaperP D * Real.exp (-((7 / 6 : ℝ) * U))
  let A3 : ℝ := lemma23PaperP D * Real.exp (-3 * U)
  let f := lemma56PerronArithmeticIntegrand θ B x τ
  let R : ℂ := ∫ t : ℝ, f ((2 : ℂ) + (t : ℂ) * I)
  let S : ℂ := ∫ t : ℝ in -H..H, f ((2 : ℂ) + (t : ℂ) * I)
  let L : ℂ := ∫ t : ℝ in -H..H, f ((a : ℂ) + (t : ℂ) * I)
  let T : ℂ := ∫ σ : ℝ in a..2, f ((σ : ℂ) + (H : ℂ) * I)
  let Q : ℂ := ∫ σ : ℝ in a..2, f ((σ : ℂ) - (H : ℂ) * I)
  have hU0 : 0 ≤ U := by
    have hv : 2000 ≤ (3 / 4 : ℝ) * U := hscale.2.2.1
    linarith only [hv]
  have hB1 : 1 ≤ B := Real.one_le_exp (by positivity)
  have hB : 0 < B := Real.exp_pos _
  have hH : 0 < H := by dsimp [H]; positivity
  have hxp : 0 < x := by linarith only [hx]
  have hN0 : 0 ≤ N := by dsimp [N]; positivity
  have hN1 : N ≤ 1 := by
    dsimp [N]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith only [Real.two_le_pi]
  have h3 : A3 ≤ A := by
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    apply Real.exp_le_exp.mpr
    linarith only [hU0]
  have hshift : I * S = I * L + T - Q := hs χ θ
    ((le_max_left _ _).trans ((le_max_left _ _).trans hDN))
    hD hA hθ hq1 hqT hne hxp hH.le le_rfl hτ
  have hleft : N * ‖L‖ ≤ (2 * (2017218816 * Real.exp (1 / 4 : ℝ))) * A := by
    have hh := hl χ θ ((le_max_right _ _).trans ((le_max_left _ _).trans hDN))
      hD hA hθ hq1 hqT hne (B := B) (H := H) (τ := τ) (x := x)
      hx hxmax hB1 hH.le le_rfl hτ
    convert hh using 1 <;> ring
  have hexterior := he χ θ ((le_max_left _ _).trans ((le_max_right _ _).trans hDN))
    hD hA hθ hq1 hqT hne hx hxmax hτ
  have htop : ‖T‖ ≤ 1844736 * A := by
    have hh : ‖T‖ ≤ 1844736 * A3 := by convert hexterior.1 using 1 <;> ring
    exact hh.trans (mul_le_mul_of_nonneg_left h3 (by norm_num : (0 : ℝ) ≤ 1844736))
  have hbot : ‖Q‖ ≤ 1844736 * A := by
    have hh : ‖Q‖ ≤ 1844736 * A3 := by convert hexterior.2.1 using 1 <;> ring
    exact hh.trans (mul_le_mul_of_nonneg_left h3 (by norm_num : (0 : ℝ) ≤ 1844736))
  have htail : ‖R - S‖ ≤ (32 * lemma56GaussianRightConstant) * A := by
    have hh : ‖R - S‖ ≤ (32 * lemma56GaussianRightConstant) * A3 := by
      convert hexterior.2.2 using 1 <;> ring
    exact hh.trans (mul_le_mul_of_nonneg_left h3
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 32) hCr))
  have hNtop : N * ‖T‖ ≤ 1844736 * A :=
    ((mul_le_mul_of_nonneg_right hN1 (norm_nonneg _)).trans_eq (one_mul _)).trans htop
  have hNbot : N * ‖Q‖ ≤ 1844736 * A :=
    ((mul_le_mul_of_nonneg_right hN1 (norm_nonneg _)).trans_eq (one_mul _)).trans hbot
  have hNtail : N * ‖R - S‖ ≤ (32 * lemma56GaussianRightConstant) * A :=
    ((mul_le_mul_of_nonneg_right hN1 (norm_nonneg _)).trans_eq (one_mul _)).trans htail
  have hfinite := mul_le_mul_of_nonneg_left (lemma56_perron_rectangle_norm_budget hshift) hN0
  have htri : ‖R‖ ≤ ‖R - S‖ + ‖S‖ := by
    simpa only [sub_add_cancel] using norm_add_le (R - S) S
  have hNtri := mul_le_mul_of_nonneg_left htri hN0
  have hi : lemma56PerronMangoldtSum θ B x τ = (N : ℂ) * R := by
    have hh := lemma56_actual_perron_mellin_identity θ hB hxp τ
    simp_rw [← lemma56_actual_perron_right_eq] at hh
    exact hh.symm
  have hn : ‖lemma56PerronMangoldtSum θ B x τ‖ = N * ‖R‖ := by
    rw [hi, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hN0]
  change ‖lemma56PerronMangoldtSum θ B x τ‖ ≤ C * lemma23PaperP D * Real.exp (-((7 / 6 : ℝ) * U))
  rw [hn]
  change N * ‖R‖ ≤ _
  dsimp [C, A] at hleft hNtop hNbot hNtail ⊢
  nlinarith only [hNtri, hfinite, hleft, hNtop, hNbot, hNtail]

end ZhangLS.Spec
