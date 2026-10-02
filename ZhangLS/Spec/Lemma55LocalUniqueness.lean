import ZhangLS.Spec.Lemma55SimpleRealZero

/-!
# Local uniqueness of the actual exceptional zero

The proved first-derivative variation gives injectivity on the full complex
closed disk of radius 64(log D)^(-2022) about one. This is a local statement;
the larger original region in Lemma 5.5 is retained in the separate target.
-/

namespace ZhangLS.Spec

open Complex Metric Set
open scoped Real

theorem lemma55_actual_local_zero_unique
    {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hDN : lemma57ExplicitModulusThreshold ≤ D) (hA : NormalizedAssumptionA χ)
    {s t : ℂ} (hs : ‖s - 1‖ ≤ lemma55RealZeroWidth D)
    (ht : ‖t - 1‖ ≤ lemma55RealZeroWidth D)
    (hLs : dirichletLFunction χ s = 0) (hLt : dirichletLFunction χ t = 0) :
    s = t := by
  have hD := lemma57_one_lt_of_explicit_threshold hDN
  have hL : 2 ≤ Real.log (D : ℝ) := by
    linarith only [lemma57_log_ge_ten_million hDN]
  have hb := lemma55_local_zero_budget hDN
  let a := LDerivAtOne χ
  let g : ℂ → ℂ := fun z => dirichletLFunction χ z - a * z
  have hdiff := differentiable_dirichletLFunction_of_one_lt_modulus χ hD
  have hg (z : ℂ) : HasDerivAt g (deriv (dirichletLFunction χ) z - a) z := by
    simpa [g] using ((hdiff z).hasDerivAt.sub ((hasDerivAt_id z).const_mul a))
  have hgBound (z : ℂ) (hz : z ∈ closedBall (1 : ℂ) (lemma55RealZeroWidth D)) :
      ‖deriv g z‖ ≤ (1 : ℝ) / 32 := by
    rw [(hg z).deriv]
    have hz1 : ‖z - 1‖ ≤ lemma55RealZeroWidth D := mem_closedBall_iff_norm.mp hz
    exact (lemma55_actual_first_derivative_variation χ hD hL (hz1.trans hb.2.1)).trans
      ((mul_le_mul_of_nonneg_left hz1 (by positivity)).trans hb.2.2)
  have hm := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z _ => (hg z).differentiableAt) hgBound
    (convex_closedBall (1 : ℂ) (lemma55RealZeroWidth D))
    (mem_closedBall_iff_norm.mpr ht) (mem_closedBall_iff_norm.mpr hs)
  have hid : g s - g t = -(a * (s - t)) := by
    dsimp [g]
    rw [hLs, hLt]
    ring
  rw [hid, norm_neg, norm_mul] at hm
  have hader : (1 : ℝ) / 16 ≤ realLDerivAtOne χ := by
    have hd := lemma57_one_sixteenth_at_explicit_threshold χ hDN hA
    have hscale := lemma57Scale_ge_one hD
    nlinarith only [hd, hscale]
  have ha : (1 : ℝ) / 16 ≤ ‖a‖ := by
    dsimp [a]
    rw [LDerivAtOne_eq_realLDerivAtOne χ hD, Complex.norm_real, Real.norm_eq_abs]
    exact hader.trans (le_abs_self _)
  have hnorm : ‖s - t‖ = 0 := by
    have hscaled := mul_le_mul_of_nonneg_right ha (norm_nonneg (s - t))
    nlinarith only [hm, hscaled, norm_nonneg (s - t)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

theorem lemma55_actual_simple_real_zero_locally_unique
    {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hDN : lemma57ExplicitModulusThreshold ≤ D) (hA : NormalizedAssumptionA χ) :
    ∃ ρ : ℝ, 0 < 1 - ρ ∧
      1 - ρ ≤ 64 * Real.log (D : ℝ) ^ (-2022 : ℤ) ∧
      dirichletLFunction χ (ρ : ℂ) = 0 ∧
      deriv (dirichletLFunction χ) (ρ : ℂ) ≠ 0 ∧
      ∀ s : ℂ, ‖s - 1‖ ≤ lemma55RealZeroWidth D →
        dirichletLFunction χ s = 0 → s = (ρ : ℂ) := by
  obtain ⟨ρ, hρleft, hρwidth, hρzero, hρsimple⟩ :=
    lemma55_actual_simple_real_zero χ hDN hA
  refine ⟨ρ, hρleft, hρwidth, hρzero, hρsimple, ?_⟩
  intro s hs hLs
  apply lemma55_actual_local_zero_unique χ hDN hA hs _ hLs hρzero
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos (by linarith only [hρleft] : ρ - 1 ≤ 0)]
  simpa [lemma55RealZeroWidth] using hρwidth

end ZhangLS.Spec
