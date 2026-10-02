import ZhangLS.Spec.Lemma55NearOneBound
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Quantitative derivatives of the actual L-function near one

A circle of radius 1/(4 log D) around any point in the closed disk of
that radius about one stays in the domain of the logarithmic Abel bound.
Cauchy's estimate therefore bounds the actual second derivative, and the
complex mean value inequality bounds the variation of the first derivative.
-/

namespace ZhangLS.Spec

open Complex Metric Set
open scoped Real

theorem lemma55_actual_second_derivative_bound
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2 ≤ Real.log (D : ℝ)) {s : ℂ}
    (hs : ‖s - 1‖ ≤ 1 / (4 * Real.log (D : ℝ))) :
    ‖deriv (deriv (dirichletLFunction χ)) s‖ ≤
      128 * Real.exp 1 * Real.log (D : ℝ) ^ 3 := by
  let L := Real.log (D : ℝ)
  let R := 1 / (4 * L)
  have hLp : 0 < L := by dsimp [L]; linarith
  have hRp : 0 < R := by dsimp [R]; positivity
  have hR2 : R + R ≤ 1 / L := by
    dsimp [R]
    field_simp
    linarith
  have hLinv : 1 / L ≤ (1 : ℝ) / 2 :=
    one_div_le_one_div_of_le (by norm_num) hL
  have hdiff := differentiable_dirichletLFunction_of_one_lt_modulus χ hD
  have hboundary (z : ℂ) (hz : z ∈ sphere s R) :
      ‖dirichletLFunction χ z‖ ≤ 4 * Real.exp 1 * L := by
    have hdist : ‖z - s‖ = R := mem_sphere_iff_norm.mp hz
    have hz1 : ‖z - 1‖ ≤ 1 / L := by
      calc
        _ = ‖(z - s) + (s - 1)‖ := by congr 1; ring
        _ ≤ ‖z - s‖ + ‖s - 1‖ := norm_add_le _ _
        _ ≤ R + R := by
          rw [hdist]
          simpa [R, L, add_comm] using add_le_add_left hs R
        _ ≤ 1 / L := hR2
    have hre : |z.re - 1| ≤ 1 / L := by
      simpa using (Complex.abs_re_le_norm (z - 1)).trans hz1
    have hσ : 1 - 1 / L ≤ z.re := by
      have hr := (abs_le.mp hre).1
      linarith
    have hnorm : ‖z‖ ≤ 2 := by
      have hnorm' : ‖z‖ ≤ ‖z - 1‖ + 1 := by
        simpa using norm_add_le (z - 1) (1 : ℂ)
      linarith
    exact lemma55_actual_L_near_one_bound χ hD hL hσ hnorm
  have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    (f := dirichletLFunction χ) (c := s) (R := R) (C := 4 * Real.exp 1 * L)
    2 hRp hdiff.diffContOnCl hboundary
  calc
    _ ≤ 2 * (4 * Real.exp 1 * L) / R ^ 2 := by
      simpa [iteratedDeriv_succ, Nat.factorial] using hc
    _ = 128 * Real.exp 1 * L ^ 3 := by
      dsimp [R]
      field_simp
      ring

theorem lemma55_actual_first_derivative_variation
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2 ≤ Real.log (D : ℝ)) {s : ℂ}
    (hs : ‖s - 1‖ ≤ 1 / (4 * Real.log (D : ℝ))) :
    ‖deriv (dirichletLFunction χ) s - LDerivAtOne χ‖ ≤
      (128 * Real.exp 1 * Real.log (D : ℝ) ^ 3) * ‖s - 1‖ := by
  let R := 1 / (4 * Real.log (D : ℝ))
  have hLp : 0 < Real.log (D : ℝ) := by linarith
  have hRp : 0 < R := by dsimp [R]; positivity
  have hdiff := differentiable_dirichletLFunction_of_one_lt_modulus χ hD
  have hd' (z : ℂ) (_hz : z ∈ closedBall (1 : ℂ) R) :
      DifferentiableAt ℂ (deriv (dirichletLFunction χ)) z :=
    (hdiff.analyticAt z).deriv.differentiableAt
  have hb (z : ℂ) (hz : z ∈ closedBall (1 : ℂ) R) :
      ‖deriv (deriv (dirichletLFunction χ)) z‖ ≤
        128 * Real.exp 1 * Real.log (D : ℝ) ^ 3 := by
    exact lemma55_actual_second_derivative_bound χ hD hL
      (mem_closedBall_iff_norm.mp hz)
  have hone : (1 : ℂ) ∈ closedBall (1 : ℂ) R := mem_closedBall_self hRp.le
  have hsmem : s ∈ closedBall (1 : ℂ) R := mem_closedBall_iff_norm.mpr hs
  simpa [LDerivAtOne] using
    Convex.norm_image_sub_le_of_norm_deriv_le hd' hb (convex_closedBall (1 : ℂ) R)
      hone hsmem

/-- A quadratic Taylor bound on the entire closed local disk. -/
theorem lemma55_actual_taylor_remainder_bound
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2 ≤ Real.log (D : ℝ)) {s : ℂ}
    (hs : ‖s - 1‖ ≤ 1 / (4 * Real.log (D : ℝ))) :
    ‖dirichletLFunction χ s - LAtOne χ - LDerivAtOne χ * (s - 1)‖ ≤
      (128 * Real.exp 1 * Real.log (D : ℝ) ^ 3) * ‖s - 1‖ ^ 2 := by
  let M := 128 * Real.exp 1 * Real.log (D : ℝ) ^ 3
  let g : ℂ → ℂ := fun z =>
    dirichletLFunction χ z - LAtOne χ - LDerivAtOne χ * (z - 1)
  have hdiff := differentiable_dirichletLFunction_of_one_lt_modulus χ hD
  have hg (z : ℂ) :
      HasDerivAt g (deriv (dirichletLFunction χ) z - LDerivAtOne χ) z := by
    simpa [g] using
      (((hdiff z).hasDerivAt.sub_const (LAtOne χ)).sub
        (((hasDerivAt_id z).sub_const 1).const_mul (LDerivAtOne χ)))
  have hb (z : ℂ) (hz : z ∈ closedBall (1 : ℂ) ‖s - 1‖) :
      ‖deriv g z‖ ≤ M * ‖s - 1‖ := by
    rw [(hg z).deriv]
    have hz1 : ‖z - 1‖ ≤ ‖s - 1‖ := mem_closedBall_iff_norm.mp hz
    exact (lemma55_actual_first_derivative_variation χ hD hL (hz1.trans hs)).trans
      (mul_le_mul_of_nonneg_left hz1 (by positivity))
  have hone : (1 : ℂ) ∈ closedBall (1 : ℂ) ‖s - 1‖ :=
    mem_closedBall_self (norm_nonneg _)
  have hsmem : s ∈ closedBall (1 : ℂ) ‖s - 1‖ := mem_closedBall_iff_norm.mpr le_rfl
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z _ => (hg z).differentiableAt) hb
    (convex_closedBall (1 : ℂ) ‖s - 1‖) hone hsmem
  simpa [g, LAtOne, M, pow_two, mul_assoc] using h

end ZhangLS.Spec
