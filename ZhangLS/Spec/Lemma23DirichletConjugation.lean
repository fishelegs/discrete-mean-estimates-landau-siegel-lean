import ZhangLS.Spec.DirichletLSeries
import ZhangLS.Spec.Lemma23RealSign
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Conjugation symmetry for Dirichlet L-functions in Lemma 2.3

This module establishes the conjugation symmetry of the actual analytically
continued Dirichlet L-function, rather than treating that symmetry as an
assumption of the vertical-line sign argument.
-/

namespace ZhangLS.Spec

open ComplexConjugate
open scoped Topology

variable {N : ℕ} [NeZero N]

/-- Termwise conjugation of a Dirichlet L-series replaces its character by
the inverse and conjugates the complex parameter. -/
theorem dirichletLSeries_inv_eq_conj_at_conj
    (χ : DirichletCharacter ℂ N) (s : ℂ) :
    LSeries (χ⁻¹ ·) s = conj (LSeries (χ ·) (conj s)) := by
  rw [LSeries, LSeries, Complex.conj_tsum]
  apply tsum_congr
  intro n
  rcases n with _ | n
  · simp [LSeries.term]
  · have hchar : conj (χ ((n + 1 : ℕ) : ZMod N)) =
        χ⁻¹ ((n + 1 : ℕ) : ZMod N) := by
      exact MulChar.star_apply' χ ((n + 1 : ℕ) : ZMod N)
    have harg : (((n + 1 : ℕ) : ℂ).arg) ≠ Real.pi := by
      rw [show (((n + 1 : ℕ) : ℂ).arg) = 0 from Complex.natCast_arg]
      exact Real.pi_ne_zero.symm
    have hpow : conj (((n + 1 : ℕ) : ℂ) ^ conj s) =
        ((n + 1 : ℕ) : ℂ) ^ s := by
      rw [Complex.cpow_conj _ _ harg]
      simp
    have hpow' : star (((n + 1 : ℕ) : ℂ) ^ conj s) =
        ((n + 1 : ℕ) : ℂ) ^ s := by
      simpa only [starRingEnd_apply] using hpow
    rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n),
      LSeries.term_of_ne_zero (Nat.succ_ne_zero n)]
    change χ⁻¹ ((n + 1 : ℕ) : ZMod N) / ((n + 1 : ℕ) : ℂ) ^ s =
      star (χ ((n + 1 : ℕ) : ZMod N) / ((n + 1 : ℕ) : ℂ) ^ conj s)
    rw [star_div₀, hchar.symm, starRingEnd_apply, hpow']

/-- Analytic continuation preserves the conjugation symmetry of the Dirichlet
L-series: the L-function of the inverse character is the conjugate-reflection
of the original L-function. -/
theorem dirichletLFunction_inv_eq_conj_at_conj
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (s : ℂ) :
    DirichletCharacter.LFunction χ⁻¹ s =
      conj (DirichletCharacter.LFunction χ (conj s)) := by
  have hinv : χ⁻¹ ≠ 1 := by
    intro h
    exact hχ (inv_eq_one.mp h)
  let f : ℂ → ℂ := DirichletCharacter.LFunction χ⁻¹
  let g : ℂ → ℂ := fun z => conj (DirichletCharacter.LFunction χ (conj z))
  have hf : Differentiable ℂ f := by
    simpa [f] using DirichletCharacter.differentiable_LFunction (χ := χ⁻¹) hinv
  have hg : Differentiable ℂ g := by
    intro z
    have hz :=
      (DirichletCharacter.differentiable_LFunction (χ := χ) hχ) (conj z)
    simpa [g, Function.comp_def] using hz.conj_conj
  have hfAnalytic : AnalyticOnNhd ℂ f Set.univ := by
    refine DifferentiableOn.analyticOnNhd (fun z _ => (hf z).differentiableWithinAt)
      isOpen_univ
  have hgAnalytic : AnalyticOnNhd ℂ g Set.univ := by
    refine DifferentiableOn.analyticOnNhd (fun z _ => (hg z).differentiableWithinAt)
      isOpen_univ
  have hregion : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  have hnear : f =ᶠ[𝓝 (2 : ℂ)] g := by
    filter_upwards [hregion] with z hz
    have hconjRegion : 1 < (conj z).re := by simpa using hz
    dsimp [f, g]
    calc
      DirichletCharacter.LFunction χ⁻¹ z = LSeries (χ⁻¹ ·) z :=
        DirichletCharacter.LFunction_eq_LSeries χ⁻¹ hz
      _ = conj (LSeries (χ ·) (conj z)) :=
        dirichletLSeries_inv_eq_conj_at_conj χ z
      _ = conj (DirichletCharacter.LFunction χ (conj z)) := by
        rw [← DirichletCharacter.LFunction_eq_LSeries χ hconjRegion]
  have heq := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    hfAnalytic hgAnalytic isPreconnected_univ (Set.mem_univ (2 : ℂ)) hnear
  exact heq (Set.mem_univ s)

/-- On the critical line, conjugation is the functional-equation reflection
` s ↦ 1 - s `.  This converts the global conjugation symmetry into exactly
the inverse-character term occurring in Zhang's Lemma 2.3. -/
theorem dirichletLFunction_inv_eq_conj_reflection_critical
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (ρ : ℂ) (hρ : ρ.re = 1 / 2) (t : ℝ) :
    DirichletCharacter.LFunction χ⁻¹ (1 - (ρ + Complex.I * (t : ℂ))) =
      conj (DirichletCharacter.LFunction χ (ρ + Complex.I * (t : ℂ))) := by
  have hreflection : conj (ρ + Complex.I * (t : ℂ)) =
      1 - (ρ + Complex.I * (t : ℂ)) := by
    apply Complex.ext <;>
      simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.I_re, Complex.I_im, hρ] <;> ring
  rw [← hreflection]
  simpa using dirichletLFunction_inv_eq_conj_at_conj χ hχ
    (conj (ρ + Complex.I * (t : ℂ)))

/-- For the actual analytically continued Dirichlet L-functions, the only
remaining input to the normalized reality argument is the functional equation
and the square-root factor: conjugation symmetry is supplied by mathlib's
Dirichlet-character structure and analytic continuation. -/
theorem lemma23_M_real_on_critical_line_of_dirichlet_LFunction
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (M Y Z : ℂ → ℂ) (ρ : ℂ) (hρ : ρ.re = 1 / 2)
    (hfactor : ∀ t : ℝ,
      M (ρ + Complex.I * (t : ℂ)) =
        Y (ρ + Complex.I * (t : ℂ)) * DirichletCharacter.LFunction χ
          (ρ + Complex.I * (t : ℂ)))
    (hLfunctional : ∀ t : ℝ,
      DirichletCharacter.LFunction χ (ρ + Complex.I * (t : ℂ)) =
        Z (ρ + Complex.I * (t : ℂ)) *
          DirichletCharacter.LFunction χ⁻¹
            (1 - (ρ + Complex.I * (t : ℂ))))
    (hYsquare : ∀ t : ℝ,
      (Y (ρ + Complex.I * (t : ℂ))) ^ 2 =
        (Z (ρ + Complex.I * (t : ℂ)))⁻¹)
    (hZnorm : ∀ t : ℝ, ‖Z (ρ + Complex.I * (t : ℂ))‖ = 1) :
    ∀ t : ℝ, (M (ρ + Complex.I * (t : ℂ))).im = 0 := by
  exact lemma23_M_real_on_critical_line_of_square_root M Y
    (DirichletCharacter.LFunction χ) (DirichletCharacter.LFunction χ⁻¹) Z ρ
    hfactor hLfunctional hYsquare hZnorm
    (fun t => dirichletLFunction_inv_eq_conj_reflection_critical χ hχ ρ hρ t)

end ZhangLS.Spec
