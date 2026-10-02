import ZhangLS.Spec.Lemma57SmoothedSummability
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# The Mellin/contour interface for Zhang's Lemma 5.7

Zhang's displayed identity is

`(2πi)⁻¹ ∫_(1) ζ(1+s)L(1+s,χ) D^(4s) ω₁(s) ds/s
    = ∑ n, νχ(n)/n * g(D⁴/n)`.

This file fixes the exact complex integrand and the two vertical integrals that
occur when the line is moved from `re s = 1` to `re s = -1/2`.  It also computes
the coefficient of `s⁻¹` at the double pole `s = 0`.

An important bookkeeping point is that this coefficient is

`L'(1,χ) + (γ + 4 log D) L(1,χ)`,

not merely `L'(1,χ) + 4 log D L(1,χ)`: the Euler--Mascheroni term comes
from the constant term of `ζ(1+s)`.  The paper absorbs the entire `L(1,χ)`
contribution into `o(1)` under Assumption (A).

We prove the local residue calculation and the final quantitative transfer here.
The Mellin inversion, contour-shift identity, and bound for the explicit shifted
integral remain separately named analytic obligations.
-/

namespace ZhangLS.Spec

open Complex MeasureTheory
open scoped Real

/-- The pole-removed factor `s * ζ(1+s)`, continuously filled in at `s = 0`. -/
noncomputable def lemma57RegularizedZeta (s : ℂ) : ℂ :=
  if s = 0 then 1 else s * riemannZeta (1 + s)

@[simp] theorem lemma57RegularizedZeta_zero :
    lemma57RegularizedZeta 0 = 1 := by
  simp [lemma57RegularizedZeta]

/-- The derivative at zero of the regularized zeta factor is Euler's constant.
This is the exact constant term in the Laurent expansion of `ζ(1+s)`. -/
theorem lemma57RegularizedZeta_hasDerivAt_zero :
    HasDerivAt lemma57RegularizedZeta
      (Real.eulerMascheroniConstant : ℂ) 0 := by
  rw [hasDerivAt_iff_tendsto_slope, slope_fun_def_field]
  have hshift :
      Filter.Tendsto (fun s : ℂ => 1 + s)
        (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ)
        (nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ) := by
    have hderiv : HasDerivAt (fun s : ℂ => 1 + s) 1 0 := by
      simpa using (hasDerivAt_const (x := (0 : ℂ)) (1 : ℂ)).add
        (hasDerivAt_id (x := (0 : ℂ)))
    simpa using hderiv.tendsto_nhdsNE one_ne_zero
  have hgamma :
      Filter.Tendsto
        (fun s : ℂ => riemannZeta (1 + s) - 1 / s)
        (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ)
        (nhds (Real.eulerMascheroniConstant : ℂ)) := by
    have hcomp := tendsto_riemannZeta_sub_one_div.comp hshift
    refine hcomp.congr' (Filter.Eventually.of_forall ?_)
    intro s
    simp only [Function.comp_apply]
    congr 2
    ring
  refine hgamma.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : s ≠ 0 := by simpa using hs
  simp only [lemma57RegularizedZeta, if_neg hs0, if_pos, sub_zero]
  field_simp

/-- Zhang's Gaussian damping factor `ω₁(s)`. -/
noncomputable def lemma57OmegaOne (D : ℕ) (s : ℂ) : ℂ :=
  Complex.exp (s ^ 2 / (4 * (Real.log (D : ℝ) : ℂ) ^ 30))

/-- The entire factor `D^(4s) * ω₁(s)`, written with one exponential. -/
noncomputable def lemma57GaussianMellinFactor (D : ℕ) (s : ℂ) : ℂ :=
  Complex.exp
    ((4 * (Real.log (D : ℝ) : ℂ)) * s +
      s ^ 2 / (4 * (Real.log (D : ℝ) : ℂ) ^ 30))

/-- For a nontrivial modulus, the one-exponential definition is exactly the
product `D^(4s) * ω₁(s)` displayed in the paper. -/
theorem lemma57GaussianMellinFactor_eq_cpow_mul_omegaOne
    {D : ℕ} (hD : 1 < D) (s : ℂ) :
    lemma57GaussianMellinFactor D s =
      (D : ℂ) ^ (4 * s) * lemma57OmegaOne D s := by
  have hD0 : (D : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hD))
  rw [Complex.cpow_def_of_ne_zero hD0]
  simp only [lemma57GaussianMellinFactor, lemma57OmegaOne, ← Complex.exp_add]
  apply congrArg Complex.exp
  rw [← Complex.natCast_log]
  ring

@[simp] theorem lemma57GaussianMellinFactor_zero (D : ℕ) :
    lemma57GaussianMellinFactor D 0 = 1 := by
  simp [lemma57GaussianMellinFactor]

/-- The Gaussian Mellin factor has logarithmic derivative `4 log D` at zero;
the even Gaussian factor itself contributes no linear term. -/
theorem lemma57GaussianMellinFactor_hasDerivAt_zero (D : ℕ) :
    HasDerivAt (lemma57GaussianMellinFactor D)
      (4 * (Real.log (D : ℝ) : ℂ)) 0 := by
  let a : ℂ := 4 * (Real.log (D : ℝ) : ℂ)
  let b : ℂ := 4 * (Real.log (D : ℝ) : ℂ) ^ 30
  have hinner :
      HasDerivAt (fun s : ℂ => a * s + s ^ 2 / b) a 0 := by
    convert ((hasDerivAt_id (x := (0 : ℂ))).const_mul a).add
      (((hasDerivAt_id (x := (0 : ℂ))).pow 2).div_const b) using 1
    all_goals simp
  change HasDerivAt
    (fun s : ℂ => Complex.exp
      ((4 * (Real.log (D : ℝ) : ℂ)) * s +
        s ^ 2 / (4 * (Real.log (D : ℝ) : ℂ) ^ 30)))
    (4 * (Real.log (D : ℝ) : ℂ)) 0
  simpa [a, b] using hinner.cexp

/-- The analytic numerator after removing the double pole `s⁻²`. -/
noncomputable def lemma57ResidueNumerator {D : ℕ}
    (χ : RealPrimitiveCharacter D) (s : ℂ) : ℂ :=
  lemma57RegularizedZeta s *
    dirichletLFunction χ (1 + s) * lemma57GaussianMellinFactor D s

/-- The exact coefficient of `s⁻¹` in Zhang's integrand at zero. -/
noncomputable def lemma57ResidueValue {D : ℕ}
    (χ : RealPrimitiveCharacter D) : ℂ :=
  LDerivAtOne χ +
    ((Real.eulerMascheroniConstant + 4 * Real.log (D : ℝ) : ℝ) : ℂ) * LAtOne χ

@[simp] theorem lemma57ResidueNumerator_zero
    {D : ℕ} (χ : RealPrimitiveCharacter D) :
    lemma57ResidueNumerator χ 0 = LAtOne χ := by
  simp [lemma57ResidueNumerator, LAtOne]

/-- Kernel-checked local residue computation.  The numerator has value `L(1,χ)`
at zero and derivative equal to the coefficient of `s⁻¹` after division by
`s²`. -/
theorem lemma57ResidueNumerator_hasDerivAt_zero
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    HasDerivAt (lemma57ResidueNumerator χ) (lemma57ResidueValue χ) 0 := by
  have hLbase :
      HasDerivAt (dirichletLFunction χ) (LDerivAtOne χ) 1 := by
    simpa [LDerivAtOne] using
      (differentiable_dirichletLFunction_of_one_lt_modulus χ hD).differentiableAt.hasDerivAt
  have hshift : HasDerivAt (fun s : ℂ => 1 + s) 1 0 := by
    simpa using (hasDerivAt_const (x := (0 : ℂ)) (1 : ℂ)).add
      (hasDerivAt_id (x := (0 : ℂ)))
  have hL :
      HasDerivAt (fun s : ℂ => dirichletLFunction χ (1 + s))
        (LDerivAtOne χ) 0 := by
    have hLbase' :
        HasDerivAt (dirichletLFunction χ) (LDerivAtOne χ) (1 + (0 : ℂ)) := by
      simpa using hLbase
    simpa [Function.comp_def] using
      HasDerivAt.comp (0 : ℂ) hLbase' hshift
  have h :=
    (lemma57RegularizedZeta_hasDerivAt_zero.mul hL).mul
      (lemma57GaussianMellinFactor_hasDerivAt_zero D)
  convert h using 1
  all_goals (simp [lemma57ResidueValue, LAtOne] ; ring)

/-- In the half-plane of absolute convergence, the product `ζ(s)L(s,χ)` is
the L-series of the actual divisor-character coefficient used by the Gaussian
sum.  This is the Dirichlet-series algebra underlying Mellin inversion. -/
theorem lemma57DirichletProduct_eq_divisorCharacterLSeries
    {D : ℕ} (χ : RealPrimitiveCharacter D) {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s * dirichletLFunction χ s =
      LSeries (divisorCharacterSum χ) s := by
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  rw [dirichletLFunction_eq_series χ hs]
  symm
  calc
    LSeries (divisorCharacterSum χ) s = LSeries χ.chi.zetaMul s := by
      exact LSeries_congr (fun {_n} _hn => divisorCharacterSum_eq_zetaMul χ) s
    _ = riemannZeta s * dirichletLSeries χ s := by
      rw [DirichletCharacter.zetaMul, ← ArithmeticFunction.coe_mul,
        LSeries_convolution']
      · congr 1
        · simp_rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs,
            ← ArithmeticFunction.natCoe_apply]
        · simpa [dirichletLSeries, dirichletCoeffs] using
            (LSeries_congr χ.chi.apply_eq_toArithmeticFunction_apply s).symm
      · exact ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs
      · exact
          (LSeriesSummable_congr _ fun h =>
            (χ.chi.apply_eq_toArithmeticFunction_apply h).symm).mpr
            (ZMod.LSeriesSummable_of_one_lt_re χ.chi hs)

/-- The genuine singular integrand in Zhang's displayed Mellin identity. -/
noncomputable def lemma57MellinIntegrand {D : ℕ}
    (χ : RealPrimitiveCharacter D) (s : ℂ) : ℂ :=
  riemannZeta (1 + s) * dirichletLFunction χ (1 + s) *
    lemma57GaussianMellinFactor D s / s

/-- Away from zero, the displayed Mellin integrand is the analytic residue
numerator divided by `s²`.  This ties the local derivative calculation above to
the actual singular integrand rather than to an unrelated auxiliary function. -/
theorem lemma57MellinIntegrand_eq_residueNumerator_div_sq
    {D : ℕ} (χ : RealPrimitiveCharacter D) {s : ℂ} (hs : s ≠ 0) :
    lemma57MellinIntegrand χ s = lemma57ResidueNumerator χ s / s ^ 2 := by
  simp only [lemma57MellinIntegrand, lemma57ResidueNumerator,
    lemma57RegularizedZeta, if_neg hs]
  field_simp

/-- The normalized improper integral on the vertical line `re s = σ`, with
`s = σ + it` and hence `ds = i dt`. -/
noncomputable def lemma57VerticalIntegral {D : ℕ}
    (χ : RealPrimitiveCharacter D) (σ : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ) * I)⁻¹ *
    ∫ t : ℝ, lemma57MellinIntegrand χ ((σ : ℂ) + (t : ℂ) * I) * I

/-- The honest integrability condition behind a vertical integral.  It is kept
explicit because the Bochner integral has a default value when integrability is
not proved. -/
def Lemma57VerticalIntegrable {D : ℕ}
    (χ : RealPrimitiveCharacter D) (σ : ℝ) : Prop :=
  Integrable
    (fun t : ℝ => lemma57MellinIntegrand χ ((σ : ℂ) + (t : ℂ) * I) * I)

/-- Exact Mellin inversion obligation, tied to the actual full Gaussian sum. -/
def Lemma57MellinIdentity {D : ℕ} (χ : RealPrimitiveCharacter D) : Prop :=
  Lemma57VerticalIntegrable χ 1 ∧
    lemma57VerticalIntegral χ 1 =
      (lemma57FullSmoothedSum χ (zhangGaussianWeight D) : ℂ)

/-- Exact contour-shift obligation from `re s = 1` to `re s = -1/2`. -/
def Lemma57ContourShiftIdentity {D : ℕ} (χ : RealPrimitiveCharacter D) : Prop :=
  Lemma57VerticalIntegrable χ (-(1 : ℝ) / 2) ∧
    lemma57VerticalIntegral χ 1 =
      lemma57ResidueValue χ + lemma57VerticalIntegral χ (-(1 : ℝ) / 2)

/-- The real `L(1,χ)` correction in the exact residue. -/
noncomputable def lemma57ResidueCorrection {D : ℕ}
    (χ : RealPrimitiveCharacter D) : ℝ :=
  (Real.eulerMascheroniConstant + 4 * Real.log (D : ℝ)) * realLAtOne χ

/-- The real part of the exact residue coefficient. -/
theorem lemma57ResidueValue_re
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    (lemma57ResidueValue χ).re =
      realLDerivAtOne χ + lemma57ResidueCorrection χ := by
  rw [lemma57ResidueValue, Complex.add_re, realLDerivAtOne_eq_re χ hD]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [lemma57ResidueCorrection, realLAtOne_eq_re]

/-- The two honest error terms after the residue is separated: the explicit
`L(1,χ)` correction and the real part of the actual shifted vertical integral. -/
noncomputable def lemma57AnalyticError {D : ℕ}
    (χ : RealPrimitiveCharacter D) : ℝ :=
  |lemma57ResidueCorrection χ| +
    |(lemma57VerticalIntegral χ (-(1 : ℝ) / 2)).re|

theorem lemma57AnalyticError_nonneg {D : ℕ}
    (χ : RealPrimitiveCharacter D) : 0 ≤ lemma57AnalyticError χ := by
  exact add_nonneg (abs_nonneg _) (abs_nonneg _)

/-- Mellin inversion plus the exact contour shift gives an approximation to
`L'(1,χ)` with precisely the two displayed analytic error terms. -/
theorem lemma57_mellin_contour_approximation
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hmellin : Lemma57MellinIdentity χ)
    (hshift : Lemma57ContourShiftIdentity χ) :
    |lemma57FullSmoothedSum χ (zhangGaussianWeight D) - realLDerivAtOne χ| ≤
      lemma57AnalyticError χ := by
  have hcomplex :
      (lemma57FullSmoothedSum χ (zhangGaussianWeight D) : ℂ) =
        lemma57ResidueValue χ + lemma57VerticalIntegral χ (-(1 : ℝ) / 2) := by
    exact hmellin.2.symm.trans hshift.2
  have hreal := congrArg Complex.re hcomplex
  rw [Complex.add_re, Complex.ofReal_re, lemma57ResidueValue_re χ hD] at hreal
  have hdiff :
      lemma57FullSmoothedSum χ (zhangGaussianWeight D) - realLDerivAtOne χ =
        lemma57ResidueCorrection χ +
          (lemma57VerticalIntegral χ (-(1 : ℝ) / 2)).re := by
    rw [hreal]
    ring
  rw [hdiff]
  unfold lemma57AnalyticError
  exact abs_add_le (lemma57ResidueCorrection χ)
    (lemma57VerticalIntegral χ (-(1 : ℝ) / 2)).re

/-- A concrete error budget matching half of the proved arithmetic constant
`1/8`.  This proposition mentions only explicit analytic objects. -/
def Lemma57GaussianAnalyticErrorBound {D : ℕ}
    (χ : RealPrimitiveCharacter D) : Prop :=
  lemma57AnalyticError χ ≤ (1 : ℝ) / 16 * lemma57Scale D

/-- The deep transfer theorem for the Gaussian route: the already-proved
arithmetic lower bound and the three explicit analytic obligations imply the
paper's derivative lower bound with constant `1/16`. -/
theorem lemma57_gaussian_mellin_contour_transfer
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hmellin : Lemma57MellinIdentity χ)
    (hshift : Lemma57ContourShiftIdentity χ)
    (herror : Lemma57GaussianAnalyticErrorBound χ) :
    (1 : ℝ) / 16 * lemma57Scale D ≤ realLDerivAtOne χ := by
  have harith := lemma57_full_gaussian_arithmetic_scale_proved χ hD
  have happ := lemma57_mellin_contour_approximation χ hD hmellin hshift
  have honeSided :
      lemma57FullSmoothedSum χ (zhangGaussianWeight D) - realLDerivAtOne χ ≤
        lemma57AnalyticError χ := le_trans (le_abs_self _) happ
  dsimp [Lemma57GaussianAnalyticErrorBound] at herror
  nlinarith

/-- Uniform forms of the three analytic obligations prove Lemma 5.7 at the
explicit constant `1/16`. -/
theorem lemma57AtConstant_one_sixteenth_of_mellin_contour
    (hmellin : ∀ {D : ℕ} (χ : RealPrimitiveCharacter D),
      1 < D → Lemma57MellinIdentity χ)
    (hshift : ∀ {D : ℕ} (χ : RealPrimitiveCharacter D),
      1 < D → Lemma57ContourShiftIdentity χ)
    (herror : ∀ {D : ℕ} (χ : RealPrimitiveCharacter D),
      1 < D → NormalizedAssumptionA χ → Lemma57GaussianAnalyticErrorBound χ) :
    Lemma57AtConstant ((1 : ℝ) / 16) := by
  constructor
  · norm_num
  · refine ⟨2, ?_⟩
    intro D χ _ hD hA
    exact lemma57_gaussian_mellin_contour_transfer χ hD
      (hmellin χ hD) (hshift χ hD) (herror χ hD hA)

/-- The same uniform inputs close the paper-level target for Lemma 5.7. -/
theorem lemma57Target_of_mellin_contour
    (hmellin : ∀ {D : ℕ} (χ : RealPrimitiveCharacter D),
      1 < D → Lemma57MellinIdentity χ)
    (hshift : ∀ {D : ℕ} (χ : RealPrimitiveCharacter D),
      1 < D → Lemma57ContourShiftIdentity χ)
    (herror : ∀ {D : ℕ} (χ : RealPrimitiveCharacter D),
      1 < D → NormalizedAssumptionA χ → Lemma57GaussianAnalyticErrorBound χ) :
    Lemma57Target := by
  exact ⟨(1 : ℝ) / 16,
    lemma57AtConstant_one_sixteenth_of_mellin_contour hmellin hshift herror⟩

end ZhangLS.Spec
