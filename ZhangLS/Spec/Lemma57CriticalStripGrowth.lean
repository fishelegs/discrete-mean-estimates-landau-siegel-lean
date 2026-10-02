import ZhangLS.Spec.Lemma57ContourGrowth
import ZhangLS.Spec.RiemannZetaCriticalLineBound

set_option maxHeartbeats 500000

/-!
# Isolating the genuine critical-strip growth input

Step 40 used an exponential bound on the whole rectangle strip.  The right
half of that strip is already inside absolute convergence after the shift
`s ↦ 1 + s`; this module proves its uniform boundedness directly from the
Dirichlet series.  Consequently the only remaining growth input is the true
critical half-strip `-1/2 ≤ re s ≤ 1/2`.
-/

namespace ZhangLS.Spec

open Complex Filter
open scoped Real Topology

private theorem norm_LSeries_le_tsum_norm_at_re
    {f : ℕ → ℂ} {s s₀ : ℂ} (hre : s₀.re ≤ s.re)
    (hs₀ : LSeriesSummable f s₀) :
    ‖LSeries f s‖ ≤ ∑' n : ℕ, ‖LSeries.term f s₀ n‖ := by
  have hs : LSeriesSummable f s := hs₀.of_re_le_re hre
  unfold LSeries
  exact (norm_tsum_le_tsum_norm hs.norm).trans
    (hs.norm.tsum_le_tsum
      (LSeries.norm_term_le_of_re_le_re f hre) hs₀.norm)

/-- A finite uniform majorant for zeta in the half-plane `re s ≥ 3/2`. -/
noncomputable def lemma57ZetaRightHalfBound : ℝ :=
  ∑' n : ℕ, ‖LSeries.term (1 : ℕ → ℂ) ((3 / 2 : ℝ) : ℂ) n‖

/-- A finite uniform majorant for the Dirichlet L-function in the half-plane
`re s ≥ 3/2`. -/
noncomputable def lemma57DirichletLRightHalfBound {D : ℕ}
    (χ : RealPrimitiveCharacter D) : ℝ :=
  ∑' n : ℕ,
    ‖LSeries.term (dirichletCoeffs χ) ((3 / 2 : ℝ) : ℂ) n‖

theorem lemma57ZetaRightHalfBound_nonneg :
    0 ≤ lemma57ZetaRightHalfBound := by
  exact tsum_nonneg fun _ => norm_nonneg _

theorem lemma57DirichletLRightHalfBound_nonneg
    {D : ℕ} (χ : RealPrimitiveCharacter D) :
    0 ≤ lemma57DirichletLRightHalfBound χ := by
  exact tsum_nonneg fun _ => norm_nonneg _

/-- The actual Riemann zeta function is uniformly bounded on
`re s ≥ 3/2` by an explicit convergent majorant. -/
theorem riemannZeta_norm_le_rightHalfBound {s : ℂ}
    (hs : (3 : ℝ) / 2 ≤ s.re) :
    ‖riemannZeta s‖ ≤ lemma57ZetaRightHalfBound := by
  have hsone : 1 < s.re := by linarith
  have hsum : LSeriesSummable (1 : ℕ → ℂ) (((3 / 2 : ℝ) : ℂ)) :=
    LSeriesSummable_of_bounded_of_one_lt_re
      (m := 1) (fun _ _ => by simp) (by norm_num)
  have hbound := norm_LSeries_le_tsum_norm_at_re
    (f := (1 : ℕ → ℂ)) (s := s) (s₀ := ((3 / 2 : ℝ) : ℂ))
    (by simpa using hs) hsum
  rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hsone,
    ArithmeticFunction.LSeries_zeta_eq]
  exact hbound

/-- The actual Dirichlet L-function is uniformly bounded on
`re s ≥ 3/2` by its absolutely convergent majorant. -/
theorem dirichletLFunction_norm_le_rightHalfBound
    {D : ℕ} (χ : RealPrimitiveCharacter D) {s : ℂ}
    (hs : (3 : ℝ) / 2 ≤ s.re) :
    ‖dirichletLFunction χ s‖ ≤ lemma57DirichletLRightHalfBound χ := by
  have hsone : 1 < s.re := by linarith
  rw [dirichletLFunction_eq_series χ hsone]
  exact norm_LSeries_le_tsum_norm_at_re
    (f := dirichletCoeffs χ) (s := s) (s₀ := ((3 / 2 : ℝ) : ℂ))
    (by simpa using hs)
    (dirichletLSeries_summable_of_one_lt_re χ (by norm_num))

/-- On the right half of the contour strip, the undamped factor is bounded
unconditionally by absolute convergence. -/
theorem lemma57UndampedMellinFactor_norm_le_rightHalf
    {D : ℕ} (χ : RealPrimitiveCharacter D)
    {σ t : ℝ} (hσ : (1 : ℝ) / 2 ≤ σ)
    (hsnorm : (1 : ℝ) / 2 ≤ ‖(σ : ℂ) + (t : ℂ) * I‖) :
    ‖lemma57UndampedMellinFactor χ ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      2 * (lemma57ZetaRightHalfBound *
        lemma57DirichletLRightHalfBound χ) := by
  let s : ℂ := (σ : ℂ) + (t : ℂ) * I
  have hre : (3 : ℝ) / 2 ≤ (1 + s).re := by
    norm_num [s]
    linarith
  have hz := riemannZeta_norm_le_rightHalfBound hre
  have hL := dirichletLFunction_norm_le_rightHalfBound χ hre
  have hspos : 0 < ‖s‖ := lt_of_lt_of_le (by norm_num) hsnorm
  rw [lemma57UndampedMellinFactor, norm_div, norm_mul]
  calc
    ‖riemannZeta (1 + s)‖ * ‖dirichletLFunction χ (1 + s)‖ / ‖s‖ ≤
        (lemma57ZetaRightHalfBound *
          lemma57DirichletLRightHalfBound χ) / ‖s‖ := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul hz hL (norm_nonneg _)
          lemma57ZetaRightHalfBound_nonneg) (norm_nonneg _)
    _ ≤ 2 * (lemma57ZetaRightHalfBound *
          lemma57DirichletLRightHalfBound χ) := by
      apply (div_le_iff₀ hspos).2
      have hprod : 0 ≤ lemma57ZetaRightHalfBound *
          lemma57DirichletLRightHalfBound χ :=
        mul_nonneg lemma57ZetaRightHalfBound_nonneg
          (lemma57DirichletLRightHalfBound_nonneg χ)
      nlinarith

/-- The genuinely unresolved growth input is only the critical half-strip.
The norm cutoff keeps the statement away from the double pole at `s = 0`. -/
def Lemma57CriticalStripExponentialGrowth {D : ℕ}
    (χ : RealPrimitiveCharacter D) : Prop :=
  ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧
    ∀ (σ t : ℝ), -(1 : ℝ) / 2 ≤ σ → σ ≤ (1 : ℝ) / 2 →
      (1 : ℝ) / 2 ≤ ‖(σ : ℂ) + (t : ℂ) * I‖ →
      ‖lemma57UndampedMellinFactor χ ((σ : ℂ) + (t : ℂ) * I)‖ ≤
        C * Real.exp (A * |t|)

/-- A sharper, polynomial estimate on the same half-strip. This is the useful
input for the quantitative Gaussian error (the exponential version alone is
too coarse for that purpose). -/
theorem lemma57UndampedMellinFactor_norm_le_quadratic
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    {σ t : ℝ} (hσlo : -(1 : ℝ) / 2 ≤ σ)
    (hσhi : σ ≤ (1 : ℝ) / 2)
    (hsnorm : (1 : ℝ) / 2 ≤ ‖(σ : ℂ) + (t : ℂ) * I‖) :
    ‖lemma57UndampedMellinFactor χ ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      288 * (D : ℝ) * (1 + t ^ 2) := by
  let s : ℂ := (σ : ℂ) + (t : ℂ) * I
  let z : ℂ := 1 + s
  have hsnormS : (1 : ℝ) / 2 ≤ ‖s‖ := by simpa [s] using hsnorm
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hsnormS
    norm_num at hsnormS
  have hsNormPos : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  have hzre : (1 : ℝ) / 2 ≤ z.re := by
    norm_num [z, s]
    linarith
  have hzpos : 0 < z.re := lt_of_lt_of_le (by norm_num) hzre
  have hz1 : z ≠ 1 := by
    intro h
    have hsEq : s = 0 := by
      have hh : 1 + s = 1 + 0 := by simpa [z] using h
      exact add_left_cancel hh
    exact hs0 hsEq
  have hzeta := norm_riemannZeta_le_fractionalPart_formula hzpos hz1
  have hnormSub : ‖z - 1‖ = ‖s‖ := by simp [z]
  have hleftDen : 0 < ‖z - 1‖ := by rw [hnormSub]; exact hsNormPos
  have hzDiv : ‖z‖ / ‖z - 1‖ ≤ 2 * ‖z‖ := by
    rw [hnormSub]
    apply (div_le_iff₀ hsNormPos).2
    have hmul := mul_le_mul_of_nonneg_left hsnormS (norm_nonneg z)
    nlinarith
  have hrightDiv : ‖z‖ / z.re ≤ 2 * ‖z‖ := by
    apply (div_le_iff₀ hzpos).2
    nlinarith [hzre, norm_nonneg z]
  have hζ : ‖riemannZeta z‖ ≤ 4 * ‖z‖ := by
    calc
      ‖riemannZeta z‖ ≤ ‖z‖ / ‖z - 1‖ + ‖z‖ / z.re := hzeta
      _ ≤ 2 * ‖z‖ + 2 * ‖z‖ := add_le_add hzDiv hrightDiv
      _ = 4 * ‖z‖ := by ring
  have hzL := χ.norm_dirichletLFunction_le_of_pos_re hD hzpos
  have hDnonneg : 0 ≤ (D : ℝ) := Nat.cast_nonneg D
  have hLcoef : (D : ℝ) / z.re ≤ 2 * (D : ℝ) := by
    apply (div_le_iff₀ hzpos).2
    nlinarith [hzre, hDnonneg]
  have hL : ‖dirichletLFunction χ z‖ ≤ 2 * (D : ℝ) * ‖z‖ := by
    calc
      ‖dirichletLFunction χ z‖ ≤ ‖z‖ * ((D : ℝ) / z.re) := hzL
      _ ≤ ‖z‖ * (2 * (D : ℝ)) :=
        mul_le_mul_of_nonneg_left hLcoef (norm_nonneg z)
      _ = 2 * (D : ℝ) * ‖z‖ := by ring
  have hfactor :
      ‖lemma57UndampedMellinFactor χ s‖ ≤ 16 * (D : ℝ) * ‖z‖ ^ 2 := by
    rw [lemma57UndampedMellinFactor, norm_div, norm_mul]
    calc
      ‖riemannZeta (1 + s)‖ * ‖dirichletLFunction χ (1 + s)‖ / ‖s‖ ≤
          (4 * ‖z‖) * (2 * (D : ℝ) * ‖z‖) / ‖s‖ := by
        apply div_le_div_of_nonneg_right _ hsNormPos.le
        exact mul_le_mul hζ hL (norm_nonneg _) (by positivity)
      _ ≤ 16 * (D : ℝ) * ‖z‖ ^ 2 := by
        apply (div_le_iff₀ hsNormPos).2
        have hcoef : 0 ≤ 8 * (D : ℝ) * ‖z‖ ^ 2 := by positivity
        have hsbound : 0 ≤ 2 * ‖s‖ - 1 := by nlinarith [hsnormS]
        nlinarith [mul_nonneg hcoef hsbound]
  have hzreEq : z.re = 1 + σ := by simp [z, s]
  have hzimEq : z.im = t := by simp [z, s]
  have hrealAbs : |z.re| ≤ (3 : ℝ) / 2 :=
    abs_le.mpr ⟨by rw [hzreEq]; linarith [hσlo], by rw [hzreEq]; linarith [hσhi]⟩
  have himAbs : |z.im| = |t| := by rw [hzimEq]
  have hmax : max |z.re| |z.im| ≤ (3 : ℝ) / 2 + |t| := by
    apply max_le
    · linarith [hrealAbs, abs_nonneg (z.im)]
    · rw [himAbs]
      linarith [hrealAbs, abs_nonneg t]
  have hsqrt2 : Real.sqrt 2 ≤ 2 := by
    have hsqrt := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    nlinarith [Real.sqrt_nonneg 2]
  have hznorm : ‖z‖ ≤ 3 + 2 * |t| := by
    calc
      ‖z‖ ≤ Real.sqrt 2 * max |z.re| |z.im| := norm_le_sqrt_two_mul_max z
      _ ≤ 2 * max |z.re| |z.im| :=
        mul_le_mul_of_nonneg_right hsqrt2
          (le_trans (abs_nonneg (z.re)) (le_max_left _ _))
      _ ≤ 2 * ((3 : ℝ) / 2 + |t|) := mul_le_mul_of_nonneg_left hmax (by norm_num)
      _ = 3 + 2 * |t| := by ring
  have hnormSq : ‖z‖ ^ 2 ≤ (3 + 2 * |t|) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg z) (by positivity)).2 hznorm
  have hpoly : (3 + 2 * |t|) ^ 2 ≤ 18 * (1 + t ^ 2) := by
    have hx : 0 ≤ |t| := abs_nonneg t
    nlinarith [sq_nonneg (3 - 2 * |t|), sq_abs t]
  calc
    ‖lemma57UndampedMellinFactor χ s‖ ≤ 16 * (D : ℝ) * ‖z‖ ^ 2 := hfactor
    _ ≤ 16 * (D : ℝ) * (3 + 2 * |t|) ^ 2 :=
      mul_le_mul_of_nonneg_left hnormSq (by positivity)
    _ ≤ 288 * (D : ℝ) * (1 + t ^ 2) := by nlinarith [mul_le_mul_of_nonneg_left hpoly (by positivity : 0 ≤ 16 * (D : ℝ))]

/-- The Abel--Mellin formulas give polynomial growth for both factors in the
critical half-strip.  The norm cutoff removes the pole of `ζ(1+s)`, and the
polynomial is absorbed by `exp (2 |t|)`. -/
theorem lemma57CriticalStripExponentialGrowth_proved
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    Lemma57CriticalStripExponentialGrowth χ := by
  have hDreal : (0 : ℝ) < D := by exact_mod_cast Nat.zero_lt_of_lt hD
  refine ⟨144 * (D : ℝ), 2, by positivity, by norm_num, ?_⟩
  intro σ t hσlo hσhi hsnorm
  let s : ℂ := (σ : ℂ) + (t : ℂ) * I
  let z : ℂ := 1 + s
  have hsnormS : (1 : ℝ) / 2 ≤ ‖s‖ := by simpa [s] using hsnorm
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hsnormS
    norm_num at hsnormS
  have hsNormPos : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  have hzre : (1 : ℝ) / 2 ≤ z.re := by
    norm_num [z, s]
    linarith
  have hzpos : 0 < z.re := lt_of_lt_of_le (by norm_num) hzre
  have hz1 : z ≠ 1 := by
    intro h
    have hs_eq_zero : s = 0 := by
      have hh : 1 + s = 1 + 0 := by simpa [z] using h
      exact add_left_cancel hh
    exact hs0 hs_eq_zero
  have hζformula := riemannZeta_eq_fractionalPart_formula_of_pos_re hzpos hz1
  have hM := norm_mellin_zetaFractionalPart_le hzpos
  have hM2 : ‖mellin zetaFractionalPart (-z)‖ ≤ 2 := by
    calc
      ‖mellin zetaFractionalPart (-z)‖ ≤ (1 : ℝ) / z.re := hM
      _ ≤ 2 := by
        apply (div_le_iff₀ hzpos).2
        nlinarith [hzre]
  have hnorm_sub : ‖z - 1‖ = ‖s‖ := by simp [z]
  have hdiv : ‖z‖ / ‖z - 1‖ ≤ 2 * ‖z‖ := by
    rw [hnorm_sub]
    apply (div_le_iff₀ hsNormPos).2
    have hmul := mul_le_mul_of_nonneg_left hsnormS (norm_nonneg z)
    nlinarith
  have hζ : ‖riemannZeta z‖ ≤ 4 * ‖z‖ := by
    rw [hζformula]
    calc
      ‖z / (z - 1) - z * mellin zetaFractionalPart (-z)‖ ≤
          ‖z / (z - 1)‖ + ‖z * mellin zetaFractionalPart (-z)‖ := norm_sub_le _ _
      _ = ‖z‖ / ‖z - 1‖ + ‖z‖ * ‖mellin zetaFractionalPart (-z)‖ := by
        simp [norm_div]
      _ ≤ 2 * ‖z‖ + ‖z‖ * 2 :=
        add_le_add hdiv (mul_le_mul_of_nonneg_left hM2 (norm_nonneg z))
      _ = 4 * ‖z‖ := by ring
  have hzL := χ.norm_dirichletLFunction_le_of_pos_re hD hzpos
  have hDnonneg : 0 ≤ (D : ℝ) := Nat.cast_nonneg D
  have hLcoef : (D : ℝ) / z.re ≤ 2 * (D : ℝ) := by
    apply (div_le_iff₀ hzpos).2
    nlinarith [hzre, hDnonneg]
  have hL : ‖dirichletLFunction χ z‖ ≤ 2 * (D : ℝ) * ‖z‖ := by
    calc
      ‖dirichletLFunction χ z‖ ≤ ‖z‖ * ((D : ℝ) / z.re) := hzL
      _ ≤ ‖z‖ * (2 * (D : ℝ)) :=
        mul_le_mul_of_nonneg_left hLcoef (norm_nonneg z)
      _ = 2 * (D : ℝ) * ‖z‖ := by ring
  have hpolynomial :
      ‖lemma57UndampedMellinFactor χ s‖ ≤
        16 * (D : ℝ) * ‖z‖ ^ 2 := by
    rw [lemma57UndampedMellinFactor, norm_div, norm_mul]
    calc
      ‖riemannZeta (1 + s)‖ * ‖dirichletLFunction χ (1 + s)‖ / ‖s‖ ≤
          (4 * ‖z‖) * (2 * (D : ℝ) * ‖z‖) / ‖s‖ := by
        apply div_le_div_of_nonneg_right _ hsNormPos.le
        exact mul_le_mul hζ hL (norm_nonneg _) (by positivity)
      _ ≤ 16 * (D : ℝ) * ‖z‖ ^ 2 := by
        apply (div_le_iff₀ hsNormPos).2
        have hcoef : 0 ≤ 8 * (D : ℝ) * ‖z‖ ^ 2 := by positivity
        have hsbound : 0 ≤ 2 * ‖s‖ - 1 := by nlinarith [hsnormS]
        nlinarith [mul_nonneg hcoef hsbound]
  have hzreEq : z.re = 1 + σ := by simp [z, s]
  have hzimEq : z.im = t := by simp [z, s]
  have hzreLo : (1 : ℝ) / 2 ≤ z.re := by rw [hzreEq]; linarith
  have hzreHi : z.re ≤ (3 : ℝ) / 2 := by rw [hzreEq]; linarith
  have hrealAbs : |z.re| ≤ (3 : ℝ) / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have himAbs : |z.im| = |t| := by rw [hzimEq]
  have hmax : max |z.re| |z.im| ≤ (3 : ℝ) / 2 + |t| := by
    apply max_le
    · linarith [hrealAbs, abs_nonneg (z.im)]
    · rw [himAbs]
      linarith [hrealAbs, abs_nonneg t]
  have hsqrt2 : Real.sqrt 2 ≤ 2 := by
    have hsqrt := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    nlinarith [Real.sqrt_nonneg 2]
  have hznorm : ‖z‖ ≤ 3 + 2 * |t| := by
    calc
      ‖z‖ ≤ Real.sqrt 2 * max |z.re| |z.im| := norm_le_sqrt_two_mul_max z
      _ ≤ 2 * max |z.re| |z.im| :=
        mul_le_mul_of_nonneg_right hsqrt2 (le_trans (abs_nonneg (z.re)) (le_max_left _ _))
      _ ≤ 2 * ((3 : ℝ) / 2 + |t|) := mul_le_mul_of_nonneg_left hmax (by norm_num)
      _ = 3 + 2 * |t| := by ring
  let x : ℝ := |t|
  have hx : 0 ≤ x := abs_nonneg t
  have hlinear : 3 + 2 * x ≤ 3 * (1 + x) := by dsimp [x]; nlinarith [abs_nonneg t]
  have hexp : 1 + x ≤ Real.exp x := by simpa [add_comm] using Real.add_one_le_exp x
  have hsquare : (1 + x) ^ 2 ≤ Real.exp (2 * x) := by
    rw [show (2 : ℝ) * x = x + x by ring, Real.exp_add]
    have hleft : 0 ≤ Real.exp x - (1 + x) := by linarith [hexp]
    have hright : 0 ≤ Real.exp x + (1 + x) := by positivity
    nlinarith [mul_nonneg hleft hright]
  have hpolyExp : (3 + 2 * x) ^ 2 ≤ (9 : ℝ) * Real.exp (2 * x) := by
    calc
      (3 + 2 * x) ^ 2 ≤ (3 * (1 + x)) ^ 2 := by nlinarith [hlinear]
      _ = 9 * (1 + x) ^ 2 := by ring
      _ ≤ 9 * Real.exp (2 * x) := by nlinarith [hsquare]
  calc
    ‖lemma57UndampedMellinFactor χ s‖ ≤ 16 * (D : ℝ) * ‖z‖ ^ 2 := hpolynomial
    _ ≤ 16 * (D : ℝ) * (3 + 2 * x) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hznorm' : ‖z‖ ≤ 3 + 2 * x := by simpa [x] using hznorm
      exact (sq_le_sq₀ (norm_nonneg z) (by positivity)).2 hznorm'
    _ ≤ 144 * (D : ℝ) * Real.exp (2 * |t|) := by
      dsimp [x]
      have := mul_le_mul_of_nonneg_left hpolyExp (by positivity : 0 ≤ 16 * (D : ℝ))
      nlinarith

/-- Absolute convergence supplies the right half of the strip, so critical
half-strip growth implies Step 40's full-strip growth interface. -/
theorem lemma57StripExponentialGrowth_of_critical
    {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hcritical : Lemma57CriticalStripExponentialGrowth χ) :
    Lemma57StripExponentialGrowth χ := by
  rcases hcritical with ⟨C, A, hC, hA, hcritical⟩
  let R : ℝ := 2 * (lemma57ZetaRightHalfBound *
    lemma57DirichletLRightHalfBound χ)
  refine ⟨max C R, A, le_trans hC (le_max_left _ _), hA, ?_⟩
  intro σ t hσ0 hσ1 hnorm
  rcases le_total σ ((1 : ℝ) / 2) with hleft | hright
  · exact (hcritical σ t hσ0 hleft hnorm).trans
      (mul_le_mul_of_nonneg_right (le_max_left C R) (Real.exp_pos _).le)
  · have hR := lemma57UndampedMellinFactor_norm_le_rightHalf
      χ hright hnorm
    calc
      ‖lemma57UndampedMellinFactor χ ((σ : ℂ) + (t : ℂ) * I)‖ ≤ R := hR
      _ ≤ max C R * Real.exp (A * |t|) := by
        have hmax : R ≤ max C R := le_max_right _ _
        have hexp : 1 ≤ Real.exp (A * |t|) := by
          rw [Real.one_le_exp_iff]
          positivity
        calc
          R ≤ max C R := hmax
          _ = max C R * 1 := (mul_one _).symm
          _ ≤ max C R * Real.exp (A * |t|) :=
            mul_le_mul_of_nonneg_left hexp
              (le_trans hC (le_max_left C R))

/-- The exact contour shift is now reduced to growth only on the true critical
half-strip; the right half is discharged by the convergent Dirichlet series. -/
theorem lemma57ContourShiftIdentity_of_criticalStripExponentialGrowth
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hcritical : Lemma57CriticalStripExponentialGrowth χ) :
    Lemma57ContourShiftIdentity χ :=
  lemma57ContourShiftIdentity_of_stripExponentialGrowth χ hD
    (lemma57StripExponentialGrowth_of_critical χ hcritical)

/-- The contour shift required by Lemma 5.7 now follows unconditionally from
the Abel--Mellin bounds for ζ and the primitive character L-function. -/
theorem lemma57ContourShiftIdentity_proved
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    Lemma57ContourShiftIdentity χ :=
  lemma57ContourShiftIdentity_of_criticalStripExponentialGrowth χ hD
    (lemma57CriticalStripExponentialGrowth_proved χ hD)

end ZhangLS.Spec
