import ZhangLS.Spec.Lemma57ContourAnalyticity
import ZhangLS.Spec.Lemma57ContourShiftLimit
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The oriented rectangle and its winding around zero

This module fixes the boundary functional for the finite rectangle with real
sides `-1/2` and `1` and imaginary heights `-T` and `T`.  It computes the
boundary integral of `s⁻¹` directly as `2πi`, including the sign of every edge,
and proves that the finite shift proposition from Step 36 is exactly the
corresponding unnormalized rectangle residue identity.

The computation uses real rational integrals and the arctangent reciprocal
identity, so it does not hide a choice of complex logarithm branch.
-/

namespace ZhangLS.Spec

open Complex MeasureTheory Set
open scoped Real Topology

/-- Positively oriented boundary integral of `f` around the rectangle
`[-1/2,1] × [-T,T]`. -/
noncomputable def lemma57RectangleBoundaryIntegral
    (f : ℂ → ℂ) (T : ℝ) : ℂ :=
  (∫ x : ℝ in (-(1 : ℝ) / 2)..1, f ((x : ℂ) - (T : ℂ) * I)) -
  (∫ x : ℝ in (-(1 : ℝ) / 2)..1, f ((x : ℂ) + (T : ℂ) * I)) +
  I * (∫ y : ℝ in -T..T, f (1 + (y : ℂ) * I)) -
  I * (∫ y : ℝ in -T..T,
    f (-(1 : ℝ) / 2 + (y : ℂ) * I))

private theorem horizontal_inv_point (T : ℝ) (hT : 0 < T) (x : ℝ) :
    ((x : ℂ) - (T : ℂ) * I)⁻¹ - ((x : ℂ) + (T : ℂ) * I)⁻¹ =
      (2 * (T : ℂ) * I) * (((T ^ 2 + x ^ 2)⁻¹ : ℝ) : ℂ) := by
  have hm : (x : ℂ) - (T : ℂ) * I ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi
    linarith
  have hp : (x : ℂ) + (T : ℂ) * I ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi
    linarith
  have hd : T ^ 2 + x ^ 2 ≠ 0 := by positivity
  have hdC : (x : ℂ) ^ 2 + (T : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast
      (add_pos_of_nonneg_of_pos (sq_nonneg x) (sq_pos_of_pos hT)).ne'
  push_cast
  field_simp [hdC]
  ring_nf
  field_simp [hdC]
  rw [I_sq]
  ring

private theorem horizontal_inv_difference (T : ℝ) (hT : 0 < T) :
    (∫ x : ℝ in (-(1 : ℝ) / 2)..1,
        ((x : ℂ) - (T : ℂ) * I)⁻¹) -
      (∫ x : ℝ in (-(1 : ℝ) / 2)..1,
        ((x : ℂ) + (T : ℂ) * I)⁻¹) =
      (2 * I : ℂ) *
        ((Real.arctan (1 / T) + Real.arctan (1 / (2 * T)) : ℝ) : ℂ) := by
  have hminus : IntervalIntegrable
      (fun x : ℝ => ((x : ℂ) - (T : ℂ) * I)⁻¹) volume
      (-(1 : ℝ) / 2) 1 := by
    apply Continuous.intervalIntegrable
    apply Continuous.inv₀
    · fun_prop
    · intro x hx
      have hi := congrArg Complex.im hx
      norm_num at hi
      linarith
  have hplus : IntervalIntegrable
      (fun x : ℝ => ((x : ℂ) + (T : ℂ) * I)⁻¹) volume
      (-(1 : ℝ) / 2) 1 := by
    apply Continuous.intervalIntegrable
    apply Continuous.inv₀
    · fun_prop
    · intro x hx
      have hi := congrArg Complex.im hx
      norm_num at hi
      linarith
  rw [← intervalIntegral.integral_sub hminus hplus]
  calc
    (∫ x : ℝ in (-(1 : ℝ) / 2)..1,
        (((x : ℂ) - (T : ℂ) * I)⁻¹ -
          ((x : ℂ) + (T : ℂ) * I)⁻¹)) =
        ∫ x : ℝ in (-(1 : ℝ) / 2)..1,
          (2 * (T : ℂ) * I) * (((T ^ 2 + x ^ 2)⁻¹ : ℝ) : ℂ) := by
      apply intervalIntegral.integral_congr
      intro x _
      exact horizontal_inv_point T hT x
    _ = (2 * (T : ℂ) * I) *
        ((∫ x : ℝ in (-(1 : ℝ) / 2)..1,
          (T ^ 2 + x ^ 2)⁻¹ : ℝ) : ℂ) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_ofReal]
    _ = _ := by
      rw [integral_inv_sq_add_sq hT.ne']
      have harg : -(1 : ℝ) / 2 / T = -(1 / (2 * T)) := by
        field_simp
      rw [harg, Real.arctan_neg]
      push_cast
      field_simp [hT.ne']
      ring

private theorem odd_rational_integral (c T : ℝ) :
    (∫ y : ℝ in -T..T, y / (c ^ 2 + y ^ 2)) = 0 := by
  let q : ℝ → ℝ := fun y => y / (c ^ 2 + y ^ 2)
  have hcomp := intervalIntegral.integral_comp_neg (f := q)
    (a := -T) (b := T)
  have hsame : (∫ y : ℝ in -T..T, q (-y)) =
      ∫ y : ℝ in -T..T, q y := by
    simp only [neg_neg] at hcomp
    exact hcomp
  have hneg : (∫ y : ℝ in -T..T, q (-y)) =
      -(∫ y : ℝ in -T..T, q y) := by
    calc
      (∫ y : ℝ in -T..T, q (-y)) =
          ∫ y : ℝ in -T..T, -q y := by
        apply intervalIntegral.integral_congr
        intro y _
        dsimp [q]
        ring
      _ = -(∫ y : ℝ in -T..T, q y) := by
        rw [intervalIntegral.integral_neg]
  change (∫ y : ℝ in -T..T, q y) = 0
  linarith

private theorem vertical_inv_point (c y : ℝ) (hc : c ≠ 0) :
    I * ((c : ℂ) + (y : ℂ) * I)⁻¹ =
      ((y / (c ^ 2 + y ^ 2) : ℝ) : ℂ) +
        ((c / (c ^ 2 + y ^ 2) : ℝ) : ℂ) * I := by
  have hz : (c : ℂ) + (y : ℂ) * I ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num at hr
    exact hc hr
  have hd : c ^ 2 + y ^ 2 ≠ 0 := by positivity
  have hdC : (c : ℂ) ^ 2 + (y : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast
      (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hc) (sq_nonneg y)).ne'
  push_cast
  field_simp [hz, hdC]
  have hz' : (c : ℂ) + I * (y : ℂ) ≠ 0 := by
    simpa [mul_comm] using hz
  apply (div_eq_iff hz').2
  ring_nf
  rw [I_sq]
  ring

private theorem vertical_inv_integral (c T : ℝ) (hc : c ≠ 0) :
    I * (∫ y : ℝ in -T..T, ((c : ℂ) + (y : ℂ) * I)⁻¹) =
      (2 * I : ℂ) * (Real.arctan (T / c) : ℂ) := by
  rw [← intervalIntegral.integral_const_mul]
  calc
    (∫ y : ℝ in -T..T, I * ((c : ℂ) + (y : ℂ) * I)⁻¹) =
        ∫ y : ℝ in -T..T,
          ((y / (c ^ 2 + y ^ 2) : ℝ) : ℂ) +
            ((c / (c ^ 2 + y ^ 2) : ℝ) : ℂ) * I := by
      apply intervalIntegral.integral_congr
      intro y _
      exact vertical_inv_point c y hc
    _ = ((∫ y : ℝ in -T..T, y / (c ^ 2 + y ^ 2) : ℝ) : ℂ) +
        ((∫ y : ℝ in -T..T, c / (c ^ 2 + y ^ 2) : ℝ) : ℂ) * I := by
      rw [intervalIntegral.integral_add]
      · rw [intervalIntegral.integral_ofReal,
          intervalIntegral.integral_mul_const,
          intervalIntegral.integral_ofReal]
      · apply Continuous.intervalIntegrable
        apply Complex.continuous_ofReal.comp
        apply Continuous.div₀
        · fun_prop
        · fun_prop
        · intro y
          positivity
      · apply Continuous.intervalIntegrable
        apply Continuous.mul
        · apply Complex.continuous_ofReal.comp
          apply Continuous.div₀
          · fun_prop
          · fun_prop
          · intro y
            positivity
        · fun_prop
    _ = _ := by
      rw [odd_rational_integral, integral_div_sq_add_sq]
      have harg : -T / c = -(T / c) := by ring
      rw [harg, Real.arctan_neg]
      push_cast
      ring

/-- The positive rectangle winds once around zero: its boundary integral of
`s⁻¹` is exactly `2πi`. -/
theorem lemma57RectangleBoundaryIntegral_inv
    (T : ℝ) (hT : 0 < T) :
    lemma57RectangleBoundaryIntegral (fun s : ℂ => s⁻¹) T =
      2 * (Real.pi : ℂ) * I := by
  unfold lemma57RectangleBoundaryIntegral
  rw [horizontal_inv_difference T hT]
  simp only
  have hright :
      I * (∫ y : ℝ in -T..T, (1 + (y : ℂ) * I)⁻¹) =
        (2 * I : ℂ) * (Real.arctan (T / 1) : ℂ) := by
    simpa using vertical_inv_integral 1 T one_ne_zero
  have hcast : -((1 : ℝ) : ℂ) / 2 =
      ((-(1 : ℝ) / 2 : ℝ) : ℂ) := by
    norm_num
  rw [hright, hcast,
    vertical_inv_integral (-(1 : ℝ) / 2) T (by norm_num)]
  have hnegarg : T / (-(1 : ℝ) / 2) = -(2 * T) := by ring
  rw [hnegarg, Real.arctan_neg]
  have hinvT : 1 / T = T⁻¹ := by ring
  have hinv2T : 1 / (2 * T) = (2 * T)⁻¹ := by ring
  rw [hinvT, hinv2T, Real.arctan_inv_of_pos hT,
    Real.arctan_inv_of_pos (by positivity : 0 < 2 * T)]
  push_cast
  ring_nf

private theorem finite_shift_at_iff_boundary
    {D : ℕ} (χ : RealPrimitiveCharacter D) (T : ℝ) :
    (lemma57TruncatedVerticalIntegral χ 1 T =
      lemma57ResidueValue χ +
        lemma57TruncatedVerticalIntegral χ (-(1 : ℝ) / 2) T +
          lemma57HorizontalIntegralError χ T) ↔
      lemma57RectangleBoundaryIntegral (lemma57MellinIntegrand χ) T =
        2 * (Real.pi : ℂ) * I * lemma57ResidueValue χ := by
  unfold lemma57TruncatedVerticalIntegral lemma57HorizontalIntegralError
    lemma57RectangleBoundaryIntegral
  simp_rw [intervalIntegral.integral_mul_const]
  have hC : 2 * (Real.pi : ℂ) * I ≠ 0 := two_pi_I_ne_zero
  constructor
  · intro h
    field_simp [hC] at h
    simp only [mul_comm I, ofReal_neg, ofReal_one, ofReal_div,
      ofReal_ofNat] at h ⊢
    ring_nf at h ⊢
    simp only [mul_comm, add_comm, sub_eq_add_neg] at h ⊢
    linear_combination h
  · intro h
    field_simp [hC]
    simp only [mul_comm I, ofReal_neg, ofReal_one, ofReal_div,
      ofReal_ofNat] at h ⊢
    ring_nf at h ⊢
    simp only [mul_comm, add_comm, sub_eq_add_neg] at h ⊢
    linear_combination h

/-- The normalized finite-shift formulation from Step 36 is equivalent to the
standard unnormalized residue identity on the positively oriented rectangle. -/
theorem lemma57FiniteRectangleShift_iff_boundaryIntegral
    {D : ℕ} (χ : RealPrimitiveCharacter D) :
    Lemma57FiniteRectangleShift χ ↔
      ∀ T : ℝ, 0 < T →
        lemma57RectangleBoundaryIntegral (lemma57MellinIntegrand χ) T =
          2 * (Real.pi : ℂ) * I * lemma57ResidueValue χ := by
  constructor <;> intro h T hT
  · exact (finite_shift_at_iff_boundary χ T).mp (h T hT)
  · exact (finite_shift_at_iff_boundary χ T).mpr (h T hT)

end ZhangLS.Spec
