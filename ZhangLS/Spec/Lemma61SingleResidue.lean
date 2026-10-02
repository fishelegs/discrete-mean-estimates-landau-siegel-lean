import ZhangLS.Spec.Lemma61GaussianCutoff
import ZhangLS.Spec.Lemma44ProductResidue

/-! # Actual finite single L contour inputs for Lemma 6.1

The original family and actual L, K, P4, Gaussian weights and strict region
are retained. The genuine residue is expanded into four oriented edges.
The actual finite right integral differs from K by at most
9 times inverse-square mass exp(-L^10/8), uniformly for L>=64.
The full Lemma61Target remains unproved: left dual integrals, reciprocal
tail truncation and horizontal edge budgets are still required.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Set MeasureTheory
open scoped Real Topology
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

noncomputable def lemma61SingleMellinNumerator {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (s : ℂ) (B : ℝ) (w : ℂ) : ℂ :=
  DirichletCharacter.LFunction ψ (s + w) *
    exp (w * (Real.log B : ℂ)) * lemma57OmegaOne D w

lemma lemma61_family_nonprincipal {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : Lemma23InPsi (D := D) ψ) : ψ ≠ 1 := by
  intro he
  have hc : ψ.conductor = p := hψ.2.1
  rw [he,DirichletCharacter.conductor_one] at hc
  exact hψ.1.ne_one hc.symm

lemma lemma61_single_mellin_numerator_entire {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : Lemma23InPsi (D := D) ψ)
    (s : ℂ) (B : ℝ) : Differentiable ℂ (lemma61SingleMellinNumerator (D := D) ψ s B) := by
  have hfirst := DirichletCharacter.differentiable_LFunction (lemma61_family_nonprincipal ψ hψ)
  unfold lemma61SingleMellinNumerator lemma57OmegaOne
  fun_prop

lemma lemma61_single_mellin_rectangle_residue {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : Lemma23InPsi (D := D) ψ)
    (s : ℂ) (B : ℝ) {H : ℝ} (hH : 0 < H) :
    lemma57RectangleBoundaryIntegral (fun w : ℂ => lemma61SingleMellinNumerator (D := D) ψ s B w / w) H =
      2 * (Real.pi : ℂ) * I * DirichletCharacter.LFunction ψ s := by
  simpa [lemma61SingleMellinNumerator,lemma57OmegaOne] using
    lemma44_simple_pole_rectangle (lemma61SingleMellinNumerator (D := D) ψ s B)
      (lemma61_single_mellin_numerator_entire ψ hψ s B) hH

lemma lemma61_actual_single_functional_equation {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : Lemma23InPsi (D := D) ψ)
    {z : ℂ} (him : 0 < z.im) :
    DirichletCharacter.LFunction ψ z = lemma23DirichletZ ψ z *
      DirichletCharacter.LFunction ψ⁻¹ (1 - z) := by
  exact lemma23_dirichletLFunction_functional_equation ψ hψ.2.1 hψ.1.ne_one
    (lemma23_gammaFactor_ne_zero_of_im_ne_zero ψ him.ne')
    (lemma23_gammaFactor_ne_zero_of_im_ne_zero ψ⁻¹ (by simpa using neg_ne_zero.mpr him.ne'))

noncomputable def lemma61RectangleBoundaryIntegral (f : ℂ → ℂ) (H : ℝ) : ℂ :=
  (∫ x : ℝ in (-(1 : ℝ))..2, f ((x : ℂ) - (H : ℂ) * I)) -
  (∫ x : ℝ in (-(1 : ℝ))..2, f ((x : ℂ) + (H : ℂ) * I)) +
  I * (∫ y : ℝ in -H..H, f (2 + (y : ℂ) * I)) -
  I * (∫ y : ℝ in -H..H, f (-1 + (y : ℂ) * I))

lemma lemma61_interval_integral_double (f : ℝ → ℂ) (a b : ℝ) :
    (∫ x in a..b, (2 : ℂ) * f (2 * x)) = ∫ x in 2 * a..2 * b, f x := by
  rw [intervalIntegral.integral_const_mul]
  simpa only [Complex.real_smul] using
    intervalIntegral.smul_integral_comp_mul_left (f := f) (a := a) (b := b) (2 : ℝ)

lemma lemma61_rectangle_scale_identity (f : ℂ → ℂ) (H : ℝ) :
    lemma57RectangleBoundaryIntegral (fun w => 2 * f (2 * w)) (H / 2) =
      lemma61RectangleBoundaryIntegral f H := by
  have hb : (∫ x in (-(1 : ℝ) / 2)..1,
      (2 : ℂ) * f (2 * ((x : ℂ) - ((H / 2 : ℝ) : ℂ) * I))) =
        ∫ x in (-(1 : ℝ))..2, f ((x : ℂ) - (H : ℂ) * I) := by
    calc
      _ = ∫ x in (-(1 : ℝ) / 2)..1, (2 : ℂ) * f (((2 * x : ℝ) : ℂ) - (H : ℂ) * I) := by
        apply intervalIntegral.integral_congr
        intro x hx
        congr 1
        congr 1
        push_cast
        ring
      _ = _ := by
        simpa only [show (2 : ℝ) * (-1 / 2) = -1 by norm_num,
          show (2 : ℝ) * 1 = 2 by norm_num] using (lemma61_interval_integral_double
          (fun x : ℝ => f ((x : ℂ) - (H : ℂ) * I)) (-(1 : ℝ) / 2) 1)
  have ht : (∫ x in (-(1 : ℝ) / 2)..1,
      (2 : ℂ) * f (2 * ((x : ℂ) + ((H / 2 : ℝ) : ℂ) * I))) =
        ∫ x in (-(1 : ℝ))..2, f ((x : ℂ) + (H : ℂ) * I) := by
    calc
      _ = ∫ x in (-(1 : ℝ) / 2)..1, (2 : ℂ) * f (((2 * x : ℝ) : ℂ) + (H : ℂ) * I) := by
        apply intervalIntegral.integral_congr
        intro x hx
        congr 1
        congr 1
        push_cast
        ring
      _ = _ := by
        simpa only [show (2 : ℝ) * (-1 / 2) = -1 by norm_num,
          show (2 : ℝ) * 1 = 2 by norm_num] using (lemma61_interval_integral_double
          (fun x : ℝ => f ((x : ℂ) + (H : ℂ) * I)) (-(1 : ℝ) / 2) 1)
  have hr : (∫ y in (-(H / 2))..(H / 2),
      (2 : ℂ) * f (2 * (1 + (y : ℂ) * I))) =
        ∫ y in (-H)..H, f (2 + (y : ℂ) * I) := by
    calc
      _ = ∫ y in (-(H / 2))..(H / 2), (2 : ℂ) * f (2 + ((2 * y : ℝ) : ℂ) * I) := by
        apply intervalIntegral.integral_congr
        intro y hy
        congr 1
        congr 1
        push_cast
        ring
      _ = _ := by
        simpa only [show (2 : ℝ) * (-(H / 2)) = -H by ring,
          show (2 : ℝ) * (H / 2) = H by ring] using (lemma61_interval_integral_double
          (fun y : ℝ => f (2 + (y : ℂ) * I)) (-(H / 2)) (H / 2))
  have hl : (∫ y in (-(H / 2))..(H / 2),
      (2 : ℂ) * f (2 * (-(1 : ℂ) / 2 + (y : ℂ) * I))) =
        ∫ y in (-H)..H, f (-1 + (y : ℂ) * I) := by
    calc
      _ = ∫ y in (-(H / 2))..(H / 2), (2 : ℂ) * f (-1 + ((2 * y : ℝ) : ℂ) * I) := by
        apply intervalIntegral.integral_congr
        intro y hy
        congr 1
        congr 1
        push_cast
        ring
      _ = _ := by
        simpa only [show (2 : ℝ) * (-(H / 2)) = -H by ring,
          show (2 : ℝ) * (H / 2) = H by ring] using (lemma61_interval_integral_double
          (fun y : ℝ => f (-1 + (y : ℂ) * I)) (-(H / 2)) (H / 2))
  unfold lemma57RectangleBoundaryIntegral lemma61RectangleBoundaryIntegral
  simp only [Complex.ofReal_one]
  rw [hb,ht,hr,hl]

lemma lemma61_simple_pole_wide_rectangle (N : ℂ → ℂ) (hN : Differentiable ℂ N)
    {H : ℝ} (hH : 0 < H) :
    lemma61RectangleBoundaryIntegral (fun w => N w / w) H = 2 * (Real.pi : ℂ) * I * N 0 := by
  have hM : Differentiable ℂ (fun w : ℂ => N (2 * w)) := by fun_prop
  have hb := lemma44_simple_pole_rectangle (fun w : ℂ => N (2 * w)) hM
    (T := H / 2) (by linarith)
  have he : (fun w : ℂ => N (2 * w) / w) = (fun w : ℂ => 2 * (N (2 * w) / (2 * w))) := by
    funext w
    by_cases hw : w = 0
    · simp [hw]
    · field_simp [hw]
  rw [he] at hb
  rw [← lemma61_rectangle_scale_identity (fun w => N w / w) H]
  simpa using hb

lemma lemma61_actual_wide_rectangle_residue {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : Lemma23InPsi (D := D) ψ)
    (s : ℂ) (B : ℝ) {H : ℝ} (hH : 0 < H) :
    lemma61RectangleBoundaryIntegral
      (fun w : ℂ => lemma61SingleMellinNumerator (D := D) ψ s B w / w) H =
        2 * (Real.pi : ℂ) * I * DirichletCharacter.LFunction ψ s := by
  simpa [lemma61SingleMellinNumerator,lemma57OmegaOne] using
    lemma61_simple_pole_wide_rectangle (lemma61SingleMellinNumerator (D := D) ψ s B)
      (lemma61_single_mellin_numerator_entire ψ hψ s B) hH

lemma lemma61_actual_rectangle_identity {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : Lemma23InPsi (D := D) ψ)
    (s : ℂ) (B : ℝ) {H : ℝ} (hH : 0 < H) :
    DirichletCharacter.LFunction ψ s =
      (2 * (Real.pi : ℂ) * I)⁻¹ *
        ((∫ x : ℝ in (-1 : ℝ)..2,
          lemma61SingleMellinNumerator (D := D) ψ s B ((x : ℂ) - (H : ℂ) * I) /
            ((x : ℂ) - (H : ℂ) * I)) -
        (∫ x : ℝ in (-1 : ℝ)..2,
          lemma61SingleMellinNumerator (D := D) ψ s B ((x : ℂ) + (H : ℂ) * I) /
            ((x : ℂ) + (H : ℂ) * I)) +
        I * (∫ y : ℝ in -H..H, lemma61RightMellinIntegrand (D := D) ψ s B 2 y) -
        I * (∫ y : ℝ in -H..H, lemma61RightMellinIntegrand (D := D) ψ s B (-1) y)) := by
  have h := lemma61_actual_wide_rectangle_residue ψ hψ s B hH
  have hc : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  calc
    _ = (2 * (Real.pi : ℂ) * I)⁻¹ * lemma61RectangleBoundaryIntegral
        (fun w : ℂ => lemma61SingleMellinNumerator (D := D) ψ s B w / w) H := by
      rw [h, inv_mul_cancel_left₀ hc]
    _ = _ := by
      unfold lemma61RectangleBoundaryIntegral lemma61SingleMellinNumerator lemma61RightMellinIntegrand
      norm_num

end ZhangLS.Spec
