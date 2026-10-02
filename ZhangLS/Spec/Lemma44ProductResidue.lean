import ZhangLS.Spec.Lemma44ProductMellin
import ZhangLS.Spec.Lemma57PrincipalPart

/-!
# The actual simple residue in Lemma 4.4

Removing the pole by `dslope` makes the regular part entire. Rectangular
Cauchy--Goursat then gives the exact residue of the product Gaussian Mellin
integrand, with the edge orientations inherited from the verified rectangle.
-/

namespace ZhangLS.Spec

open Complex MeasureTheory

set_option maxHeartbeats 1000000

/-- A simple-pole residue theorem in the verified rectangle convention. -/
theorem lemma44_simple_pole_rectangle (N : ℂ → ℂ) (hN : Differentiable ℂ N)
    {T : ℝ} (hT : 0 < T) :
    lemma57RectangleBoundaryIntegral (fun w => N w / w) T =
      2 * (Real.pi : ℂ) * I * N 0 := by
  let R := dslope N 0
  have hR : Differentiable ℂ R := by
    rw [← differentiableOn_univ]
    exact (Complex.differentiableOn_dslope (s := Set.univ) (c := (0 : ℂ))
      (by simp)).2 hN.differentiableOn
  have heq (w : ℂ) (hw : w ≠ 0) : N w / w = N 0 * w⁻¹ + R w := by
    dsimp [R]
    rw [dslope_of_ne _ hw, slope_def_field]
    simp only [sub_zero]
    field_simp
    ring
  have hsplit (γ : ℝ → ℂ) (hγ : Continuous γ) (hγne : ∀ t, γ t ≠ 0) (a b : ℝ) :
      (∫ t : ℝ in a..b, N (γ t) / γ t) =
        N 0 * (∫ t : ℝ in a..b, (γ t)⁻¹) + (∫ t : ℝ in a..b, R (γ t)) := by
    have hq : IntervalIntegrable (fun t => N 0 * (γ t)⁻¹) volume a b :=
      ((hγ.inv₀ hγne).const_mul (N 0)).intervalIntegrable a b
    have hr : IntervalIntegrable (fun t => R (γ t)) volume a b :=
      (hR.continuous.comp hγ).intervalIntegrable a b
    calc
      _ = ∫ t : ℝ in a..b, (N 0 * (γ t)⁻¹ + R (γ t)) := by
        apply intervalIntegral.integral_congr
        intro t _
        exact heq (γ t) (hγne t)
      _ = _ := by rw [intervalIntegral.integral_add hq hr,
        intervalIntegral.integral_const_mul]
  have hbottom := hsplit (fun x => (x : ℂ) - (T : ℂ) * I) (by fun_prop)
    (by intro x hx; have hi := congrArg Complex.im hx; simp at hi; linarith) (-(1 : ℝ) / 2) 1
  have htop := hsplit (fun x => (x : ℂ) + (T : ℂ) * I) (by fun_prop)
    (by intro x hx; have hi := congrArg Complex.im hx; simp at hi; linarith) (-(1 : ℝ) / 2) 1
  have hright := hsplit (fun y => (1 : ℂ) + (y : ℂ) * I) (by fun_prop)
    (by intro y hy; have hr := congrArg Complex.re hy; simp at hr) (-T) T
  have hleft := hsplit (fun y => -(1 : ℂ) / 2 + (y : ℂ) * I) (by fun_prop)
    (by intro y hy; have hr := congrArg Complex.re hy; norm_num at hr) (-T) T
  calc
    _ = N 0 * lemma57RectangleBoundaryIntegral (fun w : ℂ => w⁻¹) T +
        lemma57RectangleBoundaryIntegral R T := by
      unfold lemma57RectangleBoundaryIntegral
      simp only [ofReal_one]
      rw [hbottom, htop, hright, hleft]
      ring
    _ = _ := by
      rw [lemma57RectangleBoundaryIntegral_inv T hT,
        lemma57RectangleBoundaryIntegral_eq_zero_of_differentiable R hR T]
      ring

/-- The pole-removed numerator of the genuine product Mellin integrand. -/
noncomputable def lemma44ProductMellinNumerator {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (s : ℂ) (B : ℝ) (w : ℂ) : ℂ :=
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  DirichletCharacter.LFunction ψ (s + w) *
    DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) (s + w) *
      exp (w * (Real.log B : ℂ)) * lemma57OmegaOne D w

theorem lemma44_product_mellin_numerator_differentiable {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hL : 3 ≤ lemma23PaperL D) (hψ : Lemma23InPsi (D := D) ψ)
    (s : ℂ) (B : ℝ) : Differentiable ℂ (lemma44ProductMellinNumerator χ ψ s B) := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  have hψne : ψ ≠ 1 := by
    intro he
    have hc : ψ.conductor = p := hψ.2.1
    rw [he, DirichletCharacter.conductor_one] at hc
    exact hψ.1.ne_one hc.symm
  have htw := lemma44CharacterTwist_isPrimitive χ ψ hψ.2.1
    (lemma44_family_coprime χ ψ hL hψ)
  have htwne : lemma44CharacterTwist χ ψ ≠ 1 := by
    intro he
    have hc : (lemma44CharacterTwist χ ψ).conductor = D * p := htw
    rw [he, DirichletCharacter.conductor_one] at hc
    exact hψ.1.ne_one (Nat.dvd_one.mp (hc.symm ▸ Nat.dvd_mul_left p D))
  have hfirst := DirichletCharacter.differentiable_LFunction hψne
  have hsecond := DirichletCharacter.differentiable_LFunction htwne
  unfold lemma44ProductMellinNumerator lemma57OmegaOne
  fun_prop

/-- The actual product is the residue, with no residue identity supplied
as an additional hypothesis. -/
theorem lemma44_product_mellin_rectangle_residue {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hL : 3 ≤ lemma23PaperL D) (hψ : Lemma23InPsi (D := D) ψ)
    (s : ℂ) (B : ℝ) {T : ℝ} (hT : 0 < T) :
    letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    lemma57RectangleBoundaryIntegral
      (fun w => lemma44ProductMellinNumerator χ ψ s B w / w) T =
        2 * (Real.pi : ℂ) * I *
          (DirichletCharacter.LFunction ψ s *
            DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) s) := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  simpa [lemma44ProductMellinNumerator, lemma57OmegaOne] using
    lemma44_simple_pole_rectangle (lemma44ProductMellinNumerator χ ψ s B)
      (lemma44_product_mellin_numerator_differentiable χ ψ hL hψ s B) hT

end ZhangLS.Spec
