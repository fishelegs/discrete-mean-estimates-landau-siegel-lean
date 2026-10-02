import ZhangLS.Spec.Lemma112ShortTruncation
import ZhangLS.Spec.Lemma112OriginalLeftError
/-! # Exact reflection of the conductor-Dp reciprocal model -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Real Topology

noncomputable def lemma112ReciprocalModelIntegrand {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ) (z : ℝ) (w : ℂ) : ℂ :=
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  lemma23DirichletZ (lemma44CharacterTwist χ ψ) s * exp (-w * (Real.log (lemma112DualScale D z) : ℂ)) *
    lemma112ShortPolynomial χ ψ⁻¹ (1 - s - w) * lemma57OmegaOne D w / w

lemma lemma112_reciprocal_model_reflection {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ) (z v : ℝ) :
    letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    lemma112ReciprocalModelIntegrand χ ψ s z (-1 + (v : ℂ) * I) * I =
      -lemma23DirichletZ (lemma44CharacterTwist χ ψ) s *
        (lemma112ShortRightMellinIntegrand χ ψ⁻¹ (1 - s) (lemma112DualScale D z) 1 (-v) * I) := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  let u : ℂ := 1 + ((-v : ℝ) : ℂ) * I
  have hw : (-1 : ℂ) + (v : ℂ) * I = -u := by dsimp [u]; push_cast; ring
  have hs : 1 - s - (-u) = (1 - s) + u := by ring
  have homega : lemma57OmegaOne D (-u) = lemma57OmegaOne D u := by
    unfold lemma57OmegaOne
    congr 2
    ring
  unfold lemma112ReciprocalModelIntegrand lemma112ShortRightMellinIntegrand
  change lemma23DirichletZ (lemma44CharacterTwist χ ψ) s *
      exp (-(-1 + (v : ℂ) * I) * (Real.log (lemma112DualScale D z) : ℂ)) *
      lemma112ShortPolynomial χ ψ⁻¹ (1 - s - (-1 + (v : ℂ) * I)) *
      lemma57OmegaOne D (-1 + (v : ℂ) * I) / (-1 + (v : ℂ) * I) * I =
    -lemma23DirichletZ (lemma44CharacterTwist χ ψ) s *
      (lemma112ShortPolynomial χ ψ⁻¹ ((1 - s) + u) *
        exp (u * (Real.log (lemma112DualScale D z) : ℂ)) * lemma57OmegaOne D u / u * I)
  rw [hw, hs, homega]
  simp only [neg_neg]
  ring

lemma lemma112_reciprocal_model_vertical_identity {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ) (z H : ℝ) :
    letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    (2 * (Real.pi : ℂ) * I)⁻¹ *
      (∫ v : ℝ in -H..H, lemma112ReciprocalModelIntegrand χ ψ s z (-1 + (v : ℂ) * I) * I) =
      -lemma23DirichletZ (lemma44CharacterTwist χ ψ) s * ((2 * (Real.pi : ℂ) * I)⁻¹ *
        (∫ v : ℝ in -H..H, lemma112ShortRightMellinIntegrand χ ψ⁻¹ (1 - s) (lemma112DualScale D z) 1 v * I)) := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  simp_rw [lemma112_reciprocal_model_reflection χ ψ s z]
  rw [intervalIntegral.integral_const_mul]
  have hc := intervalIntegral.integral_comp_neg
    (fun v : ℝ => lemma112ShortRightMellinIntegrand χ ψ⁻¹ (1 - s) (lemma112DualScale D z) 1 v * I)
    (a := -H) (b := H)
  simp only [neg_neg] at hc
  rw [hc]
  ring

lemma lemma112_actual_finite_reciprocal_model_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hψ : Lemma23InPsi (D := D) ψ) (hD : 1 < D) (hL : 64 ≤ lemma23PaperL D)
    {s : ℂ} (hs : Lemma112InRegion D s) {z : ℝ}
    (hz : z ∈ Icc (1 / 2 : ℝ) (63 / 125 : ℝ)) :
    letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    ‖(2 * (Real.pi : ℂ) * I)⁻¹ *
      (∫ v : ℝ in -(lemma23PaperL D ^ 20)..(lemma23PaperL D ^ 20),
        lemma112ReciprocalModelIntegrand χ ψ s z (-1 + (v : ℂ) * I) * I) +
      lemma23DirichletZ (lemma44CharacterTwist χ ψ) s *
        lemma112GaussianSeries χ ψ⁻¹ (lemma112DualScale D z) (1 - s)‖ ≤
      (16 + lemma44InverseSquareMass) * Real.exp (-(lemma23PaperL D ^ 10) / 8) := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  have hn := lemma112_actual_finite_short_mellin_dual_bound χ ψ⁻¹ s hD hL (by rw [hs.1]; norm_num) hz
  have htw := lemma112_twist_family_data χ ψ (by linarith) hψ
  have hZ : ‖lemma23DirichletZ (lemma44CharacterTwist χ ψ) s‖ = 1 :=
    lemma23DirichletZ_norm_eq_one_on_critical_line _ htw.1 htw.2.2.1 hs.1
  rw [lemma112_reciprocal_model_vertical_identity]
  have he : ∀ A B : ℂ, -lemma23DirichletZ (lemma44CharacterTwist χ ψ) s * A +
      lemma23DirichletZ (lemma44CharacterTwist χ ψ) s * B =
      lemma23DirichletZ (lemma44CharacterTwist χ ψ) s * (B - A) := by intros; ring
  rw [he, norm_mul, hZ, one_mul, norm_sub_rev]
  exact hn

end ZhangLS.Spec
