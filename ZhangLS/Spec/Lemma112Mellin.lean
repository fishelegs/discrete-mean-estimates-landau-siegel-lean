import ZhangLS.Spec.Lemma112Parameters
/-! # Actual Mellin inversion and finite residues at conductor Dp -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Real Topology ComplexConjugate

noncomputable def lemma112GaussianSeries {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (B : ℝ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, LSeries.term (lemma112Coefficient χ ψ) s n *
    (zhangGaussianWeight D (B / n) : ℂ)

lemma lemma112_actual_gaussian_mellin {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (s : ℂ) (hD : 1 < D) {B σ : ℝ}
    (hB : 0 < B) (hσ : 0 < σ) (hs : 1 < s.re + σ) :
    letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    Integrable (lemma61RightMellinIntegrand (D := D) (lemma44CharacterTwist χ ψ) s B σ) ∧
      Summable (fun n : ℕ => LSeries.term (lemma112Coefficient χ ψ) s n *
        (zhangGaussianWeight D (B / n) : ℂ)) ∧
      (2 * (Real.pi : ℂ) * I)⁻¹ *
        (∫ t : ℝ, lemma61RightMellinIntegrand (D := D) (lemma44CharacterTwist χ ψ) s B σ t * I) =
          lemma112GaussianSeries χ ψ B s := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  simpa only [lemma112GaussianSeries, lemma112_coefficient_eq_twist] using
    lemma61_actual_right_gaussian_mellin (lemma44CharacterTwist χ ψ) s hD hB hσ hs

/-- The actual Gaussian series converges at every s, not just in Re(s)>1. -/
lemma lemma112_actual_gaussian_summable {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (s : ℂ) (hD : 1 < D) {B : ℝ} (hB : 0 < B) :
    Summable (fun n : ℕ => LSeries.term (lemma112Coefficient χ ψ) s n *
      (zhangGaussianWeight D (B / n) : ℂ)) := by
  exact (lemma112_actual_gaussian_mellin χ ψ s hD hB
    (σ := |s.re| + 2) (by positivity) (by linarith [neg_le_abs s.re])).2.1

lemma lemma112_actual_mellin_numerator_entire {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hL : 3 ≤ lemma23PaperL D) (hψ : Lemma23InPsi (D := D) ψ)
    (s : ℂ) (B : ℝ) :
    letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    Differentiable ℂ (lemma61SingleMellinNumerator (D := D) (lemma44CharacterTwist χ ψ) s B) := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  have hfirst := DirichletCharacter.differentiable_LFunction
    (lemma112_twist_family_data χ ψ hL hψ).2.2.2
  unfold lemma61SingleMellinNumerator lemma57OmegaOne
  fun_prop

lemma lemma112_actual_wide_rectangle_residue {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hL : 3 ≤ lemma23PaperL D) (hψ : Lemma23InPsi (D := D) ψ)
    (s : ℂ) (B : ℝ) {H : ℝ} (hH : 0 < H) :
    letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    lemma61RectangleBoundaryIntegral
      (fun w : ℂ => lemma61SingleMellinNumerator (D := D) (lemma44CharacterTwist χ ψ) s B w / w) H =
        2 * (Real.pi : ℂ) * I * DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) s := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  simpa [lemma61SingleMellinNumerator, lemma57OmegaOne] using
    lemma61_simple_pole_wide_rectangle
      (lemma61SingleMellinNumerator (D := D) (lemma44CharacterTwist χ ψ) s B)
      (lemma112_actual_mellin_numerator_entire χ ψ hL hψ s B) hH

lemma lemma112_scale_log_bound {D : ℕ} (hL : 3 ≤ lemma23PaperL D)
    {z : ℝ} (hz : z ∈ Icc (1 / 2 : ℝ) (63 / 125 : ℝ)) :
    Real.log (lemma23PaperP D ^ z) ≤ 2 * lemma23PaperL D ^ 9 := by
  rw [lemma23PaperP, Real.log_rpow (Real.exp_pos _), Real.log_exp]
  exact mul_le_mul_of_nonneg_right (by linarith [hz.2]) (pow_nonneg (by linarith) _)

/-- The actual finite right line, uniformly in the original z interval. -/
lemma lemma112_actual_right_mellin_truncation {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : 1 < D) (hL : 64 ≤ lemma23PaperL D)
    {s : ℂ} (hs : s.re = 1 / 2) {z : ℝ}
    (hz : z ∈ Icc (1 / 2 : ℝ) (63 / 125 : ℝ)) :
    letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    ‖(∫ v : ℝ, lemma61RightMellinIntegrand (D := D) (lemma44CharacterTwist χ ψ)
        s (lemma23PaperP D ^ z) 2 v * I) -
      (∫ v : ℝ in -(lemma23PaperL D ^ 20)..(lemma23PaperL D ^ 20),
        lemma61RightMellinIntegrand (D := D) (lemma44CharacterTwist χ ψ)
          s (lemma23PaperP D ^ z) 2 v * I)‖ ≤
        8 * lemma44InverseSquareMass * Real.exp (-(lemma23PaperL D ^ 10) / 8) := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  exact lemma61_actual_right_mellin_truncation (lemma44CharacterTwist χ ψ) hD hL
    (by rw [hs]; norm_num) (Real.rpow_pos_of_pos (Real.exp_pos _) _)
    (lemma112_scale_log_bound (by linarith) hz)

end ZhangLS.Spec
