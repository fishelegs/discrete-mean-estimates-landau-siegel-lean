import ZhangLS.Spec.Lemma61ShortTruncation

/-! # Faithful original Lemma 6.1

Finite short-polynomial Gaussian inversion, actual original-left integral
decomposition and N approximation, actual full horizontal L edges and
uniform constants/thresholds yield lemma61_proved : Lemma61Target.
Original Psi, strict region and actual L/K/N/E1 are retained.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Real Topology
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

noncomputable def lemma61ReciprocalModelIntegrand {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (s w : ℂ) : ℂ :=
  lemma23DirichletZ ψ s * exp (-2 * (Real.log (lemma56PaperT D) : ℂ) * w) *
    lemma61ShortPolynomial D ψ⁻¹ (1 - s - w) * lemma57OmegaOne D w / w

lemma lemma61_reciprocal_model_reflection {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (s : ℂ) (v : ℝ) :
    lemma61ReciprocalModelIntegrand (D := D) ψ s (-1 + (v : ℂ) * I) * I =
      -lemma23DirichletZ ψ s *
        (lemma61ShortRightMellinIntegrand D ψ⁻¹ (1 - s) (lemma56PaperT D ^ 2) 1 (-v) * I) := by
  let u : ℂ := 1 + ((-v : ℝ) : ℂ) * I
  have hw : (-1 : ℂ) + (v : ℂ) * I = -u := by dsimp [u]; push_cast; ring
  have hs : 1 - s - (-u) = (1 - s) + u := by ring
  have hlog : (Real.log (lemma56PaperT D ^ 2) : ℂ) =
      2 * (Real.log (lemma56PaperT D) : ℂ) := by rw [Real.log_pow]; push_cast; ring
  have homega : lemma57OmegaOne D (-u) = lemma57OmegaOne D u := by
    unfold lemma57OmegaOne
    congr 2
    ring
  unfold lemma61ReciprocalModelIntegrand lemma61ShortRightMellinIntegrand
  change lemma23DirichletZ ψ s * exp (-2 * (Real.log (lemma56PaperT D) : ℂ) *
      (-1 + (v : ℂ) * I)) * lemma61ShortPolynomial D ψ⁻¹ (1 - s - (-1 + (v : ℂ) * I)) *
      lemma57OmegaOne D (-1 + (v : ℂ) * I) / (-1 + (v : ℂ) * I) * I =
    -lemma23DirichletZ ψ s * (lemma61ShortPolynomial D ψ⁻¹ ((1 - s) + u) *
      exp (u * (Real.log (lemma56PaperT D ^ 2) : ℂ)) * lemma57OmegaOne D u / u * I)
  rw [hw,hs,homega,hlog]
  have he : -2 * (Real.log (lemma56PaperT D) : ℂ) * (-u) =
      u * (2 * (Real.log (lemma56PaperT D) : ℂ)) := by ring
  rw [he]
  ring

lemma lemma61_reciprocal_model_vertical_identity {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (s : ℂ) (H : ℝ) :
    (2 * (Real.pi : ℂ) * I)⁻¹ *
      (∫ v : ℝ in -H..H,
        lemma61ReciprocalModelIntegrand (D := D) ψ s (-1 + (v : ℂ) * I) * I) =
      -lemma23DirichletZ ψ s * ((2 * (Real.pi : ℂ) * I)⁻¹ *
        (∫ v : ℝ in -H..H,
          lemma61ShortRightMellinIntegrand D ψ⁻¹ (1 - s) (lemma56PaperT D ^ 2) 1 v * I)) := by
  simp_rw [lemma61_reciprocal_model_reflection ψ s]
  rw [intervalIntegral.integral_const_mul]
  have hc := intervalIntegral.integral_comp_neg
    (fun v : ℝ => lemma61ShortRightMellinIntegrand D ψ⁻¹ (1 - s)
      (lemma56PaperT D ^ 2) 1 v * I) (a := -H) (b := H)
  simp only [neg_neg] at hc
  rw [hc]
  ring

lemma lemma61_actual_finite_reciprocal_model_N_bound {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : Lemma23InPsi (D := D) ψ)
    (hD : 1 < D) (hL : 64 ≤ lemma23PaperL D) {s : ℂ} (hs : Lemma61InRegion D s) :
    ‖(2 * (Real.pi : ℂ) * I)⁻¹ *
      (∫ v : ℝ in -(lemma23PaperL D ^ 20)..(lemma23PaperL D ^ 20),
        lemma61ReciprocalModelIntegrand (D := D) ψ s (-1 + (v : ℂ) * I) * I) +
      lemma23DirichletZ ψ s * lemma61ActualN D ψ⁻¹ (1 - s)‖ ≤
      Real.exp (1 + 4 * Real.pi) * (16 + lemma44InverseSquareMass) *
        Real.exp (-(lemma23PaperL D ^ 10) / 8) := by
  have hre := (lemma61_region_real_parts (by linarith) hs).2.le
  have hn := lemma61_actual_finite_short_mellin_N_bound ψ⁻¹ s hD hL hre
  have hz := lemma61_actual_Z_original_norm_bound ψ hψ (by linarith) hs
  rw [lemma61_reciprocal_model_vertical_identity]
  rw [show -lemma23DirichletZ ψ s * ((2 * (Real.pi : ℂ) * I)⁻¹ *
      (∫ v : ℝ in -(lemma23PaperL D ^ 20)..(lemma23PaperL D ^ 20),
        lemma61ShortRightMellinIntegrand D ψ⁻¹ (1 - s) (lemma56PaperT D ^ 2) 1 v * I)) +
      lemma23DirichletZ ψ s * lemma61ActualN D ψ⁻¹ (1 - s) =
      -lemma23DirichletZ ψ s * (((2 * (Real.pi : ℂ) * I)⁻¹ *
      (∫ v : ℝ in -(lemma23PaperL D ^ 20)..(lemma23PaperL D ^ 20),
        lemma61ShortRightMellinIntegrand D ψ⁻¹ (1 - s) (lemma56PaperT D ^ 2) 1 v * I)) -
        lemma61ActualN D ψ⁻¹ (1 - s)) by ring]
  rw [norm_mul,norm_neg]
  exact (mul_le_mul hz hn (norm_nonneg _) (Real.exp_nonneg _)).trans_eq (by ring)

end ZhangLS.Spec
