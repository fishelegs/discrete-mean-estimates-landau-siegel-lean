import ZhangLS.Spec.Lemma61LeftIntegralSplit

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

noncomputable def lemma61ActualLeftMellinIntegral {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (s : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * I)⁻¹ *
    (∫ v : ℝ in -(lemma23PaperL D ^ 20)..(lemma23PaperL D ^ 20),
      (lemma61SingleMellinNumerator (D := D) ψ s (lemma61PaperP4 D) (-1 + (v : ℂ) * I) /
        (-1 + (v : ℂ) * I)) * I)

noncomputable def lemma61LeftApproximationConstant : ℝ :=
  Real.exp (1 + 4 * Real.pi) * (16 + lemma44InverseSquareMass) +
    (35 * Real.exp (246 * Real.pi + 1) + 16 * Real.exp (2 + 4 * Real.pi)) +
    2 * Real.exp (2 + 4 * Real.pi) * (lemma44InverseSquareMass + lemma61QuarterSeriesMass)

lemma lemma61_actual_original_left_N_bound {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : Lemma23InPsi (D := D) ψ)
    (hD : 1 < D) (hL : 64 ≤ lemma23PaperL D) {s : ℂ} (hs : Lemma61InRegion D s) :
    ‖lemma61ActualLeftMellinIntegral (D := D) ψ s +
      lemma23DirichletZ ψ s * lemma61ActualN D ψ⁻¹ (1 - s)‖ ≤
      lemma61LeftApproximationConstant * lemma61ActualE1 D ψ s (1 / 8) := by
  let c : ℂ := (2 * (Real.pi : ℂ) * I)⁻¹
  let M := c * (∫ v : ℝ in -(lemma23PaperL D ^ 20)..(lemma23PaperL D ^ 20),
    lemma61ReciprocalModelIntegrand (D := D) ψ s (-1 + (v : ℂ) * I) * I)
  let E := c * (∫ v : ℝ in -(lemma23PaperL D ^ 20)..(lemma23PaperL D ^ 20),
    lemma61ActualZErrorIntegrand (D := D) ψ s (-1 + (v : ℂ) * I) * I)
  let T := c * (∫ v : ℝ in -(lemma23PaperL D ^ 20)..(lemma23PaperL D ^ 20),
    lemma61ActualReciprocalTailIntegrand (D := D) ψ s (-1 + (v : ℂ) * I) * I)
  let ZN := lemma23DirichletZ ψ s * lemma61ActualN D ψ⁻¹ (1 - s)
  have hsplit : lemma61ActualLeftMellinIntegral (D := D) ψ s = M + E + T :=
    lemma61_actual_original_left_integral_split ψ hψ hD (by linarith) hs
  have hM := lemma61_actual_finite_reciprocal_model_N_bound ψ hψ hD hL hs
  have hE := lemma61_actual_original_left_Z_error_bound ψ hψ hL hs
  have hT := lemma61_actual_reciprocal_tail_truncation_bound ψ hψ hL hs
  change ‖M + ZN‖ ≤ _ at hM
  change ‖E‖ ≤ _ at hE
  change ‖T‖ ≤ _ at hT
  have hm2 : 0 ≤ lemma44InverseSquareMass := tsum_nonneg (fun _ => by positivity)
  have hm4 : 0 ≤ lemma61QuarterSeriesMass := tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hf := lemma61_E1_exponential_floor (D := D) ψ s (1 / 8)
  have hf' : Real.exp (-(lemma23PaperL D ^ 10) / 8) ≤ lemma61ActualE1 D ψ s (1 / 8) := by
    convert hf using 1 <;> ring
  have hM' := hM.trans (mul_le_mul_of_nonneg_left hf' (by positivity :
    0 ≤ Real.exp (1 + 4 * Real.pi) * (16 + lemma44InverseSquareMass)))
  have hT' := hT.trans (mul_le_mul_of_nonneg_left hf' (by positivity :
    0 ≤ 2 * Real.exp (2 + 4 * Real.pi) * (lemma44InverseSquareMass + lemma61QuarterSeriesMass)))
  have hn1 := norm_add_le (M + ZN) E
  have hn2 := norm_add_le (M + ZN + E) T
  have he : lemma61ActualLeftMellinIntegral (D := D) ψ s + ZN = (M + ZN + E) + T := by
    rw [hsplit]; ring
  change ‖lemma61ActualLeftMellinIntegral (D := D) ψ s + ZN‖ ≤ _
  rw [he]
  unfold lemma61LeftApproximationConstant
  nlinarith only [hn1,hn2,hM',hE,hT']

end ZhangLS.Spec
