import ZhangLS.Spec.Lemma61HorizontalTruncation

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

noncomputable def lemma61ApproximationConstant : ℝ :=
  lemma61LeftApproximationConstant + 9 * lemma44InverseSquareMass +
    816 * Real.exp (2 + 4 * Real.pi)

lemma lemma61_actual_approximation_bound {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : Lemma23InPsi (D := D) ψ)
    (hD : 1 < D) (hL : 64 ≤ lemma23PaperL D) {s : ℂ} (hs : Lemma61InRegion D s) :
    ‖DirichletCharacter.LFunction ψ s - lemma61ActualK D ψ s -
      lemma23DirichletZ ψ s * lemma61ActualN D ψ⁻¹ (1 - s)‖ ≤
      lemma61ApproximationConstant * lemma61ActualE1 D ψ s (1 / 8) := by
  let H := lemma23PaperL D ^ 20
  let c : ℂ := (2 * (Real.pi : ℂ) * I)⁻¹
  let R := c * (∫ v : ℝ in -H..H,
    lemma61RightMellinIntegrand (D := D) ψ s (lemma61PaperP4 D) 2 v * I)
  let B := c * (∫ x : ℝ in (-1 : ℝ)..2,
    lemma61SingleMellinNumerator (D := D) ψ s (lemma61PaperP4 D) ((x : ℂ) - (H : ℂ) * I) /
      ((x : ℂ) - (H : ℂ) * I))
  let U := c * (∫ x : ℝ in (-1 : ℝ)..2,
    lemma61SingleMellinNumerator (D := D) ψ s (lemma61PaperP4 D) ((x : ℂ) + (H : ℂ) * I) /
      ((x : ℂ) + (H : ℂ) * I))
  let A := lemma61ActualLeftMellinIntegral (D := D) ψ s
  let ZN := lemma23DirichletZ ψ s * lemma61ActualN D ψ⁻¹ (1 - s)
  have h0 : 0 < lemma23PaperL D := by linarith
  have hH : 0 < H := pow_pos h0 20
  have hID : DirichletCharacter.LFunction ψ s = B - U + R - A := by
    have h := lemma61_actual_rectangle_identity ψ hψ s (lemma61PaperP4 D) hH
    dsimp [H] at h
    dsimp [B,U,R,A,c,H,lemma61ActualLeftMellinIntegral]
    simp only [intervalIntegral.integral_mul_const]
    simp only [lemma61RightMellinIntegrand,lemma61SingleMellinNumerator] at h ⊢
    simp only [Complex.ofReal_neg,Complex.ofReal_one,Complex.ofReal_ofNat,sub_eq_add_neg,add_assoc] at h ⊢
    linear_combination h
  have hR := lemma61_actual_finite_right_K_bound ψ hD hL hs
  have hA := lemma61_actual_original_left_N_bound ψ hψ hD hL hs
  have hB := lemma61_actual_horizontal_L_integral_bound ψ hψ hL hs (t := -H)
    (by simpa only [abs_neg] using abs_of_pos hH)
  have hU := lemma61_actual_horizontal_L_integral_bound ψ hψ hL hs (t := H) (abs_of_pos hH)
  change ‖R - lemma61ActualK D ψ s‖ ≤ _ at hR
  change ‖A + ZN‖ ≤ _ at hA
  have hB' : ‖B‖ ≤ 408 * Real.exp (2 + 4 * Real.pi) * Real.exp (-(lemma23PaperL D ^ 10) / 8) := by
    simpa only [B,c,H,Complex.ofReal_neg,neg_mul,sub_eq_add_neg] using hB
  change ‖U‖ ≤ _ at hU
  have hf : Real.exp (-(lemma23PaperL D ^ 10) / 8) ≤ lemma61ActualE1 D ψ s (1 / 8) := by
    convert lemma61_E1_exponential_floor (D := D) ψ s (1 / 8) using 1 <;> ring
  have hm : 0 ≤ lemma44InverseSquareMass := tsum_nonneg (fun _ => by positivity)
  have hR' := hR.trans (mul_le_mul_of_nonneg_left hf (by positivity : 0 ≤ 9 * lemma44InverseSquareMass))
  have hB'' := hB'.trans (mul_le_mul_of_nonneg_left hf (by positivity : 0 ≤ 408 * Real.exp (2 + 4 * Real.pi)))
  have hU' := hU.trans (mul_le_mul_of_nonneg_left hf (by positivity : 0 ≤ 408 * Real.exp (2 + 4 * Real.pi)))
  have he : DirichletCharacter.LFunction ψ s - lemma61ActualK D ψ s - ZN =
      ((R - lemma61ActualK D ψ s) - (A + ZN)) + B - U := by rw [hID]; ring
  change ‖DirichletCharacter.LFunction ψ s - lemma61ActualK D ψ s - ZN‖ ≤ _
  rw [he]
  have hn1 := norm_sub_le (R - lemma61ActualK D ψ s) (A + ZN)
  have hn2 := norm_add_le ((R - lemma61ActualK D ψ s) - (A + ZN)) B
  have hn3 := norm_sub_le (((R - lemma61ActualK D ψ s) - (A + ZN)) + B) U
  unfold lemma61ApproximationConstant
  nlinarith only [hn1,hn2,hn3,hR',hA,hB'',hU']

end ZhangLS.Spec
