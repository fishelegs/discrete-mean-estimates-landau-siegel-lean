import ZhangLS.Spec.Lemma112LeftIntegralSplit
/-! # The actual variable-cutoff approximate functional equation for χψ -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Real Topology

noncomputable def lemma112ActualLeftMellinIntegral {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ) (z : ℝ) : ℂ :=
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  (2 * (Real.pi : ℂ) * I)⁻¹ *
    (∫ v : ℝ in -(lemma23PaperL D ^ 20)..(lemma23PaperL D ^ 20),
      (lemma61SingleMellinNumerator (D := D) (lemma44CharacterTwist χ ψ) s (lemma23PaperP D ^ z)
        (-1 + (v : ℂ) * I) / (-1 + (v : ℂ) * I)) * I)

noncomputable def lemma112LeftApproximationConstant : ℝ :=
  (16 + lemma44InverseSquareMass) + (lemma51ErrorConstant + 8 * Real.exp 2) +
    2 * Real.exp 2 * (lemma44InverseSquareMass + lemma61QuarterSeriesMass)

noncomputable def lemma112ApproximationConstant : ℝ :=
  lemma112LeftApproximationConstant + 8 * lemma44InverseSquareMass + 408 * Real.exp 2

lemma lemma112_actual_original_left_dual_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hψ : Lemma23InPsi (D := D) ψ) (hD : 1 < D) (hL : 64 ≤ lemma23PaperL D)
    (hthreshold : lemma23SectionFourModulusThreshold ≤ D) {s : ℂ}
    (hs : Lemma112InRegion D s) {z : ℝ} (hz : z ∈ Icc (1 / 2 : ℝ) (63 / 125 : ℝ)) :
    letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    ‖lemma112ActualLeftMellinIntegral χ ψ s z + lemma23DirichletZ (lemma44CharacterTwist χ ψ) s *
      lemma112GaussianSeries χ ψ⁻¹ (lemma112DualScale D z) (1 - s)‖ ≤
      lemma112LeftApproximationConstant * lemma112ActualE2 χ ψ s := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  let c : ℂ := (2 * (Real.pi : ℂ) * I)⁻¹
  let M := c * (∫ v : ℝ in -(lemma23PaperL D ^ 20)..(lemma23PaperL D ^ 20),
    lemma112ReciprocalModelIntegrand χ ψ s z (-1 + (v : ℂ) * I) * I)
  let E := c * (∫ v : ℝ in -(lemma23PaperL D ^ 20)..(lemma23PaperL D ^ 20),
    lemma112ActualZErrorIntegrand χ ψ s z (-1 + (v : ℂ) * I) * I)
  let T := c * (∫ v : ℝ in -(lemma23PaperL D ^ 20)..(lemma23PaperL D ^ 20),
    lemma112ActualReciprocalTailIntegrand χ ψ s z (-1 + (v : ℂ) * I) * I)
  let ZN := lemma23DirichletZ (lemma44CharacterTwist χ ψ) s *
    lemma112GaussianSeries χ ψ⁻¹ (lemma112DualScale D z) (1 - s)
  have hsplit : lemma112ActualLeftMellinIntegral χ ψ s z = M + E + T :=
    lemma112_actual_original_left_integral_split χ ψ z hψ hD (by linarith) hs
  have hM := lemma112_actual_finite_reciprocal_model_bound χ ψ hψ hD hL hs hz
  have hE := lemma112_actual_original_left_Z_error_bound χ ψ hψ hD hL hthreshold hs hz
  have hT := lemma112_reciprocal_tail_truncation_bound χ ψ hψ hD hL hs hz.1
  change ‖M + ZN‖ ≤ _ at hM
  change ‖E‖ ≤ _ at hE
  change ‖T‖ ≤ _ at hT
  have hm2 : 0 ≤ lemma44InverseSquareMass := tsum_nonneg (fun _ => by positivity)
  have hm4 : 0 ≤ lemma61QuarterSeriesMass := tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hf := lemma112_exp_remainder_le_E2 χ ψ hL (by rw [hs.1]; norm_num)
  have hM' := hM.trans (mul_le_mul_of_nonneg_left hf (by positivity : 0 ≤ 16 + lemma44InverseSquareMass))
  have hT' := hT.trans (mul_le_mul_of_nonneg_left hf (by positivity :
    0 ≤ 2 * Real.exp 2 * (lemma44InverseSquareMass + lemma61QuarterSeriesMass)))
  have hn1 := norm_add_le (M + ZN) E
  have hn2 := norm_add_le (M + ZN + E) T
  have he : lemma112ActualLeftMellinIntegral χ ψ s z + ZN = (M + ZN + E) + T := by
    rw [hsplit]; ring
  change ‖lemma112ActualLeftMellinIntegral χ ψ s z + ZN‖ ≤ _
  rw [he]
  unfold lemma112LeftApproximationConstant
  nlinarith only [hn1, hn2, hM', hE, hT']

lemma lemma112_actual_approximation_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hψ : Lemma23InPsi (D := D) ψ) (hD : 1 < D) (hL : 64 ≤ lemma23PaperL D)
    (hthreshold : lemma23SectionFourModulusThreshold ≤ D) {s : ℂ}
    (hs : Lemma112InRegion D s) {z : ℝ} (hz : z ∈ Icc (1 / 2 : ℝ) (63 / 125 : ℝ)) :
    letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    ‖lemma112GaussianSeries χ ψ (lemma23PaperP D ^ z) s -
      DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) s +
      lemma23DirichletZ (lemma44CharacterTwist χ ψ) s *
        lemma112GaussianSeries χ ψ⁻¹ (lemma112DualScale D z) (1 - s)‖ ≤
      lemma112ApproximationConstant * lemma112ActualE2 χ ψ s := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  let H := lemma23PaperL D ^ 20
  let c : ℂ := (2 * (Real.pi : ℂ) * I)⁻¹
  let R := c * (∫ v : ℝ in -H..H,
    lemma61RightMellinIntegrand (D := D) (lemma44CharacterTwist χ ψ) s (lemma23PaperP D ^ z) 2 v * I)
  let B := c * (∫ x : ℝ in (-1 : ℝ)..2,
    lemma61SingleMellinNumerator (D := D) (lemma44CharacterTwist χ ψ) s (lemma23PaperP D ^ z)
      ((x : ℂ) - (H : ℂ) * I) / ((x : ℂ) - (H : ℂ) * I))
  let U := c * (∫ x : ℝ in (-1 : ℝ)..2,
    lemma61SingleMellinNumerator (D := D) (lemma44CharacterTwist χ ψ) s (lemma23PaperP D ^ z)
      ((x : ℂ) + (H : ℂ) * I) / ((x : ℂ) + (H : ℂ) * I))
  let A := lemma112ActualLeftMellinIntegral χ ψ s z
  let ZN := lemma23DirichletZ (lemma44CharacterTwist χ ψ) s *
    lemma112GaussianSeries χ ψ⁻¹ (lemma112DualScale D z) (1 - s)
  let G := lemma112GaussianSeries χ ψ (lemma23PaperP D ^ z) s
  have h0 : 0 < lemma23PaperL D := by linarith
  have hH : 0 < H := pow_pos h0 20
  have hID : DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) s = B - U + R - A := by
    have h := lemma112_actual_wide_rectangle_residue χ ψ (by linarith) hψ s (lemma23PaperP D ^ z) hH
    have hc : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
    have hh := congrArg (fun x : ℂ => c * x) h
    dsimp only [c] at hh
    rw [inv_mul_cancel_left₀ hc] at hh
    rw [← hh]
    dsimp [B,U,R,A,c,H,lemma112ActualLeftMellinIntegral]
    unfold lemma61RectangleBoundaryIntegral
    simp only [intervalIntegral.integral_mul_const, lemma61RightMellinIntegrand,
      lemma61SingleMellinNumerator, Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_ofNat]
    ring
  have hfull := (lemma112_actual_gaussian_mellin χ ψ s hD
    (Real.rpow_pos_of_pos (show 0 < lemma23PaperP D from Real.exp_pos _) z) (σ := 2) (by norm_num)
    (by rw [hs.1]; norm_num)).2.2
  have htail := lemma112_actual_right_mellin_truncation χ ψ hD hL hs.1 hz
  have hR : ‖R - G‖ ≤ 8 * lemma44InverseSquareMass * Real.exp (-(lemma23PaperL D ^ 10) / 8) := by
    dsimp [R,G,c,H]
    rw [← hfull, ← mul_sub, norm_mul]
    exact (mul_le_mul_of_nonneg_right lemma61_mellin_normalization_norm_le_one (norm_nonneg _)).trans
      (by simpa only [one_mul,norm_sub_rev] using htail)
  have hA := lemma112_actual_original_left_dual_bound χ ψ hψ hD hL hthreshold hs hz
  have hB := lemma112_actual_horizontal_L_integral_bound χ ψ hψ hD hL hs hz
    (t := -H) (by simpa only [abs_neg] using abs_of_pos hH)
  have hU := lemma112_actual_horizontal_L_integral_bound χ ψ hψ hD hL hs hz (t := H) (abs_of_pos hH)
  change ‖A + ZN‖ ≤ _ at hA
  have hB' : ‖B‖ ≤ 204 * Real.exp 2 * Real.exp (-(lemma23PaperL D ^ 10) / 8) := by
    simpa only [B,c,H,Complex.ofReal_neg,neg_mul,sub_eq_add_neg] using hB
  change ‖U‖ ≤ _ at hU
  have hf := lemma112_exp_remainder_le_E2 χ ψ hL (by rw [hs.1]; norm_num)
  have hm : 0 ≤ lemma44InverseSquareMass := tsum_nonneg (fun _ => by positivity)
  have hR' := hR.trans (mul_le_mul_of_nonneg_left hf (by positivity : 0 ≤ 8 * lemma44InverseSquareMass))
  have hB'' := hB'.trans (mul_le_mul_of_nonneg_left hf (by positivity : 0 ≤ 204 * Real.exp 2))
  have hU' := hU.trans (mul_le_mul_of_nonneg_left hf (by positivity : 0 ≤ 204 * Real.exp 2))
  have he : G - DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) s + ZN =
      -(((R - G) - (A + ZN)) + B - U) := by rw [hID]; ring
  change ‖G - DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) s + ZN‖ ≤ _
  rw [he, norm_neg]
  have hn1 := norm_sub_le (R - G) (A + ZN)
  have hn2 := norm_add_le ((R - G) - (A + ZN)) B
  have hn3 := norm_sub_le (((R - G) - (A + ZN)) + B) U
  unfold lemma112ApproximationConstant
  nlinarith only [hn1,hn2,hn3,hR',hA,hB'',hU']

end ZhangLS.Spec
