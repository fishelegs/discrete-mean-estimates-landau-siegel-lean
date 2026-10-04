import ZhangLS.Spec.DivisorConductorBlockMomentsEnergy

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec.DivisorConductorBlockMoments
open Complex Finset
open scoped Classical ComplexConjugate

theorem long_nontrivial_moment {X R C_b : ℝ} (hX : 1 ≤ X) (hR : 1 ≤ R)
    (hC : 0 ≤ C_b) {b : ℕ → ℂ} (hb : CoefficientBound C_b b)
    (d h : ℕ) (hd : 0 < d) (t : ℝ) :
    (∑ r ∈ primitiveDyadicModuli R, ((r : ℝ) / (r.totient : ℝ)) *
      ∑ θ ∈ univ.filter (fun θ : DirichletCharacter ℂ r => θ.IsPrimitive),
        ‖longPolynomial d h X b r θ t‖ ^ 2) ≤
      (16 * (32 + Real.pi ^ 2)) * (1 + R ^ 2 / X) * longEnvelope C_b d X := by
  simp_rw [longPolynomial_coefficient_sum]
  have hs := primitive_large_sieve_finset_weighted (primitiveDyadicModuli R)
    (fun r hr => (mem_primitiveDyadicModuli.mp hr).1) (longIndices h X)
    (longCoefficient d b t) hR (fun r hr => (mem_primitiveDyadicModuli.mp hr).2.2.le)
    0 ⌊8 * X⌋₊ (fun l hl => ⟨Nat.zero_le _, by
      simpa only [zero_add] using (mem_Icc.mp (longIndices_subset h X hl)).2⟩)
  apply hs.trans
  have hXp : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hE := longEnvelope_nonneg C_b d hX
  have hfloor : (⌊8 * X⌋₊ : ℝ) ≤ 8 * X := Nat.floor_le (by positivity)
  have hK : 0 ≤ 32 + Real.pi ^ 2 := by positivity
  have hratio : 0 ≤ R ^ 2 / X := div_nonneg (sq_nonneg R) hXp.le
  have hf : 2 * (R ^ 2 / X) + 16 ≤ 16 * (1 + R ^ 2 / X) := by nlinarith
  calc
    _ ≤ (32 + Real.pi ^ 2) * (R ^ 2 + (⌊8 * X⌋₊ : ℝ)) *
        ((2 / X) * longEnvelope C_b d X) :=
      mul_le_mul_of_nonneg_left (long_coefficient_energy hX hC hb d h hd t) (by positivity)
    _ ≤ (32 + Real.pi ^ 2) * (R ^ 2 + 8 * X) *
        ((2 / X) * longEnvelope C_b d X) := by gcongr
    _ = (32 + Real.pi ^ 2) * (2 * (R ^ 2 / X) + 16) * longEnvelope C_b d X := by
      field_simp
      ring
    _ ≤ (32 + Real.pi ^ 2) * (16 * (1 + R ^ 2 / X)) * longEnvelope C_b d X :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hf hK) hE
    _ = _ := by ring

/-- Exact real dyadic block, including r=1, with the stronger scale ratio. -/
theorem long_block_strong {X R C_b : ℝ} (hX : 1 ≤ X) (hR : 1 ≤ R)
    (hC : 0 ≤ C_b) {b : ℕ → ℂ} (hb : CoefficientBound C_b b)
    (d h : ℕ) (hd : 0 < d) (t : ℝ) :
    blockMoment R (fun r θ => longPolynomial d h X b r θ t) ≤
      blockConstant * (1 + R ^ 2 / X) * longEnvelope C_b d X := by
  apply (blockMoment_le_one_add_nontrivial R _).trans
  have hl := long_one_moment hX hC hb d h hd t
  have hn := long_nontrivial_moment hX hR hC hb d h hd t
  have hE := longEnvelope_nonneg C_b d hX
  have hratio : 0 ≤ R ^ 2 / X := div_nonneg (sq_nonneg R) (by linarith)
  calc
    _ ≤ 16 * longEnvelope C_b d X +
        (16 * (32 + Real.pi ^ 2)) * (1 + R ^ 2 / X) * longEnvelope C_b d X := add_le_add hl hn
    _ ≤ 16 * (1 + R ^ 2 / X) * longEnvelope C_b d X +
        (16 * (32 + Real.pi ^ 2)) * (1 + R ^ 2 / X) * longEnvelope C_b d X := by
      gcongr
      linarith
    _ = _ := by unfold blockConstant; ring

/-- The requested R²≤X specialization, with C=32*(33+π²). -/
theorem long_block_bound {X R C_b : ℝ} (hX : 1 ≤ X) (hR : 1 ≤ R)
    (hRX : R ^ 2 ≤ X) (hC : 0 ≤ C_b) {b : ℕ → ℂ}
    (hb : CoefficientBound C_b b) (d h : ℕ) (hd : 0 < d) (t : ℝ) :
    blockMoment R (fun r θ => longPolynomial d h X b r θ t) ≤
      (32 * (33 + Real.pi ^ 2)) * C_b ^ 2 * (lemma34Tau 5 d : ℝ) ^ 2 *
        (1 + Real.log (8 * X)) ^ 25 := by
  apply (long_block_strong hX hR hC hb d h hd t).trans
  have hratio : R ^ 2 / X ≤ 1 := (div_le_one (by linarith : 0 < X)).mpr hRX
  have hE := longEnvelope_nonneg C_b d hX
  have hK : 0 ≤ blockConstant := blockConstant_pos.le
  calc
    _ ≤ blockConstant * 2 * longEnvelope C_b d X := by
      gcongr
      linarith
    _ = _ := by unfold blockConstant longEnvelope logWeight; ring

theorem positive_long_block_strong {X R C_b : ℝ} (hX : 1 ≤ X) (hR : 1 ≤ R)
    (hC : 0 ≤ C_b) {b : ℕ → ℂ} (hb : CoefficientBound C_b b)
    (d h : ℕ+) (t : ℝ) :
    blockMoment R (fun r θ => positiveLongPolynomial d h X b r θ t) ≤
      blockConstant * (1 + R ^ 2 / X) * longEnvelope C_b (d : ℕ) X := by
  simpa only [positiveLongPolynomial_eq] using long_block_strong hX hR hC hb
    (d : ℕ) (h : ℕ) d.property t

theorem positive_long_block_bound {X R C_b : ℝ} (hX : 1 ≤ X) (hR : 1 ≤ R)
    (hRX : R ^ 2 ≤ X) (hC : 0 ≤ C_b) {b : ℕ → ℂ}
    (hb : CoefficientBound C_b b) (d h : ℕ+) (t : ℝ) :
    blockMoment R (fun r θ => positiveLongPolynomial d h X b r θ t) ≤
      (32 * (33 + Real.pi ^ 2)) * C_b ^ 2 * (lemma34Tau 5 (d : ℕ) : ℝ) ^ 2 *
        (1 + Real.log (8 * X)) ^ 25 := by
  simpa only [positiveLongPolynomial_eq] using long_block_bound hX hR hRX hC hb
    (d : ℕ) (h : ℕ) d.property t

end ZhangLS.Spec.DivisorConductorBlockMoments
