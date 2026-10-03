import ZhangLS.Spec.Lemma111GaussianFarTail
import ZhangLS.Spec.Proposition26ProfileBV
import ZhangLS.Spec.Proposition26OriginalObjects

/-! The original truncated Gaussian errors, normalized by exactly L^24. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace ZhangLS.Spec
open Finset Complex
open scoped BigOperators Classical

noncomputable def proposition26GaussianCutoff (D : ℕ) : ℝ :=
  lemma23PaperP D ^ (101/200 : ℝ)

lemma proposition26_P505_le_polynomial_cutoff {D : ℕ} (hL : 64 ≤ lemma23PaperL D) :
    lemma23PaperP D ^ (101/200 : ℝ) ≤ lemma81Cutoff D := by
  have hP : 0 < lemma23PaperP D := Real.exp_pos _
  have hT : 0 < lemma56PaperT D := Real.exp_pos _
  have hC : 0 < lemma81Cutoff D := mul_pos hP (zpow_pos hT _)
  have h1 : 1 ≤ lemma23PaperL D := by linarith
  have h7 : (8:ℝ) ≤ lemma23PaperL D ^ 7 := by
    have hpow := pow_le_pow_right₀ h1 (by norm_num : 1 ≤ 7)
    simp only [pow_one] at hpow
    linarith
  have h9 : 8 * lemma23PaperL D ^ 2 ≤ lemma23PaperL D ^ 9 := by
    calc
      _ ≤ lemma23PaperL D ^ 7 * lemma23PaperL D ^ 2 :=
        mul_le_mul_of_nonneg_right h7 (sq_nonneg _)
      _ = _ := by ring
  have hr : lemma23PaperL D ^ (11/10:ℝ) ≤ lemma23PaperL D ^ (2:ℕ) := by
    simpa only [Real.rpow_two] using
      Real.rpow_le_rpow_of_exponent_le h1 (by norm_num : (11/10:ℝ) ≤ (2:ℝ))
  have hlogC : Real.log (lemma81Cutoff D) =
      lemma23PaperL D ^ 9 - 2 * lemma23PaperL D ^ (11/10:ℝ) := by
    rw [lemma81Cutoff, Real.log_mul hP.ne' (zpow_pos hT (-2:ℤ)).ne', Real.log_zpow,
      lemma23PaperP, lemma56PaperT, Real.log_exp, Real.log_exp]
    norm_num <;> ring
  apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hP _) hC).mp
  rw [Real.log_rpow hP, hlogC, lemma23PaperP, Real.log_exp]
  linarith [sq_nonneg (lemma23PaperL D)]

noncomputable def proposition26NormalizedGaussianProfile (D : ℕ)
    (e : ℝ → ℝ) (n : ℕ) : ℂ :=
  ((lemma111Scale D *
    (if (n:ℝ) < proposition26GaussianCutoff D then e n else 0) : ℝ) : ℂ)

noncomputable def proposition26ErrorProfileOne (D : ℕ) : ℕ → ℂ :=
  proposition26NormalizedGaussianProfile D (lemma111TentErrorOne D)
noncomputable def proposition26ErrorProfileTwo (D : ℕ) : ℕ → ℂ :=
  proposition26NormalizedGaussianProfile D (lemma111TentErrorTwo D)

lemma proposition26_normalized_gaussian_variation {D : ℕ} (hD : 1 < D)
    (e : ℝ → ℝ)
    (he : ∀ (q : ℕ), 0 < q → ∀ N : ℕ,
      lemma111SequenceVariation (fun i =>
        if ((q*(i+1):ℕ):ℝ) < proposition26GaussianCutoff D then e (q*(i+1):ℕ) else 0) N ≤
          16000 / lemma111Scale D) :
    Proposition26VariationBound (proposition26NormalizedGaussianProfile D e) 16000 := by
  refine ⟨by norm_num, ?_⟩
  intro q N hq
  have hA := lemma111_scale_pos hD
  let f : ℕ → ℝ := fun i =>
    if ((q*(i+1):ℕ):ℝ) < proposition26GaussianCutoff D then e (q*(i+1):ℕ) else 0
  have hv : lemma111SequenceVariation (fun i => lemma111Scale D * f i) (N-1) ≤ 16000 := by
    rw [lemma111_sequence_variation_mul, abs_of_pos hA]
    calc
      _ ≤ lemma111Scale D * (16000 / lemma111Scale D) :=
        mul_le_mul_of_nonneg_left (he q hq (N-1)) hA.le
      _ = _ := by field_simp [hA.ne']
  simpa only [lemma111SequenceVariation, f, proposition26NormalizedGaussianProfile,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, Nat.add_assoc] using hv

lemma proposition26_error_profile_one_variation {D : ℕ} (hD : 1 < D) :
    Proposition26VariationBound (proposition26ErrorProfileOne D) 16000 := by
  apply proposition26_normalized_gaussian_variation hD
  intro q hq N
  apply lemma111_tent_error_one_strict_variation hD
    (fun i => ((q*(i+1):ℕ):ℝ))
  · intro i
    exact_mod_cast Nat.mul_pos hq (Nat.succ_pos i)
  · intro i j hij
    dsimp
    exact_mod_cast Nat.mul_le_mul_left q (Nat.add_le_add_right hij 1)

lemma proposition26_error_profile_two_variation {D : ℕ} (hD : 1 < D) :
    Proposition26VariationBound (proposition26ErrorProfileTwo D) 16000 := by
  apply proposition26_normalized_gaussian_variation hD
  intro q hq N
  apply lemma111_tent_error_two_strict_variation hD
    (fun i => ((q*(i+1):ℕ):ℝ))
  · intro i
    exact_mod_cast Nat.mul_pos hq (Nat.succ_pos i)
  · intro i j hij
    dsimp
    exact_mod_cast Nat.mul_le_mul_left q (Nat.add_le_add_right hij 1)

lemma proposition26_normalized_gaussian_support {D : ℕ} (hL : 64 ≤ lemma23PaperL D)
    (e : ℝ → ℝ) (n : ℕ) (hn : lemma81Cutoff D ≤ (n:ℝ)) :
    proposition26NormalizedGaussianProfile D e n = 0 := by
  have hx : proposition26GaussianCutoff D ≤ (n:ℝ) :=
    (proposition26_P505_le_polynomial_cutoff hL).trans hn
  simp [proposition26NormalizedGaussianProfile, not_lt.mpr hx]

lemma proposition26_error_profile_one_support {D : ℕ} (hL : 64 ≤ lemma23PaperL D)
    (n : ℕ) (hn : lemma81Cutoff D ≤ (n:ℝ)) : proposition26ErrorProfileOne D n = 0 :=
  proposition26_normalized_gaussian_support hL _ n hn

lemma proposition26_error_profile_two_support {D : ℕ} (hL : 64 ≤ lemma23PaperL D)
    (n : ℕ) (hn : lemma81Cutoff D ≤ (n:ℝ)) : proposition26ErrorProfileTwo D n = 0 :=
  proposition26_normalized_gaussian_support hL _ n hn

lemma proposition26_error_profile_one_admissible {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 64 ≤ lemma23PaperL D) (v : ℝ) :
    Lemma81AdmissibleSequence D 16000
      (proposition26TwistedCoefficient χ v (proposition26ErrorProfileOne D)) :=
  proposition26_twisted_coefficient_admissible χ v
    (proposition26_error_profile_one_variation hD) (proposition26_error_profile_one_support hL)

lemma proposition26_error_profile_two_admissible {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 64 ≤ lemma23PaperL D) (v : ℝ) :
    Lemma81AdmissibleSequence D 16000
      (proposition26TwistedCoefficient χ v (proposition26ErrorProfileTwo D)) :=
  proposition26_twisted_coefficient_admissible χ v
    (proposition26_error_profile_two_variation hD) (proposition26_error_profile_two_support hL)

@[simp] lemma proposition26_error_profile_one_zero (D : ℕ) : proposition26ErrorProfileOne D 0 = 0 := by
  simp [proposition26ErrorProfileOne, proposition26NormalizedGaussianProfile]

@[simp] lemma proposition26_error_profile_two_zero (D : ℕ) : proposition26ErrorProfileTwo D 0 = 0 := by
  simp [proposition26ErrorProfileTwo, proposition26NormalizedGaussianProfile]


noncomputable def proposition26CutoffIndicator (X : ℝ) (n : ℕ) : ℂ :=
  ((if (n:ℝ) < X then 1 else 0 : ℝ) : ℂ)

lemma proposition26_cutoff_indicator_variation (X : ℝ) :
    Proposition26VariationBound (proposition26CutoffIndicator X) 1 := by
  refine ⟨by norm_num, ?_⟩
  intro q N hq
  have hv : ∀ M, lemma111SequenceVariation (fun _ : ℕ => (1:ℝ)) M ≤ 1 := by
    intro M
    simp [lemma111SequenceVariation]
  have hm : ∀ i j : ℕ, i ≤ j → ((q*(j+1):ℕ):ℝ) < X → ((q*(i+1):ℕ):ℝ) < X := by
    intro i j hij hj
    exact lt_of_le_of_lt (by exact_mod_cast Nat.mul_le_mul_left q (Nat.add_le_add_right hij 1)) hj
  have hh := lemma111_sequence_variation_cutoff hv
    (fun i => ((q*(i+1):ℕ):ℝ) < X) hm (N-1)
  simpa only [lemma111SequenceVariation, proposition26CutoffIndicator,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, Nat.add_assoc] using hh

lemma proposition26_cutoff_indicator_support {D : ℕ} {X : ℝ}
    (hcut : X ≤ lemma81Cutoff D) (n : ℕ) (hn : lemma81Cutoff D ≤ (n:ℝ)) :
    proposition26CutoffIndicator X n = 0 := by
  simp [proposition26CutoffIndicator, not_lt.mpr (hcut.trans hn)]

lemma proposition26_cutoff_indicator_admissible {D : ℕ} (χ : RealPrimitiveCharacter D)
    {X : ℝ} (hcut : X ≤ lemma81Cutoff D) (v : ℝ) :
    Lemma81AdmissibleSequence D 1 (proposition26TwistedCoefficient χ v (proposition26CutoffIndicator X)) :=
  proposition26_twisted_coefficient_admissible χ v
    (proposition26_cutoff_indicator_variation X) (proposition26_cutoff_indicator_support hcut)

end ZhangLS.Spec
