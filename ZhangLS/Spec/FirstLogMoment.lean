import ZhangLS.Spec.Lemma171Target

/-! The actual first logarithmic moment, with the paper's strict cutoff. -/

set_option autoImplicit false
namespace ZhangLS.Spec
open Finset
open scoped Classical

noncomputable def lemma171FirstLogMoment {D : ℕ} (χ : RealPrimitiveCharacter D) : ℝ :=
  ∑ n ∈ Finset.Ico 1 (D ^ 4),
    lemma171Coefficient χ n * Real.log (n : ℝ) / (n : ℝ)

lemma lemma171_first_log_moment_nonneg {D : ℕ} (χ : RealPrimitiveCharacter D) :
    0 ≤ lemma171FirstLogMoment χ := by
  apply Finset.sum_nonneg
  intro n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ico.mp hn).1
  exact div_nonneg (mul_nonneg (lemma171_coefficient_nonneg χ n)
    (Real.log_nonneg hn1)) (Nat.cast_nonneg n)

lemma lemma171_first_log_moment_le {D : ℕ} (χ : RealPrimitiveCharacter D) :
    lemma171FirstLogMoment χ ≤ 4 * lemma23PaperL D * lemma171ShortHarmonicSum χ := by
  unfold lemma171FirstLogMoment lemma171ShortHarmonicSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hn1 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Ico.mp hn).1
  have hnD : (n : ℝ) ≤ (D : ℝ) ^ 4 := by
    exact_mod_cast (Finset.mem_Ico.mp hn).2.le
  have hlog : Real.log (n : ℝ) ≤ 4 * lemma23PaperL D := by
    calc
      _ ≤ Real.log ((D : ℝ) ^ 4) := Real.log_le_log hn1 hnD
      _ = _ := by rw [Real.log_pow]; rfl
  calc
    _ = (lemma171Coefficient χ n / (n : ℝ)) * Real.log (n : ℝ) := by ring
    _ ≤ (lemma171Coefficient χ n / (n : ℝ)) * (4 * lemma23PaperL D) :=
      mul_le_mul_of_nonneg_left hlog
        (div_nonneg (lemma171_coefficient_nonneg χ n) hn1.le)
    _ = _ := by ring

lemma lemma171_first_log_moment_endpoint {D : ℕ} (χ : RealPrimitiveCharacter D) :
    (∑ n ∈ Finset.Icc 1 (D ^ 4),
      lemma171Coefficient χ n * Real.log (n : ℝ) / (n : ℝ)) =
      lemma171FirstLogMoment χ + 4 * lemma23PaperL D * (D : ℝ) ^ (-4 : ℤ) := by
  have hD : 1 ≤ D ^ 4 := Nat.one_le_pow 4 D χ.modulus_pos
  have h := Finset.sum_Ico_add_eq_sum_Icc
    (f := fun n : ℕ => lemma171Coefficient χ n * Real.log (n : ℝ) / n) hD
  dsimp only at h
  rw [lemma171_coefficient_modulus_power, Nat.cast_pow, Real.log_pow] at h
  simpa [lemma171FirstLogMoment, lemma23PaperL, zpow_neg, zpow_ofNat,
    div_eq_mul_inv] using h.symm

lemma lemma171_log_weighted_short_sum {D : ℕ} (χ : RealPrimitiveCharacter D) (y : ℝ) :
    (∑ n ∈ Finset.Ico 1 (D ^ 4),
      lemma171Coefficient χ n / (n : ℝ) * (y - Real.log (n : ℝ))) =
      y * lemma171ShortHarmonicSum χ - lemma171FirstLogMoment χ := by
  unfold lemma171ShortHarmonicSum lemma171FirstLogMoment
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  ring

end ZhangLS.Spec
