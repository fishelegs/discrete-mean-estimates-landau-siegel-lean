import ZhangLS.Spec.Lemma31RealCoefficients
import ZhangLS.Spec.Lemma34DivisorFunction
import Mathlib.Algebra.GCDMonoid.Nat

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Finset
open scoped Classical ArithmeticFunction.zeta

noncomputable def squareNu {D : ℕ} (χ : RealPrimitiveCharacter D) : ArithmeticFunction ℝ :=
  ⟨lemma31NuReal χ, by simp [lemma31NuReal]⟩

@[simp] lemma squareNu_apply {D : ℕ} (χ : RealPrimitiveCharacter D) (n : ℕ) :
    squareNu χ n = lemma31NuReal χ n := rfl

lemma squareNu_nonneg {D : ℕ} (χ : RealPrimitiveCharacter D) (n : ℕ) :
    0 ≤ squareNu χ n := lemma31_nu_real_nonneg χ n

lemma squareNu_multiplicative {D : ℕ} (χ : RealPrimitiveCharacter D) :
    ArithmeticFunction.IsMultiplicative (squareNu χ) := by
  constructor
  · simp [squareNu, lemma31NuReal, lemma31_actual_nu_one]
  · intro m n hmn
    change (lemma23NuArithmeticFunction χ (m*n)).re = _
    rw [(lemma31_actual_nu_multiplicative χ).map_mul_of_coprime hmn]
    simp [Complex.mul_re, lemma31_nu_im_zero, squareNu, lemma31NuReal]

noncomputable def squareLift (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if IsSquare n then f (Nat.sqrt n) else 0, by simp⟩

lemma squareLift_apply (f : ArithmeticFunction ℝ) (n : ℕ) :
    squareLift f n = if IsSquare n then f (Nat.sqrt n) else 0 := rfl

@[simp] lemma squareLift_sq (f : ArithmeticFunction ℝ) (m : ℕ) :
    squareLift f (m^2) = f m := by
  simp [squareLift, show IsSquare (m^2) from ⟨m, by simp [pow_two]⟩]

lemma squareLift_nonneg (f : ArithmeticFunction ℝ) (hf : ∀ n, 0 ≤ f n) (n : ℕ) :
    0 ≤ squareLift f n := by
  simp only [squareLift_apply]
  split_ifs
  · exact hf _
  · exact le_rfl

lemma squareLift_eq_zero (f : ArithmeticFunction ℝ) {n : ℕ} (hn : ¬IsSquare n) :
    squareLift f n = 0 := by simp [squareLift_apply, hn]

lemma square_isSquare_mul_iff {m n : ℕ} (hmn : m.Coprime n) :
    IsSquare (m*n) ↔ IsSquare m ∧ IsSquare n := by
  constructor
  · rintro ⟨a, ha⟩
    have hg : IsUnit (GCDMonoid.gcd m n) := by
      change IsUnit (Nat.gcd m n)
      rw [hmn.gcd_eq_one]
      exact isUnit_one
    obtain ⟨b, hb⟩ := exists_eq_pow_of_mul_eq_pow hg (show m*n = a^2 by simpa [pow_two] using ha)
    obtain ⟨c, hc⟩ := exists_eq_pow_of_mul_eq_pow (by simpa [gcd_comm] using hg)
      (show n*m = a^2 by simpa [pow_two, mul_comm] using ha)
    exact ⟨⟨b, by simpa [pow_two] using hb⟩, ⟨c, by simpa [pow_two] using hc⟩⟩
  · rintro ⟨hm, hn⟩
    exact hm.mul hn

lemma squareLift_multiplicative (f : ArithmeticFunction ℝ)
    (hf : ArithmeticFunction.IsMultiplicative f) :
    ArithmeticFunction.IsMultiplicative (squareLift f) := by
  constructor
  · simpa [squareLift] using hf.map_one
  · intro m n hmn
    by_cases hm : IsSquare m
    · by_cases hn : IsSquare n
      · obtain ⟨a, rfl⟩ := hm
        obtain ⟨b, rfl⟩ := hn
        have hab : a.Coprime b := (show (a*a).Coprime (b*b) from hmn).coprime_mul_left.coprime_mul_left_right
        simpa only [← pow_two, ← mul_pow, squareLift_sq] using hf.map_mul_of_coprime hab
      · simp [squareLift_apply, hn, square_isSquare_mul_iff hmn]
    · simp [squareLift_apply, hm, square_isSquare_mul_iff hmn]

noncomputable def squareTau (K : ℕ) : ArithmeticFunction ℝ :=
  squareLift ((ArithmeticFunction.zeta ^ K : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)

lemma squareTau_apply (K n : ℕ) :
    squareTau K n = if IsSquare n then (lemma34Tau K (Nat.sqrt n) : ℝ) else 0 := rfl

@[simp] lemma squareTau_sq (K m : ℕ) :
    squareTau K (m^2) = (lemma34Tau K m : ℝ) := squareLift_sq _ m

lemma squareTau_nonneg (K n : ℕ) : 0 ≤ squareTau K n := by
  apply squareLift_nonneg
  intro n
  exact Nat.cast_nonneg _

lemma squareTau_eq_zero (K : ℕ) {n : ℕ} (hn : ¬IsSquare n) : squareTau K n = 0 :=
  squareLift_eq_zero _ hn

lemma squareTau_multiplicative (K : ℕ) :
    ArithmeticFunction.IsMultiplicative (squareTau K) :=
  squareLift_multiplicative _ (lemma34_tau_multiplicative K).natCast

@[simp] lemma squareLift_one : squareLift (1 : ArithmeticFunction ℝ) = 1 := by
  ext n
  by_cases hn : IsSquare n
  · obtain ⟨m, rfl⟩ := hn
    simp [← pow_two, ArithmeticFunction.one_apply, Nat.pow_eq_one]
  · have hn1 : n ≠ 1 := by intro hn1; subst n; exact hn (by simp)
    simp [squareLift_eq_zero _ hn, ArithmeticFunction.one_apply, hn1]

@[simp] lemma squareTau_zero_order : squareTau 0 = 1 := by
  unfold squareTau
  simpa using squareLift_one

end ZhangLS.Spec
