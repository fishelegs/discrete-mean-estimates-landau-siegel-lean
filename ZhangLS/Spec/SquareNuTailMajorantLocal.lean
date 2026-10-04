import ZhangLS.Spec.SquareNuTailMajorantLift
import ZhangLS.Spec.Lemma34TauProduct
import ZhangLS.Spec.Proposition71DivisorWeights

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Finset
open scoped Classical ArithmeticFunction.zeta

noncomputable def squareDivisor (k : ℕ) : ArithmeticFunction ℝ :=
  ((ArithmeticFunction.zeta ^ k : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)

@[simp] lemma squareDivisor_apply (k n : ℕ) :
    squareDivisor k n = (lemma34Tau k n : ℝ) := rfl

lemma squareDivisor_pow (k r : ℕ) : squareDivisor k ^ r = squareDivisor (k*r) := by
  induction r with
  | zero => simp [squareDivisor]
  | succ r ih =>
    rw [pow_succ, ih]
    simp [squareDivisor, Nat.mul_add, pow_add]

lemma squareDivisor_multiplicative (k : ℕ) :
    ArithmeticFunction.IsMultiplicative (squareDivisor k) :=
  (lemma34_tau_multiplicative k).natCast

lemma square_function_pow_nonneg (f : ArithmeticFunction ℝ) (hf : ∀ n, 0 ≤ f n)
    (k n : ℕ) : 0 ≤ (f^k) n := by
  induction k generalizing n with
  | zero => simp only [pow_zero, ArithmeticFunction.one_apply]; split_ifs <;> norm_num
  | succ k ih =>
    rw [pow_succ, ArithmeticFunction.mul_apply]
    exact sum_nonneg (fun ab _ => mul_nonneg (ih _) (hf _))

lemma square_function_pow_multiplicative (f : ArithmeticFunction ℝ)
    (hf : ArithmeticFunction.IsMultiplicative f) (k : ℕ) :
    ArithmeticFunction.IsMultiplicative (f^k) := by
  induction k with
  | zero => simpa using (ArithmeticFunction.isMultiplicative_one (R := ℝ))
  | succ k ih => rw [pow_succ]; exact ih.mul hf

lemma square_tau_mono (a b n : ℕ) (hab : a ≤ b) : lemma34Tau a n ≤ lemma34Tau b n := by
  by_cases hn : n=0
  · subst n; simp [lemma34Tau]
  · have hb : b = a+(b-a) := by omega
    rw [hb]
    unfold lemma34Tau
    rw [pow_add, ArithmeticFunction.mul_apply]
    have hm : (n,1) ∈ n.divisorsAntidiagonal := Nat.mem_divisorsAntidiagonal.mpr ⟨by simp, hn⟩
    have hs := single_le_sum (f := fun ab : ℕ×ℕ =>
      (ArithmeticFunction.zeta^a) ab.1 * (ArithmeticFunction.zeta^(b-a)) ab.2)
      (fun ab _ => Nat.zero_le _) hm
    simpa [(lemma34_tau_multiplicative (b-a)).map_one] using hs

lemma squareNu_prime_of_one {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (hp : p.Prime) (h : χ.evalNat p=1) (e : ℕ) :
    squareNu χ (p^e) = squareDivisor 2 (p^e) := by
  rw [squareNu_apply, lemma31NuReal, lemma31_actual_nu_prime_power_of_one χ hp h e,
    squareDivisor_apply]
  have ht := lemma34_tau_prime_power hp 1 e
  simpa [Nat.multichoose_two] using congrArg (fun x : ℕ => (x : ℝ)) ht.symm

lemma squareNu_prime_of_zero {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (hp : p.Prime) (h : χ.evalNat p=0) (e : ℕ) :
    squareNu χ (p^e) = squareDivisor 1 (p^e) := by
  rw [squareNu_apply, lemma31NuReal, lemma31_actual_nu_prime_power χ hp e, h]
  simp [zero_pow_eq, squareDivisor, hp.ne_zero]

lemma squareNu_prime_of_neg_one {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (hp : p.Prime) (h : χ.evalNat p = -1) (e : ℕ) :
    squareNu χ (p^e) = squareTau 1 (p^e) := by
  rw [squareNu_apply, lemma31NuReal, lemma31_actual_nu_prime_power χ hp e, h,
    neg_one_geom_sum, squareTau_one_prime hp]
  by_cases he : Even e <;> simp [Nat.even_add_one, he]

lemma squareNu_pow_prime_of_one {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (hp : p.Prime) (h : χ.evalNat p=1) (r e : ℕ) :
    (squareNu χ ^ r) (p^e) = squareDivisor (2*r) (p^e) := by
  rw [square_prime_pow_congr hp _ _ (squareNu_prime_of_one χ hp h), squareDivisor_pow]

lemma squareNu_pow_prime_of_zero {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (hp : p.Prime) (h : χ.evalNat p=0) (r e : ℕ) :
    (squareNu χ ^ r) (p^e) = squareDivisor r (p^e) := by
  rw [square_prime_pow_congr hp _ _ (squareNu_prime_of_zero χ hp h), squareDivisor_pow,
    one_mul]

lemma squareNu_pow_prime_of_neg_one {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (hp : p.Prime) (h : χ.evalNat p = -1) (r e : ℕ) :
    (squareNu χ ^ r) (p^e) = squareTau r (p^e) := by
  rw [square_prime_pow_congr hp _ _ (squareNu_prime_of_neg_one χ hp h), ← squareTau_eq_pow]

lemma squareNu_squareTau_prime_of_neg_one {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (hp : p.Prime) (h : χ.evalNat p = -1) (r K e : ℕ) :
    (squareNu χ ^ r * squareTau K) (p^e) = squareTau (r+K) (p^e) := by
  rw [square_prime_mul_congr hp _ _ _ _ (squareNu_pow_prime_of_neg_one χ hp h r)
    (fun _ => rfl), squareTau_mul]

lemma squareNu_pow_le_mul_squareTau {D : ℕ} (χ : RealPrimitiveCharacter D)
    (r K n : ℕ) :
    (squareNu χ^r) n ≤ (squareNu χ^r * squareTau K) n := by
  by_cases hn : n=0
  · subst n; simp
  · rw [ArithmeticFunction.mul_apply]
    have hm : (n,1) ∈ n.divisorsAntidiagonal := Nat.mem_divisorsAntidiagonal.mpr ⟨by simp, hn⟩
    have hs := single_le_sum (f := fun ab : ℕ×ℕ => (squareNu χ^r) ab.1*squareTau K ab.2)
      (fun ab _ => mul_nonneg (square_function_pow_nonneg _ (squareNu_nonneg χ) _ _)
        (squareTau_nonneg _ _)) hm
    simpa [(squareTau_multiplicative K).map_one] using hs

end ZhangLS.Spec
