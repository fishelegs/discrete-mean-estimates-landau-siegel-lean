import ZhangLS.Spec.SquareNuTailMajorantDefs

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Finset
open scoped Classical ArithmeticFunction.zeta

lemma squareLift_ne_zero_isSquare (f : ArithmeticFunction ℝ) {n : ℕ}
    (hn : squareLift f n ≠ 0) : IsSquare n := by
  by_contra h
  exact hn (squareLift_eq_zero f h)

lemma squareLift_mul (f g : ArithmeticFunction ℝ) :
    squareLift (f*g) = squareLift f * squareLift g := by
  ext n
  by_cases hn : IsSquare n
  · obtain ⟨m, rfl⟩ := hn
    rw [← pow_two, squareLift_sq, ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
    apply sum_bij_ne_zero (fun ab _ _ => (ab.1^2, ab.2^2))
    · intro ab hab hab0
      rcases Nat.mem_divisorsAntidiagonal.mp hab with ⟨hm, hm0⟩
      apply Nat.mem_divisorsAntidiagonal.mpr
      exact ⟨by simpa only [← mul_pow] using congrArg (fun x : ℕ => x^2) hm,
        pow_ne_zero _ hm0⟩
    · intro ab hab hab0 cd hcd hcd0 he
      apply Prod.ext
      · exact Nat.pow_left_injective (by norm_num : 2 ≠ 0) (congrArg Prod.fst he)
      · exact Nat.pow_left_injective (by norm_num : 2 ≠ 0) (congrArg Prod.snd he)
    · intro ab hab hab0
      have ha := squareLift_ne_zero_isSquare f (mul_ne_zero_iff.mp hab0).1
      have hb := squareLift_ne_zero_isSquare g (mul_ne_zero_iff.mp hab0).2
      obtain ⟨a, ha⟩ := ha
      obtain ⟨b, hb⟩ := hb
      have ha' : ab.1 = a^2 := by simpa [pow_two] using ha
      have hb' : ab.2 = b^2 := by simpa [pow_two] using hb
      have hab' := Nat.mem_divisorsAntidiagonal.mp hab
      have hm : a*b = m := Nat.pow_left_injective (by norm_num : 2 ≠ 0) (by
        simpa only [ha', hb', ← mul_pow] using hab'.1)
      refine ⟨(a,b), Nat.mem_divisorsAntidiagonal.mpr ⟨hm, ?_⟩, ?_, ?_⟩
      · exact fun hm0 => hab'.2 (by simp [hm0])
      · simpa [ha', hb'] using hab0
      · exact Prod.ext ha'.symm hb'.symm
    · intro ab hab hab0
      simp
  · rw [squareLift_eq_zero _ hn, ArithmeticFunction.mul_apply]
    symm
    apply sum_eq_zero
    intro ab hab
    by_contra hab0
    have ha := squareLift_ne_zero_isSquare f (mul_ne_zero_iff.mp hab0).1
    have hb := squareLift_ne_zero_isSquare g (mul_ne_zero_iff.mp hab0).2
    exact hn ((Nat.mem_divisorsAntidiagonal.mp hab).1 ▸ ha.mul hb)

lemma squareLift_pow (f : ArithmeticFunction ℝ) (k : ℕ) :
    squareLift (f^k) = squareLift f ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, squareLift_mul, ih, pow_succ]

lemma squareTau_mul (a b : ℕ) : squareTau a * squareTau b = squareTau (a+b) := by
  unfold squareTau
  rw [← squareLift_mul, pow_add]
  congr 1
  simp

lemma squareTau_eq_pow (k : ℕ) : squareTau k = squareTau 1 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [← squareTau_mul, ih, pow_succ]

lemma square_prime_mul_apply {p : ℕ} (hp : p.Prime)
    (f g : ArithmeticFunction ℝ) (e : ℕ) :
    (f*g) (p^e) = ∑ j ∈ range (e+1), f (p^j)*g (p^(e-j)) := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => f a*g b),
    Nat.sum_divisors_prime_pow hp]
  apply sum_congr rfl
  intro j hj
  rw [Nat.pow_div (by have := mem_range.mp hj; omega) hp.pos]

lemma square_prime_mul_congr {p : ℕ} (hp : p.Prime)
    (f g f' g' : ArithmeticFunction ℝ)
    (hf : ∀ e, f (p^e) = f' (p^e)) (hg : ∀ e, g (p^e) = g' (p^e)) (e : ℕ) :
    (f*g) (p^e) = (f'*g') (p^e) := by
  rw [square_prime_mul_apply hp, square_prime_mul_apply hp]
  simp_rw [hf, hg]

lemma square_prime_pow_congr {p : ℕ} (hp : p.Prime)
    (f g : ArithmeticFunction ℝ) (h : ∀ e, f (p^e)=g (p^e)) (r e : ℕ) :
    (f^r) (p^e) = (g^r) (p^e) := by
  induction r generalizing e with
  | zero => simp
  | succ r ih =>
    simp only [pow_succ]
    exact square_prime_mul_congr hp _ _ _ _ ih h e

lemma square_prime_isSquare_iff {p : ℕ} (hp : p.Prime) (e : ℕ) :
    IsSquare (p^e) ↔ Even e := by
  constructor
  · rintro ⟨m, hm⟩
    have h := congrArg (fun n : ℕ => n.factorization p) hm
    change (p^e).factorization p = (m*m).factorization p at h
    rw [← pow_two, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at h
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      hp.factorization_self, mul_one] at h
    exact ⟨m.factorization p, by omega⟩
  · rintro ⟨a, rfl⟩
    exact ⟨p^a, by rw [pow_add]⟩

lemma squareTau_one_prime {p : ℕ} (hp : p.Prime) (e : ℕ) :
    squareTau 1 (p^e) = if Even e then 1 else 0 := by
  by_cases he : Even e
  · obtain ⟨a, ha⟩ := he
    rw [ha, show a+a = a*2 by omega, pow_mul, squareTau_sq]
    simp [lemma34Tau, hp.ne_zero]
  · simp [squareTau_apply, square_prime_isSquare_iff hp, he]

end ZhangLS.Spec
