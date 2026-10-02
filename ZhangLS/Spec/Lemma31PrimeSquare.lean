import ZhangLS.Spec.Lemma31OrderedArithmetic
set_option autoImplicit false
namespace ZhangLS.Spec
open scoped ComplexOrder
set_option maxHeartbeats 2000000

lemma lemma31_linear_convolution_sum_bound (e : ℕ) :
    (e+1)^2 ≤ ∑ j ∈ Finset.range (e+1), (j+1)*(e-j+1) := by
  calc
    _ = ∑ j ∈ Finset.range (e+1), (e+1) := by simp [pow_two]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j hj
      have hje : j ≤ e := by have := Finset.mem_range.mp hj; omega
      have hsum := Nat.sub_add_cancel hje
      nlinarith

lemma lemma31_actual_nu_convolution_prime_power {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (hp : p.Prime) (k : ℕ) :
    (lemma23NuArithmeticFunction χ * lemma23NuArithmeticFunction χ) (p^k) =
      ∑ j ∈ Finset.range (k+1), lemma23NuArithmeticFunction χ (p^j) *
        lemma23NuArithmeticFunction χ (p^(k-j)) := by
  rw [ArithmeticFunction.mul_apply]
  rw [Nat.sum_divisorsAntidiagonal (fun a b =>
    lemma23NuArithmeticFunction χ a * lemma23NuArithmeticFunction χ b),
    Nat.sum_divisors_prime_pow hp]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Nat.pow_div (show j ≤ k by have := Finset.mem_range.mp hj; omega) hp.pos]

lemma lemma31_actual_nu_prime_power_of_one {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (hp : p.Prime) (h : χ.evalNat p = 1) (k : ℕ) :
    lemma23NuArithmeticFunction χ (p^k) = (k+1 : ℕ) := by
  rw [lemma31_actual_nu_prime_power χ hp k,h]
  simp

lemma lemma31_actual_nu_prime_power_idempotent {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (hp : p.Prime) (h : χ.evalNat p = 0 ∨ χ.evalNat p = -1) (k : ℕ) :
    lemma23NuArithmeticFunction χ (p^k)^2 = lemma23NuArithmeticFunction χ (p^k) := by
  rcases h with h | h
  · rw [lemma31_actual_nu_prime_power χ hp k,h]
    simp [zero_pow_eq]
  · rw [lemma31_actual_nu_prime_power χ hp k,h,neg_one_geom_sum]
    split_ifs <;> simp

lemma lemma31_actual_nu_prime_square_le_of_one {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (hp : p.Prime) (h : χ.evalNat p = 1) (k : ℕ) :
    lemma23NuArithmeticFunction χ (p^k)^2 ≤
      (lemma23NuArithmeticFunction χ * lemma23NuArithmeticFunction χ) (p^k) := by
  rw [lemma31_actual_nu_prime_power_of_one χ hp h k,
    lemma31_actual_nu_convolution_prime_power χ hp k]
  simp_rw [lemma31_actual_nu_prime_power_of_one χ hp h]
  exact_mod_cast lemma31_linear_convolution_sum_bound k

lemma lemma31_actual_nu_prime_square_le {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (hp : p.Prime) (k : ℕ) :
    lemma23NuArithmeticFunction χ (p^k)^2 ≤
      (lemma23NuArithmeticFunction χ * lemma23NuArithmeticFunction χ) (p^k) := by
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr χ.quadratic (p : ZMod D) with h | h | h
  · have hh : χ.evalNat p = 0 := by simpa only [RealPrimitiveCharacter.evalNat] using h
    rw [lemma31_actual_nu_prime_power_idempotent χ hp (Or.inl hh) k]
    exact lemma31_actual_nu_le_convolution_square χ (p^k)
  · exact lemma31_actual_nu_prime_square_le_of_one χ hp
      (by simpa only [RealPrimitiveCharacter.evalNat] using h) k
  · have hh : χ.evalNat p = -1 := by simpa only [RealPrimitiveCharacter.evalNat] using h
    rw [lemma31_actual_nu_prime_power_idempotent χ hp (Or.inr hh) k]
    exact lemma31_actual_nu_le_convolution_square χ (p^k)

end ZhangLS.Spec
