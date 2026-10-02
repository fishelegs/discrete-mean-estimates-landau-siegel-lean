import ZhangLS.Spec.Lemma153LocalCorrection
import ZhangLS.Spec.Lemma153Ramified
/-! Arithmetic bridge from the genuine divisor-sum varpi to the local kernel.
The three ratio premises are exactly the three cases to be supplied by (15.18),
not estimates or analytic assumptions on the desired U function. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma153_lambda_prime_power {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (hp : p.Prime) (n : ℕ) (hn : n ≠ 0) :
    lemma152Lambda χ β (p^n) = lemma152LambdaFactor χ β p 1 := by
  simp [lemma152Lambda,Nat.primeFactors_pow _ hn,hp.primeFactors]

lemma lemma153_cpow_prime_power (p n : ℕ) (γ : ℂ) :
    ((p^n:ℕ):ℂ)^γ = ((p:ℂ)^γ)^n := by
  rw [Nat.cast_pow,← Complex.natCast_cpow_natCast_mul,Complex.cpow_nat_mul]

lemma lemma153_character_prime_power {D : ℕ} (χ : RealPrimitiveCharacter D) (p n : ℕ) :
    χ.evalNat (p^n) = χ.evalNat p^n := by
  simp [RealPrimitiveCharacter.evalNat]

lemma lemma153_quadratic_power_cancel (v : ℂ) (hv : v^2 = 1) (n k : ℕ) (hk : k ≤ n) :
    v^n*v^(n-k) = v^k := by
  have he : v^n = v^k*v^(n-k) := by rw [← pow_add,Nat.add_sub_of_le hk]
  rw [he]
  have hs : v^(n-k)*v^(n-k) = 1 := by
    rw [← pow_two,← pow_mul,mul_comm (n-k) 2,pow_mul,hv,one_pow]
  rw [mul_assoc,hs,mul_one]

lemma lemma153_h2_one_sum (t : ℂ) (n : ℕ) :
    lemma83LocalH2 1 t n = ∑ k ∈ range (n+1), t^k := by
  unfold lemma83LocalH2 lemma83AddConvolution
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => (1:ℂ)^i*t^j)]
  simp only [one_pow,one_mul]
  simpa using sum_range_reflect (fun k => t^k) (n+1)

lemma lemma153_local_kernel_finite_sum (B C E F lam t : ℂ) (n : ℕ) (hn : 0 < n) :
    (∑ k ∈ range (n+1), if k = 0 then C/B else
      if k = n then lam*E/B*t^n else lam*F/B*t^k) =
        lemma153LocalChiVarpi B C E F lam t n := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [sum_range_succ]
  have hs : (∑ k ∈ range (r+1), if k = 0 then C/B else
      if k = r+1 then lam*E/B*t^(r+1) else lam*F/B*t^k) =
        lam*F/B*(∑ k ∈ range r, t^(k+1)) + C/B := by
    rw [sum_range_succ']
    simp only [show ¬(0:ℕ)=r+1 by omega,if_true]
    rw [mul_sum]
    congr 1
    apply sum_congr rfl
    intro k hk
    have hkne : k+1 ≠ r+1 := by have := mem_range.mp hk; omega
    have hkr : k ≠ r := by have := mem_range.mp hk; omega
    simp [hkr]
  rw [hs]
  simp only [Nat.succ_ne_zero,if_false,if_true]
  unfold lemma153LocalChiVarpi
  rw [if_neg (by omega),lemma153_h2_one_sum,sum_range_succ,sum_range_succ']
  simp only [pow_zero,pow_succ]
  ring

lemma lemma153_chi_varpi_prime_power {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (γ : ℂ) (M : ℕ → ℕ → ℂ → ℂ)
    (hp : p.Prime) (hv : χ.evalNat p^2 = 1)
    (hM : M 1 1 (1-γ) ≠ 0) (B C E F : ℂ)
    (hC : ∀ n : ℕ, 0 < n → M 1 (p^n) (1-γ)/M 1 1 (1-γ) = C/B)
    (hE : ∀ n : ℕ, 0 < n → M (p^n) 1 (1-γ)/M 1 1 (1-γ) = E/B)
    (hF : ∀ k l : ℕ, 0 < k → 0 < l →
      M (p^k) (p^l) (1-γ)/M 1 1 (1-γ) = F/B) (n : ℕ) :
    χ.evalNat (p^n)*lemma153Varpi χ β γ M (p^n) =
      lemma153LocalChiVarpi B C E F (lemma152LambdaFactor χ β p 1)
        (χ.evalNat p*(p:ℂ)^γ) n := by
  by_cases hn : n = 0
  · subst n
    simp [lemma153_varpi_one χ β γ M hM,lemma153LocalChiVarpi,RealPrimitiveCharacter.evalNat]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  rw [← lemma153_local_kernel_finite_sum B C E F
    (lemma152LambdaFactor χ β p 1) (χ.evalNat p*(p:ℂ)^γ) n hnpos]
  unfold lemma153Varpi
  rw [Nat.sum_divisorsAntidiagonal (fun d l =>
    lemma152Lambda χ β d*(d:ℂ)^γ*χ.evalNat l*(M d l (1-γ)/M 1 1 (1-γ))),
    Nat.sum_divisors_prime_pow hp,mul_sum,lemma153_character_prime_power]
  apply sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by have := mem_range.mp hk; omega
  rw [Nat.pow_div hkn hp.pos,lemma153_cpow_prime_power,lemma153_character_prime_power]
  by_cases hk0 : k = 0
  · subst k
    simp only [pow_zero,lemma153_lambda_one,Complex.one_cpow,one_mul,Nat.sub_zero,if_true]
    rw [hC n hnpos]
    have hh := lemma153_quadratic_power_cancel (χ.evalNat p) hv n 0 (Nat.zero_le n)
    simp only [Nat.sub_zero,pow_zero] at hh
    calc
      _ = (χ.evalNat p^n*χ.evalNat p^n)*(C/B) := by ring
      _ = C/B := by rw [hh,one_mul]
  · rw [if_neg hk0,lemma153_lambda_prime_power χ β hp k hk0]
    by_cases hkn' : k = n
    · subst k
      simp only [Nat.sub_self,pow_zero]
      rw [hE n hnpos]
      simp only [ite_true,mul_pow]
      ring
    · rw [if_neg hkn',hF k (n-k) (Nat.pos_of_ne_zero hk0) (by omega),mul_pow]
      have hh := lemma153_quadratic_power_cancel (χ.evalNat p) hv n k hkn
      calc
        _ = (χ.evalNat p^n*χ.evalNat p^(n-k))*
          (lemma152LambdaFactor χ β p 1*((p:ℂ)^γ)^k*(F/B)) := by ring
        _ = _ := by rw [hh]; ring

lemma lemma153_actual_prime_power_extraction {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (γ : ℂ) (M : ℕ → ℕ → ℂ → ℂ)
    (hp : p.Prime) (hv : χ.evalNat p^2 = 1)
    (hM : M 1 1 (1-γ) ≠ 0) (B C E F : ℂ) (hB : B ≠ 0)
    (hcompat : B = C+lemma152LambdaFactor χ β p 1*E-lemma152LambdaFactor χ β p 1*F)
    (hC : ∀ n : ℕ, 0 < n → M 1 (p^n) (1-γ)/M 1 1 (1-γ) = C/B)
    (hE : ∀ n : ℕ, 0 < n → M (p^n) 1 (1-γ)/M 1 1 (1-γ) = E/B)
    (hF : ∀ k l : ℕ, 0 < k → 0 < l →
      M (p^k) (p^l) (1-γ)/M 1 1 (1-γ) = F/B)
    (z : ℂ) (hz : ‖z‖ < 1) (htz : ‖χ.evalNat p*(p:ℂ)^γ*z‖ < 1) :
    (1-z)^2*(1-χ.evalNat p*(p:ℂ)^γ*z)^2 *
      (∑' n : ℕ, lemma153Coefficient χ β γ M (p^n)*z^n) =
        lemma153ShiftedLocalCorrection B C E F (lemma152LambdaFactor χ β p 1)
          (χ.evalNat p*(p:ℂ)^γ) z := by
  convert lemma153_shifted_local_extraction B C E F (lemma152LambdaFactor χ β p 1)
    (χ.evalNat p*(p:ℂ)^γ) z hB hcompat hz htz using 1
  congr 1
  apply tsum_congr
  intro n
  rw [lemma153Coefficient,lemma153_tau_two_prime_power hp]
  have hh := lemma153_chi_varpi_prime_power χ β γ M hp hv hM B C E F hC hE hF n
  push_cast
  rw [show χ.evalNat (p^n)*((n:ℂ)+1)*lemma153Varpi χ β γ M (p^n) =
    ((n:ℂ)+1)*(χ.evalNat (p^n)*lemma153Varpi χ β γ M (p^n)) by ring,hh]

end ZhangLS.Spec
