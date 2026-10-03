import ZhangLS.Spec.Lemma162CoefficientReassembly
import ZhangLS.Spec.Lemma162NuChiLocalH3

/-! Finite local divisor-kernel algebra, with the true degree-zero constant. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def lemma162RawKernel (F00 F01 F10 F11 lam b v : ℂ) (i j : ℕ) : ℂ :=
  (if i=0 then 1 else lam)*b^i*v^j *
    (if i=0 then if j=0 then F00 else F01 else if j=0 then F10 else F11)

noncomputable def lemma162RawCoefficient (F00 F01 F10 F11 lam b v : ℂ) (n : ℕ) : ℂ :=
  (if n=0 then F00-lam*F10-F01+lam*F11 else 0) +
    (lam*F10-lam*F11)*b^n + (F01-lam*F11)*v^n +
      lam*F11*lemma83LocalH2 b v n

lemma lemma162_raw_kernel_boundary_decomposition (F00 F01 F10 F11 lam b v : ℂ) (i j : ℕ) :
    lemma162RawKernel F00 F01 F10 F11 lam b v i j =
      lam*F11*(b^i*v^j) +
      (if j=0 then (lam*F10-lam*F11)*b^i else 0) +
      (if i=0 then (F01-lam*F11)*v^j else 0) +
      (if i=0 ∧ j=0 then F00-lam*F10-F01+lam*F11 else 0) := by
  by_cases hi : i=0 <;> by_cases hj : j=0 <;>
    simp [lemma162RawKernel,hi,hj] <;> ring

lemma lemma162_antidiagonal_snd_boundary (f : ℕ → ℂ) (n : ℕ) :
    (∑ ij ∈ antidiagonal n, if ij.2=0 then f ij.1 else 0) = f n := by
  rw [sum_eq_single (n,0)]
  · simp
  · intro ij hij hne
    by_cases hj : ij.2=0
    · have hi : ij.1=n := by have h := mem_antidiagonal.mp hij; omega
      exact False.elim (hne (Prod.ext hi hj))
    · simp [hj]
  · simp

lemma lemma162_antidiagonal_fst_boundary (f : ℕ → ℂ) (n : ℕ) :
    (∑ ij ∈ antidiagonal n, if ij.1=0 then f ij.2 else 0) = f n := by
  rw [sum_eq_single (0,n)]
  · simp
  · intro ij hij hne
    by_cases hi : ij.1=0
    · have hj : ij.2=n := by have h := mem_antidiagonal.mp hij; omega
      exact False.elim (hne (Prod.ext hi hj))
    · simp [hi]
  · simp

lemma lemma162_antidiagonal_corner (C : ℂ) (n : ℕ) :
    (∑ ij ∈ antidiagonal n, if ij.1=0 ∧ ij.2=0 then C else 0) = if n=0 then C else 0 := by
  by_cases hn : n=0
  · subst n; simp
  · rw [if_neg hn]
    apply sum_eq_zero
    intro ij hij
    have hnot : ¬(ij.1=0 ∧ ij.2=0) := by
      rintro ⟨h1,h2⟩
      have h := mem_antidiagonal.mp hij
      rw [h1,h2,zero_add] at h
      exact hn h.symm
    rw [if_neg hnot]

lemma lemma162_raw_kernel_sum (F00 F01 F10 F11 lam b v : ℂ) (n : ℕ) :
    (∑ ij ∈ antidiagonal n, lemma162RawKernel F00 F01 F10 F11 lam b v ij.1 ij.2) =
      lemma162RawCoefficient F00 F01 F10 F11 lam b v n := by
  simp_rw [lemma162_raw_kernel_boundary_decomposition]
  simp only [sum_add_distrib]
  rw [lemma162_antidiagonal_snd_boundary (fun i => (lam*F10-lam*F11)*b^i) n,
    lemma162_antidiagonal_fst_boundary (fun j => (F01-lam*F11)*v^j) n,
    lemma162_antidiagonal_corner]
  rw [← mul_sum]
  unfold lemma162RawCoefficient lemma83LocalH2 lemma83AddConvolution
  ring

@[simp] lemma lemma162_raw_coefficient_zero (F00 F01 F10 F11 lam b v : ℂ) :
    lemma162RawCoefficient F00 F01 F10 F11 lam b v 0 = F00 := by
  simp [lemma162RawCoefficient]
  ring

lemma lemma162_divisor_kernel_prime_power (H : ℕ → ℕ → ℂ)
    {p : ℕ} (hp : p.Prime) (n : ℕ) :
    lemma152DivisorKernelSum H (p^n) =
      ∑ ij ∈ antidiagonal n, H (p^ij.1) (p^ij.2) := by
  change (∑ dl ∈ (p^n).divisorsAntidiagonal, H dl.1 dl.2) = _
  rw [Nat.sum_divisorsAntidiagonal H,Nat.sum_divisors_prime_pow hp,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => H (p^i) (p^j))]
  apply sum_congr rfl
  intro k hk
  rw [Nat.pow_div (show k≤n by have := mem_range.mp hk; omega) hp.pos]

lemma lemma162_lambda_prime_power {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hp : p.Prime) (i : ℕ) :
    lemma161Lambda χ β (p^i) = if i=0 then 1 else lemma161LambdaFactor χ β p 1 := by
  cases i with
  | zero => simp
  | succ i => simp [lemma161Lambda,Nat.primeFactors_pow,hp.primeFactors]

lemma lemma162_nat_power_cpow (p i : ℕ) (γ : ℂ) :
    ((p^i:ℕ):ℂ)^γ = ((p:ℂ)^γ)^i := by
  rw [Nat.cast_pow,← Complex.natCast_cpow_natCast_mul p i γ,Complex.cpow_nat_mul]

lemma lemma162_general_m_prime_power_flags {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (q : Nat.Primes) (s : ℂ) (i j : ℕ) :
    lemma162GeneralMPrimeFactor χ β (q.val^i) (q.val^j) q s =
      if i=0 then
        if j=0 then lemma161PrimeFactor χ β q s else lemma162GeneralMPrimeFactor χ β 1 q.val q s
      else if j=0 then lemma162GeneralMPrimeFactor χ β q.val 1 q s
        else lemma162GeneralMPrimeFactor χ β q.val q.val q s := by
  by_cases hi : i=0 <;> by_cases hj : j=0
  · subst i; subst j; simp
  · subst i
    have hd := dvd_pow_self q.val hj
    simp [lemma162GeneralMPrimeFactor,hj,q.property.not_dvd_one,hd]
  · subst j
    have hd := dvd_pow_self q.val hi
    simp [lemma162GeneralMPrimeFactor,hi,q.property.not_dvd_one,hd]
  · have hdi := dvd_pow_self q.val hi
    have hdj := dvd_pow_self q.val hj
    simp [lemma162GeneralMPrimeFactor,hi,hj,hdi,hdj]

end ZhangLS.Spec
