import ZhangLS.Spec.Lemma152DivisorKernel
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.ArithmeticFunction.Zeta

/-!
Verified generic helper for the actual exceptional-prime reassembly.

The exceptional prime has an arbitrary degree-zero coefficient. The lemmas
below never require that coefficient to be one or nonzero. The arithmetic
input is a bivariate kernel splitting across a prime-power part and a
prime-coprime part; no Euler/Dirichlet identity is assumed.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Nat Complex
open scoped Classical
set_option maxHeartbeats 1500000

/-- Localized version of `lemma152_divisor_kernel_multiplicative`. Only
splitting for this one coprime pair is needed; neither auxiliary kernel has
to have value one at (1,1). -/
lemma lemma162_divisor_kernel_coprime_split (H A B : ℕ → ℕ → ℂ)
    {m n : ℕ} (cop : m.Coprime n)
    (hsplit : ∀ a₁ a₂ b₁ b₂ : ℕ, a₁*a₂=m → b₁*b₂=n →
      H (a₁*b₁) (a₂*b₂) = A a₁ a₂ * B b₁ b₂) :
    lemma152DivisorKernelSum H (m*n) =
      lemma152DivisorKernelSum A m * lemma152DivisorKernelSum B n := by
  simp only [lemma152DivisorKernelSum,ArithmeticFunction.coe_mk]
  rw [sum_mul_sum, ← sum_product']
  symm
  apply sum_nbij fun ((i, j), k, l) ↦ (i * k, j * l)
  · rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ h
    simp only [mem_divisorsAntidiagonal, Ne, mem_product] at h
    rcases h with ⟨⟨rfl, ha⟩, ⟨rfl, hb⟩⟩
    simp only [mem_divisorsAntidiagonal, _root_.mul_eq_zero, Ne]
    constructor
    · ring
    rw [_root_.mul_eq_zero] at *
    exact not_or_intro ha hb
  · simp only [Set.InjOn, mem_coe, mem_divisorsAntidiagonal, mem_product, Prod.mk_inj]
    rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ ⟨⟨rfl, ha⟩, ⟨rfl, hb⟩⟩ ⟨⟨c1, c2⟩, ⟨d1, d2⟩⟩ hcd h
    ext
    · trans Nat.gcd (a1 * a2) (a1 * b1)
      · rw [Nat.gcd_mul_left, cop.coprime_mul_left.coprime_mul_right_right.gcd_eq_one, mul_one]
      · rw [← hcd.1.1, ← hcd.2.1] at cop
        rw [← hcd.1.1, h.1, Nat.gcd_mul_left, cop.coprime_mul_left.coprime_mul_right_right.gcd_eq_one,
          mul_one]
    · trans Nat.gcd (a1 * a2) (a2 * b2)
      · rw [mul_comm, Nat.gcd_mul_left, cop.coprime_mul_right.coprime_mul_left_right.gcd_eq_one,
          mul_one]
      · rw [← hcd.1.1, ← hcd.2.1] at cop
        rw [← hcd.1.1, h.2, mul_comm, Nat.gcd_mul_left,
          cop.coprime_mul_right.coprime_mul_left_right.gcd_eq_one, mul_one]
    · trans Nat.gcd (b1 * b2) (a1 * b1)
      · rw [mul_comm, Nat.gcd_mul_right, cop.coprime_mul_right.coprime_mul_left_right.symm.gcd_eq_one,
          one_mul]
      · rw [← hcd.1.1, ← hcd.2.1] at cop
        rw [← hcd.2.1, h.1, mul_comm c1 d1, Nat.gcd_mul_left,
          cop.coprime_mul_right.coprime_mul_left_right.symm.gcd_eq_one, mul_one]
    · trans Nat.gcd (b1 * b2) (a2 * b2)
      · rw [Nat.gcd_mul_right, cop.coprime_mul_left.coprime_mul_right_right.symm.gcd_eq_one, one_mul]
      · rw [← hcd.1.1, ← hcd.2.1] at cop
        rw [← hcd.2.1, h.2, Nat.gcd_mul_right,
          cop.coprime_mul_left.coprime_mul_right_right.symm.gcd_eq_one, one_mul]
  · simp only [Set.SurjOn, Set.subset_def, mem_coe, mem_divisorsAntidiagonal, mem_product,
      Set.mem_image]
    rintro ⟨b1, b2⟩ h
    use ((b1.gcd m, b2.gcd m), (b1.gcd n, b2.gcd n))
    rw [← cop.gcd_mul _, ← cop.gcd_mul _, ← h.1, gcd_mul_gcd_of_coprime_of_mul_eq_mul cop h.1,
      gcd_mul_gcd_of_coprime_of_mul_eq_mul cop.symm _]
    · rw [Ne, _root_.mul_eq_zero, not_or] at h
      simp [h.2.1, h.2.2]
    rw [mul_comm n m, h.1]
  · simp only [mem_divisorsAntidiagonal, mem_product]
    rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ ⟨⟨rfl, ha⟩, ⟨rfl, hb⟩⟩
    exact (hsplit a1 a2 b1 b2 rfl rfl).symm


/-- Keep only powers of one designated prime, including its zeroth power. -/
noncomputable def lemma162PrimePowerPart (p : ℕ) (f : ArithmeticFunction ℂ) :
    ArithmeticFunction ℂ :=
  ⟨fun n => if ∃ r : ℕ, n=p^r then f n else 0,by dsimp; split_ifs <;> simp⟩

/-- Keep only integers coprime to one designated prime. -/
noncomputable def lemma162CoprimePart (p : ℕ) (f : ArithmeticFunction ℂ) :
    ArithmeticFunction ℂ :=
  ⟨fun n => if p.Coprime n then f n else 0,by dsimp; split_ifs <;> simp⟩

lemma lemma162_prime_power_part_apply (p r : ℕ) (f : ArithmeticFunction ℂ) :
    lemma162PrimePowerPart p f (p^r) = f (p^r) := by
  simp [lemma162PrimePowerPart,show ∃ k : ℕ, p^r=p^k from ⟨r,rfl⟩]

lemma lemma162_coprime_part_apply (p n : ℕ) (f : ArithmeticFunction ℂ)
    (hn : p.Coprime n) : lemma162CoprimePart p f n = f n := by
  simp [lemma162CoprimePart,hn]

/-- A prime-power/prime-coprime factorization is unique. No exponent
calculation or choice of p-adic valuation is needed by callers. -/
lemma lemma162_prime_power_coprime_unique {p : ℕ} (hp : p.Prime)
    {r k m n : ℕ} (hm : p.Coprime m) (hn : p.Coprime n)
    (he : p^k*n=p^r*m) : p^k=p^r ∧ n=m := by
  have hm0 : m ≠ 0 := by
    intro hz
    subst m
    have hh : p=1 := by simpa using hm
    exact hp.ne_one hh
  have hm' : ¬p ∣ m := hp.coprime_iff_not_dvd.mp hm
  have hn' : ¬p ∣ n := hp.coprime_iff_not_dvd.mp hn
  have hec := congrArg (fun a : ℕ => a / p^(a.factorization p)) he
  dsimp only at hec
  rw [Nat.ordCompl_pow_mul_of_not_dvd k hp hn',
    Nat.ordCompl_pow_mul_of_not_dvd r hp hm'] at hec
  refine ⟨?_,hec⟩
  rw [hec] at he
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hm0) he

/-- Explicitly evaluate the convolution. Its prime-supported factor may have
any value at one, including zero. -/
lemma lemma162_prime_supported_convolution_apply {p : ℕ} (hp : p.Prime)
    (f g : ArithmeticFunction ℂ) (r m : ℕ) (hm : p.Coprime m) :
    (lemma162PrimePowerPart p f * lemma162CoprimePart p g) (p^r*m) =
      f (p^r)*g m := by
  have hm0 : m ≠ 0 := by
    intro hz
    subst m
    have hh : p=1 := by simpa using hm
    exact hp.ne_one hh
  have hprod0 := mul_ne_zero (pow_ne_zero r hp.ne_zero) hm0
  rw [ArithmeticFunction.mul_apply]
  rw [Finset.sum_eq_single (p^r,m)]
  · rw [lemma162_prime_power_part_apply,lemma162_coprime_part_apply p m g hm]
  · rintro ⟨a,b⟩ hab hne
    by_cases ha : ∃ k : ℕ, a=p^k
    · by_cases hb : p.Coprime b
      · obtain ⟨k,rfl⟩ := ha
        have he := (Nat.mem_divisorsAntidiagonal.mp hab).1
        obtain ⟨hpow,hb'⟩ := lemma162_prime_power_coprime_unique hp hm hb he
        exact False.elim (hne (Prod.ext hpow hb'))
      · simp [lemma162CoprimePart,hb]
    · simp [lemma162PrimePowerPart,ha]
  · intro hnot
    exact False.elim (hnot (Nat.mem_divisorsAntidiagonal.mpr ⟨rfl,hprod0⟩))

/-- Prime-local bivariate splitting implies an exact convolution identity
for the actual finite divisor sum. This is an algebraic theorem, not an
assumed Euler identity or assumed multiplicativity of the full coefficient. -/
lemma lemma162_divisor_kernel_prime_convolution {p : ℕ} (hp : p.Prime)
    (H A B : ℕ → ℕ → ℂ)
    (hsplit : ∀ i j d l : ℕ, p.Coprime (d*l) →
      H (p^i*d) (p^j*l) = A (p^i) (p^j)*B d l) :
    lemma152DivisorKernelSum H =
      lemma162PrimePowerPart p (lemma152DivisorKernelSum A) *
        lemma162CoprimePart p (lemma152DivisorKernelSum B) := by
  ext n
  by_cases hn : n=0
  · subst n
    simp
  obtain ⟨r,m,hm,rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one
  have hcop := hp.coprime_iff_not_dvd.mpr hm
  rw [lemma162_prime_supported_convolution_apply hp _ _ r m hcop]
  apply lemma162_divisor_kernel_coprime_split H A B (Nat.Coprime.pow_left r hcop)
  intro a₁ a₂ b₁ b₂ ha hb
  have ha₁ : a₁ ∣ p^r := ha ▸ dvd_mul_right a₁ a₂
  have ha₂ : a₂ ∣ p^r := ha ▸ dvd_mul_left a₂ a₁
  obtain ⟨i,hi,rfl⟩ := (Nat.dvd_prime_pow hp).mp ha₁
  obtain ⟨j,hj,rfl⟩ := (Nat.dvd_prime_pow hp).mp ha₂
  apply hsplit
  simpa only [hb] using hcop

/-- Restricting a multiplicative arithmetic function to p-coprime inputs
preserves multiplicativity and retains its value one at one. -/
lemma lemma162_coprime_part_multiplicative (p : ℕ) (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative) : (lemma162CoprimePart p f).IsMultiplicative := by
  refine ⟨by simp [lemma162CoprimePart,hf.map_one],?_⟩
  intro m n hmn
  change (if p.Coprime (m*n) then f (m*n) else 0) =
    (if p.Coprime m then f m else 0)*(if p.Coprime n then f n else 0)
  rw [hf.map_mul_of_coprime hmn]
  by_cases hm : p.Coprime m
  · by_cases hn : p.Coprime n
    · have hh : p.Coprime (m*n) := Nat.coprime_mul_iff_right.mpr ⟨hm,hn⟩
      rw [if_pos hh,if_pos hm,if_pos hn]
    · have hh : ¬p.Coprime (m*n) := fun h => hn (Nat.coprime_mul_iff_right.mp h).2
      rw [if_neg hh,if_pos hm,if_neg hn,mul_zero]
  · have hh : ¬p.Coprime (m*n) := fun h => hm (Nat.coprime_mul_iff_right.mp h).1
    rw [if_neg hh,if_neg hm,zero_mul]

/-- Pointwise multiplication by a multiplicative function distributes across
a convolution whose two supports are pairwise coprime. Neither convolution
factor itself needs to be multiplicative. -/
lemma lemma162_pmul_convolution_of_coprime_support
    (f g h : ArithmeticFunction ℂ) (hh : h.IsMultiplicative)
    (hcop : ∀ a b : ℕ, f a ≠ 0 → g b ≠ 0 → a.Coprime b) :
    (f*g).pmul h = f.pmul h * g.pmul h := by
  ext n
  simp only [ArithmeticFunction.pmul_apply,ArithmeticFunction.mul_apply]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  rintro ⟨a,b⟩ hab
  by_cases ha : f a=0
  · simp [ha]
  by_cases hb : g b=0
  · simp [hb]
  have he := (Nat.mem_divisorsAntidiagonal.mp hab).1
  rw [← he,hh.map_mul_of_coprime (hcop a b ha hb)]
  ring

/-- Apply the actual multiplicative Hadamard weight, such as ν*χ, after the
prime-power/odd decomposition. The exceptional degree-zero term is retained. -/
lemma lemma162_prime_supported_pmul_convolution (p : ℕ)
    (f g h : ArithmeticFunction ℂ) (hh : h.IsMultiplicative) :
    (lemma162PrimePowerPart p f * lemma162CoprimePart p g).pmul h =
      (lemma162PrimePowerPart p f).pmul h * (lemma162CoprimePart p g).pmul h := by
  apply lemma162_pmul_convolution_of_coprime_support _ _ _ hh
  intro a b ha hb
  have hap : ∃ r : ℕ, a=p^r := by
    by_contra hn
    exact ha (by simp [lemma162PrimePowerPart,hn])
  have hbp : p.Coprime b := by
    by_contra hn
    exact hb (by simp [lemma162CoprimePart,hn])
  obtain ⟨r,rfl⟩ := hap
  exact Nat.Coprime.pow_left r hbp

/-- Coefficient-level reassembly, already including the Hadamard multiplier.
Use p=2, A=the exact 2-adic source kernel/N₂, and B=the odd normalized kernel. -/
lemma lemma162_weighted_divisor_kernel_prime_convolution {p : ℕ} (hp : p.Prime)
    (H A B : ℕ → ℕ → ℂ)
    (hsplit : ∀ i j d l : ℕ, p.Coprime (d*l) →
      H (p^i*d) (p^j*l) = A (p^i) (p^j)*B d l)
    (h : ArithmeticFunction ℂ) (hh : h.IsMultiplicative) :
    (lemma152DivisorKernelSum H).pmul h =
      (lemma162PrimePowerPart p (lemma152DivisorKernelSum A)).pmul h *
        (lemma162CoprimePart p (lemma152DivisorKernelSum B)).pmul h := by
  rw [lemma162_divisor_kernel_prime_convolution hp H A B hsplit]
  exact lemma162_prime_supported_pmul_convolution p _ _ h hh

/-- Once absolute convergence of the two concrete pieces is proved, ordinary
L-series convolution supplies convergence of the actual coefficient and the
product identity. No multiplicativity is demanded of the exceptional piece. -/
lemma lemma162_weighted_divisor_kernel_lseries {p : ℕ} (hp : p.Prime)
    (H A B : ℕ → ℕ → ℂ)
    (hsplit : ∀ i j d l : ℕ, p.Coprime (d*l) →
      H (p^i*d) (p^j*l) = A (p^i) (p^j)*B d l)
    (h : ArithmeticFunction ℂ) (hh : h.IsMultiplicative) (s : ℂ)
    (hf : LSeriesSummable
      ((lemma162PrimePowerPart p (lemma152DivisorKernelSum A)).pmul h) s)
    (hg : LSeriesSummable
      ((lemma162CoprimePart p (lemma152DivisorKernelSum B)).pmul h) s) :
    LSeriesSummable ((lemma152DivisorKernelSum H).pmul h) s ∧
      LSeries ((lemma152DivisorKernelSum H).pmul h) s =
        LSeries ((lemma162PrimePowerPart p (lemma152DivisorKernelSum A)).pmul h) s *
          LSeries ((lemma162CoprimePart p (lemma152DivisorKernelSum B)).pmul h) s := by
  rw [lemma162_weighted_divisor_kernel_prime_convolution hp H A B hsplit h hh]
  exact ⟨ArithmeticFunction.LSeriesSummable_mul hf hg,
    ArithmeticFunction.LSeries_mul' hf hg⟩

end ZhangLS.Spec
