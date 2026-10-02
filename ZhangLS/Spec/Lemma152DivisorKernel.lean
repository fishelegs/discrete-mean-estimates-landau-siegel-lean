import ZhangLS.Spec.Lemma171DirichletSeries

/-! Multiplicativity of genuine divisor kernels. This avoids defining arithmetic
coefficients by prime-factor products just to obtain multiplicativity. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Nat
open scoped Classical
set_option maxHeartbeats 1000000

noncomputable def lemma152DivisorKernelSum (H : ℕ → ℕ → ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => ∑ a ∈ n.divisorsAntidiagonal, H a.1 a.2, by simp⟩

/-- A kernel multiplicative in coprime pairs has a multiplicative divisor sum. -/
lemma lemma152_divisor_kernel_multiplicative (H : ℕ → ℕ → ℂ)
    (h1 : H 1 1 = 1)
    (hmul : ∀ a₁ a₂ b₁ b₂ : ℕ, (a₁*a₂).Coprime (b₁*b₂) →
      H (a₁*b₁) (a₂*b₂) = H a₁ a₂ * H b₁ b₂) :
    (lemma152DivisorKernelSum H).IsMultiplicative := by
  refine ⟨by simp [lemma152DivisorKernelSum,h1], ?_⟩
  simp only [lemma152DivisorKernelSum,ArithmeticFunction.coe_mk]
  intro m n cop
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
    exact (hmul a1 a2 b1 b2 cop).symm

end ZhangLS.Spec
