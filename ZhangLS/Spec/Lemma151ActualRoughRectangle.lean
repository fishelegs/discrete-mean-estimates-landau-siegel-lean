import ZhangLS.Spec.Lemma151ActualFiniteSupport
import ZhangLS.Spec.FiniteDivisorProductReindex

/-! Exact smooth/rough factor splitting for the actual Lemma 15.1 coefficient.
The initial product cutoff is removed only through original kernel support. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical

lemma actual151_rough_domain_positive {D X n : ℕ}
    (hn : n∈roughCollisionDomain D X) : 0<n :=
  (mem_Icc.mp (mem_filter.mp hn).1).1

lemma actual151_rough_domain_factor_closed {D X a b : ℕ}
    (ha : 0<a) (hb : 0<b) (hab : a*b∈roughCollisionDomain D X) :
    a∈roughCollisionDomain D X ∧ b∈roughCollisionDomain D X := by
  have hp := mem_filter.mp hab
  have hX := (mem_Icc.mp hp.1).2
  constructor
  · exact mem_filter.mpr ⟨mem_Icc.mpr
      ⟨ha,(Nat.le_mul_of_pos_right a hb).trans hX⟩,
        Nat.Coprime.of_dvd_left (show a∣a*b from ⟨b,rfl⟩) hp.2⟩
  · exact mem_filter.mpr ⟨mem_Icc.mpr
      ⟨hb,(Nat.le_mul_of_pos_left b ha).trans hX⟩,
        Nat.Coprime.of_dvd_left (show b∣a*b from ⟨a,mul_comm a b⟩) hp.2⟩

/-- Exact finite reindexing of b0(n1*n) with an arbitrary arithmetic weight.
No coprimality between the two rough factors is assumed. -/
theorem actual151_b_weight_rough_rectangle {D n₁ : ℕ}
    (hn₁ : Lemma151Supported (lemma151Q D) n₁) (f : ℕ→ℂ) :
    (∑ n∈roughCollisionDomain D ⌊lemma23PaperP D⌋₊,
      lemma151BChiPsi D (n₁*n)*f n/n) =
      ∑ dd∈n₁.divisorsAntidiagonal,
        ∑ a∈roughCollisionDomain D ⌊lemma23PaperP D⌋₊,
          ∑ b∈roughCollisionDomain D ⌊lemma23PaperP D⌋₊,
            lemma151First D (dd.1*a)*lemma151Second D (dd.2*b)*
              f (a*b)/((a : ℂ)*(b : ℂ)) := by
  let S := roughCollisionDomain D ⌊lemma23PaperP D⌋₊
  have hsplit (n : ℕ) (hn : n∈S) :
      lemma151BChiPsi D (n₁*n)*f n/n =
        ∑ dd∈n₁.divisorsAntidiagonal, ∑ ll∈n.divisorsAntidiagonal,
          lemma151First D (dd.1*ll.1)*lemma151Second D (dd.2*ll.2)*
            f (ll.1*ll.2)/((ll.1 : ℂ)*(ll.2 : ℂ)) := by
    have hnQ : n.Coprime (lemma151Q D) := (mem_filter.mp hn).2
    rw [roughCollision_actual_B_smooth_split hn₁ hnQ
      (actual151_rough_domain_positive hn).ne']
    simp only [sum_mul,sum_div]
    apply sum_congr rfl
    intro dd hdd
    apply sum_congr rfl
    intro ll hll
    rw [←(Nat.mem_divisorsAntidiagonal.mp hll).1,Nat.cast_mul]
  change (∑ n∈S,lemma151BChiPsi D (n₁*n)*f n/n)=_
  calc
    _ = ∑ n∈S,∑ dd∈n₁.divisorsAntidiagonal,∑ ll∈n.divisorsAntidiagonal,
          lemma151First D (dd.1*ll.1)*lemma151Second D (dd.2*ll.2)*
            f (ll.1*ll.2)/((ll.1 : ℂ)*(ll.2 : ℂ)) := sum_congr rfl hsplit
    _ = ∑ dd∈n₁.divisorsAntidiagonal,∑ n∈S,∑ ll∈n.divisorsAntidiagonal,
          lemma151First D (dd.1*ll.1)*lemma151Second D (dd.2*ll.2)*
            f (ll.1*ll.2)/((ll.1 : ℂ)*(ll.2 : ℂ)) := sum_comm
    _ = ∑ dd∈n₁.divisorsAntidiagonal,∑ a∈S,∑ b∈S,
          if a*b∈S then
            lemma151First D (dd.1*a)*lemma151Second D (dd.2*b)*
              f (a*b)/((a : ℂ)*(b : ℂ)) else 0 := by
      apply sum_congr rfl
      intro dd hdd
      exact finiteDivisorProduct_reindex S
        (fun _ hn => actual151_rough_domain_positive hn)
        (fun _ _ ha hb hab => actual151_rough_domain_factor_closed ha hb hab)
        (fun a b => lemma151First D (dd.1*a)*lemma151Second D (dd.2*b)*
          f (a*b)/((a : ℂ)*(b : ℂ)))
    _ = _ := by
      apply sum_congr rfl
      intro dd hdd
      apply sum_congr rfl
      intro a ha
      apply sum_congr rfl
      intro b hb
      by_cases hab : a*b∈S
      · rw [if_pos hab]
      · rw [if_neg hab]
        have hddpos := actual151_divisor_coordinates hdd
        have hz : lemma151First D (dd.1*a)*lemma151Second D (dd.2*b)=0 := by
          by_contra hne
          have hcut := actual151_kernel_pair_product_le_floor hddpos.1 hddpos.2.1 hne
          have haQ : a.Coprime (lemma151Q D) := (mem_filter.mp ha).2
          have hbQ : b.Coprime (lemma151Q D) := (mem_filter.mp hb).2
          exact hab (mem_filter.mpr ⟨mem_Icc.mpr
            ⟨Nat.mul_pos (actual151_rough_domain_positive ha)
              (actual151_rough_domain_positive hb),hcut⟩,
            Nat.coprime_mul_iff_left.mpr ⟨haQ,hbQ⟩⟩)
        simp [hz]

/-- The exact rho convolution is the full rough rectangle. -/
theorem actual151_rho_rough_rectangle {D n₁ : ℕ}
    (hn₁ : Lemma151Supported (lemma151Q D) n₁) (β : ℂ) :
    (∑ n∈roughCollisionDomain D ⌊lemma23PaperP D⌋₊,
      lemma151BChiPsi D (n₁*n)*lemma151Rho β n/n) =
      ∑ dd∈n₁.divisorsAntidiagonal,
        ∑ a∈roughCollisionDomain D ⌊lemma23PaperP D⌋₊,
          ∑ b∈roughCollisionDomain D ⌊lemma23PaperP D⌋₊,
            lemma151First D (dd.1*a)*lemma151Second D (dd.2*b)*
              lemma151Rho β (a*b)/((a : ℂ)*(b : ℂ)) :=
  actual151_b_weight_rough_rectangle hn₁ (lemma151Rho β)

/-- Exact source arithmetic sum after the actual psi coefficient cancellation,
with rho-star still present on every rough product. -/
theorem actual151_psi_arithmetic_sum_rectangle {D n₁ : ℕ}
    (χ : RealPrimitiveCharacter D) (hD : 1<D) (c : ℝ) (j : Fin 3)
    (hn₁ : Lemma151Supported (lemma151Q D) n₁) :
    lemma151ArithmeticSum χ c j (lemma151BPsi χ) n₁ =
      χ.evalNat n₁ * ∑ dd∈n₁.divisorsAntidiagonal,
        ∑ a∈roughCollisionDomain D ⌊lemma23PaperP D⌋₊,
          ∑ b∈roughCollisionDomain D ⌊lemma23PaperP D⌋₊,
            lemma151First D (dd.1*a)*lemma151Second D (dd.2*b)*
              lemma151RhoStar χ (lemma83PaperBeta D c j) (a*b)/((a : ℂ)*(b : ℂ)) := by
  rw [actual151_psi_arithmetic_sum_finite χ hD c j n₁ (Nat.pos_of_ne_zero hn₁.1),
    actual151_b_weight_rough_rectangle hn₁]

end ZhangLS.Spec
