import ZhangLS.Spec.Proposition71ConvolutionSplit
import ZhangLS.Spec.Lemma34CoefficientEnergy

/-! # Genuine divisor and totient weights in the Section 7 conductor sums

The submultiplicative τ bounds follow from the proved gcd divisor-pair
bijection. Reciprocal totient loss is retained and bounded arithmetically.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset
open scoped Classical ArithmeticFunction.zeta
set_option maxHeartbeats 2000000

lemma proposition71_nat_divisor_pair_split {d l : ℕ} (hd : d≠0) (hl : l≠0)
    (F : ℕ → ℕ → ℕ) :
    (∑ ab∈(d*l).divisorsAntidiagonal, F ab.1 ab.2)=
      ∑ dd∈d.divisorsAntidiagonal,
        ∑ ll∈l.divisorsAntidiagonal.filter (fun ll => ll.1.Coprime dd.2),
          F (dd.1*ll.1) (dd.2*ll.2) := by
  have hh := proposition71_divisor_pair_split hd hl (fun a b => (F a b : ℂ))
  exact_mod_cast hh

/-- Convolution preserves submultiplicativity for nonnegative arithmetic functions. -/
theorem proposition71_convolution_submultiplicative (f g : ArithmeticFunction ℕ)
    (hf : ∀m n, f (m*n)≤f m*f n) (hg : ∀m n, g (m*n)≤g m*g n) (m n : ℕ) :
    (f*g) (m*n)≤(f*g) m*(f*g) n := by
  by_cases hm : m=0
  · subst m; simp
  by_cases hn : n=0
  · subst n; simp
  rw [ArithmeticFunction.mul_apply,proposition71_nat_divisor_pair_split hm hn (fun a b => f a*g b)]
  calc
    _≤∑ dd∈m.divisorsAntidiagonal, ∑ ll∈n.divisorsAntidiagonal,
        (f dd.1*g dd.2)*(f ll.1*g ll.2) := by
      apply sum_le_sum
      intro dd hdd
      calc
        _≤∑ ll∈n.divisorsAntidiagonal.filter (fun ll => ll.1.Coprime dd.2),
            (f dd.1*g dd.2)*(f ll.1*g ll.2) := by
          apply sum_le_sum
          intro ll hll
          calc
            _≤(f dd.1*f ll.1)*(g dd.2*g ll.2) := Nat.mul_le_mul (hf _ _) (hg _ _)
            _=_ := by ring
        _≤∑ ll∈n.divisorsAntidiagonal, (f dd.1*g dd.2)*(f ll.1*g ll.2) :=
          sum_le_sum_of_subset (filter_subset _ _)
    _=_ := by
      rw [ArithmeticFunction.mul_apply,ArithmeticFunction.mul_apply,sum_mul_sum]

/-- The genuine standard τ_k is submultiplicative, including noncoprime arguments. -/
theorem proposition71_tau_submultiplicative (k m n : ℕ) :
    lemma34Tau k (m*n)≤lemma34Tau k m*lemma34Tau k n := by
  induction k generalizing m n with
  | zero =>
    by_cases hm : m=1 <;> by_cases hn : n=1 <;>
      simp [lemma34Tau,ArithmeticFunction.one_apply,hm,hn]
  | succ k ih =>
    have hz (a b : ℕ) : ArithmeticFunction.zeta (a*b)≤ArithmeticFunction.zeta a*ArithmeticFunction.zeta b := by
      by_cases ha : a=0
      · subst a; simp
      by_cases hb : b=0
      · subst b; simp
      simp [ArithmeticFunction.zeta_apply_ne ha,ArithmeticFunction.zeta_apply_ne hb,
        ArithmeticFunction.zeta_apply_ne (Nat.mul_ne_zero ha hb)]
    simpa only [lemma34Tau,pow_succ] using
      proposition71_convolution_submultiplicative (ArithmeticFunction.zeta^k)
        ArithmeticFunction.zeta (fun a b => ih a b) hz m n

/-- The reciprocal totient costs at most τ₂(n)/n, with positivity explicit. -/
theorem proposition71_reciprocal_totient_le_tau {n : ℕ} (hn : 0<n) :
    (Nat.totient n : ℝ)⁻¹≤(lemma34Tau 2 n : ℝ)/(n : ℝ) := by
  have hphi : 0<Nat.totient n := Nat.totient_pos.mpr hn
  have hnat : n≤lemma34Tau 2 n*Nat.totient n := by
    calc
      n=∑ d∈n.divisors, Nat.totient d := (Nat.sum_totient n).symm
      _≤∑ _d∈n.divisors, Nat.totient n := by
        apply sum_le_sum
        intro d hd
        exact Nat.le_of_dvd hphi (Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_divisors hd))
      _=n.divisors.card*Nat.totient n := by simp
      _=_ := by rw [lemma34_tau2_eq_divisor_card]
  have hnr : (0:ℝ)<n := by exact_mod_cast hn
  have hpr : (0:ℝ)<Nat.totient n := by exact_mod_cast hphi
  apply (le_div_iff₀ hnr).mpr
  rw [mul_comm,←div_eq_mul_inv]
  apply (div_le_iff₀ hpr).mpr
  exact_mod_cast hnat

/-- This is the actual φ(hr) denominator, including possible common primes. -/
theorem proposition71_reciprocal_product_totient {h r : ℕ} (hh : 0<h) (hr : 0<r) :
    (Nat.totient (h*r) : ℝ)⁻¹≤
      (lemma34Tau 2 h : ℝ)*(lemma34Tau 2 r : ℝ)/((h : ℝ)*(r : ℝ)) := by
  have hb := proposition71_reciprocal_totient_le_tau (Nat.mul_pos hh hr)
  rw [Nat.cast_mul] at hb
  apply hb.trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast proposition71_tau_submultiplicative 2 h r

end ZhangLS.Spec
