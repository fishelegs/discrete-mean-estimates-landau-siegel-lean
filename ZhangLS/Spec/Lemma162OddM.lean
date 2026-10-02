import ZhangLS.Spec.Lemma162GeneralMContinuation
import ZhangLS.Spec.Lemma153FiniteProductRatio

/-! Universal isolation of q=2. Only the odd product is normalized; the
possibly vanishing q=2 factor is never divided out in the exceptional case. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex Filter Topology
open scoped Classical
set_option maxHeartbeats 2000000

def lemma162PrimeTwo : Nat.Primes := ⟨2,Nat.prime_two⟩

noncomputable def lemma162OddMPrimeFactor {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (d l : ℕ) (q : Nat.Primes) (s : ℂ) : ℂ :=
  if 2<q.val then lemma162GeneralMPrimeFactor χ β d l q s else 1

noncomputable def lemma162OddMEulerProduct {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (d l : ℕ) (s : ℂ) : ℂ :=
  ∏' q : Nat.Primes, lemma162OddMPrimeFactor χ β d l q s

lemma lemma162_odd_m_multipliable {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) {d l : ℕ} (hd : d ≠ 0) (hl : l ≠ 0)
    (s : ℂ) (hs : 9/10 ≤ s.re) :
    Multipliable (fun q : Nat.Primes => lemma162OddMPrimeFactor χ β d l q s) := by
  have hsum : Summable (fun q : Nat.Primes => ‖lemma162OddMPrimeFactor χ β d l q s-1‖) := by
    apply (lemma162_general_m_majorant_summable hd hl).of_nonneg_of_le (fun _ => norm_nonneg _)
    intro q
    unfold lemma162OddMPrimeFactor
    split_ifs
    · exact lemma162_general_m_prime_error_bound χ β hβ d l q s hs
    · simp only [sub_self,norm_zero]
      unfold lemma162GeneralMMajorant
      have hC := lemma152_correction_constant_pos
      have hE := lemma162_general_m_exception_bound_pos
      split_ifs <;> positivity
  simpa only [add_sub_cancel] using multipliable_one_add_of_summable hsum

lemma lemma162_general_m_two_odd_decomposition {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) {d l : ℕ} (hd : d ≠ 0) (hl : l ≠ 0)
    (s : ℂ) (hs : 9/10 ≤ s.re) :
    lemma162GeneralMEulerProduct χ β d l s =
      lemma162GeneralMPrimeFactor χ β d l lemma162PrimeTwo s *
        lemma162OddMEulerProduct χ β d l s := by
  have hsmall := lemma153_finite_ite_hasProd ({lemma162PrimeTwo} : Finset Nat.Primes)
    (fun q => lemma162GeneralMPrimeFactor χ β d l q s)
  simp only [prod_singleton] at hsmall
  have hodd := (lemma162_odd_m_multipliable χ β hβ hd hl s hs).hasProd
  have hwhole := (lemma162_general_m_euler_multipliable χ β hβ hd hl s hs).hasProd
  have hprod : HasProd (fun q => lemma162GeneralMPrimeFactor χ β d l q s)
      (lemma162GeneralMPrimeFactor χ β d l lemma162PrimeTwo s *
        lemma162OddMEulerProduct χ β d l s) := by
    apply (hsmall.mul hodd).congr_fun
    intro q
    by_cases hq : 2<q.val
    · have hn : q ≠ lemma162PrimeTwo := by
        intro h; rw [h] at hq; norm_num [lemma162PrimeTwo] at hq
      simp [lemma162OddMPrimeFactor,hq,hn]
    · have he : q = lemma162PrimeTwo := by
        apply Subtype.ext
        have ht := q.property.two_le
        dsimp [lemma162PrimeTwo]
        omega
      subst q
      simp [lemma162OddMPrimeFactor,lemma162PrimeTwo]
  exact hwhole.unique hprod

lemma lemma162_odd_m_baseline {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β s : ℂ) :
    lemma162OddMEulerProduct χ β 1 1 s =
      lemma161RestrictedProduct χ β (fun q => 2<q.val) s := by
  unfold lemma162OddMEulerProduct lemma161RestrictedProduct
  apply tprod_congr
  intro q
  simp [lemma162OddMPrimeFactor,lemma161RestrictedFactor]

noncomputable def lemma162TwoNormalizer {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β s : ℂ) : ℂ :=
  if χ.evalNat 2 = 1 then 2 else lemma161PrimeFactor χ β lemma162PrimeTwo s

lemma lemma162_star_odd_decomposition {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (s : ℂ) (hs : 9/10 ≤ s.re) :
    lemma161Star χ β s = lemma162TwoNormalizer χ β s *
      lemma162OddMEulerProduct χ β 1 1 s := by
  by_cases h2 : χ.evalNat 2 = 1
  · simp [lemma161Star,lemma162TwoNormalizer,h2,lemma162_odd_m_baseline]
  · rw [lemma161Star,if_neg h2,lemma162TwoNormalizer,if_neg h2]
    have h := lemma162_general_m_two_odd_decomposition χ β hβ (by norm_num : (1:ℕ)≠0)
      (by norm_num : (1:ℕ)≠0) s hs
    simpa only [lemma162_general_m_baseline,lemma162_general_m_baseline_prime] using h

lemma lemma162_odd_baseline_nonzero {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (s : ℂ) (hs : 9/10 ≤ s.re)
    (hstar : lemma161Star χ β s ≠ 0) :
    lemma162OddMEulerProduct χ β 1 1 s ≠ 0 ∧ lemma162TwoNormalizer χ β s ≠ 0 := by
  rw [lemma162_star_odd_decomposition χ β hβ s hs] at hstar
  exact ⟨right_ne_zero_of_mul hstar,left_ne_zero_of_mul hstar⟩

lemma lemma162_general_m_prime_pair_mul {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (d l d' l' : ℕ) (h : (d*l).Coprime (d'*l'))
    (q : Nat.Primes) (s : ℂ) :
    lemma162GeneralMPrimeFactor χ β (d*d') (l*l') q s * lemma161PrimeFactor χ β q s =
      lemma162GeneralMPrimeFactor χ β d l q s * lemma162GeneralMPrimeFactor χ β d' l' q s := by
  by_cases hq : q.val ∣ d*l
  · have hq' : ¬q.val ∣ d'*l' := fun hh => q.property.ne_one (Nat.eq_one_of_dvd_coprimes h hq hh)
    have hd' : ¬q.val ∣ d' := fun hh => hq' (hh.trans (dvd_mul_right d' l'))
    have hl' : ¬q.val ∣ l' := fun hh => hq' (hh.trans (dvd_mul_left l' d'))
    simp [lemma162GeneralMPrimeFactor,q.property.dvd_mul,hd',hl']
  · have hd : ¬q.val ∣ d := fun hh => hq (hh.trans (dvd_mul_right d l))
    have hl : ¬q.val ∣ l := fun hh => hq (hh.trans (dvd_mul_left l d))
    simp [lemma162GeneralMPrimeFactor,q.property.dvd_mul,hd,hl,mul_comm]

lemma lemma162_odd_m_prime_pair_mul {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (d l d' l' : ℕ) (h : (d*l).Coprime (d'*l'))
    (q : Nat.Primes) (s : ℂ) :
    lemma162OddMPrimeFactor χ β (d*d') (l*l') q s * lemma162OddMPrimeFactor χ β 1 1 q s =
      lemma162OddMPrimeFactor χ β d l q s * lemma162OddMPrimeFactor χ β d' l' q s := by
  unfold lemma162OddMPrimeFactor
  split_ifs
  · simpa only [lemma162_general_m_baseline_prime] using
      lemma162_general_m_prime_pair_mul χ β d l d' l' h q s
  · simp

lemma lemma162_odd_m_pair_mul {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0)
    {d l d' l' : ℕ} (hd : d ≠ 0) (hl : l ≠ 0) (hd' : d' ≠ 0) (hl' : l' ≠ 0)
    (h : (d*l).Coprime (d'*l')) (s : ℂ) (hs : 9/10 ≤ s.re) :
    lemma162OddMEulerProduct χ β (d*d') (l*l') s * lemma162OddMEulerProduct χ β 1 1 s =
      lemma162OddMEulerProduct χ β d l s * lemma162OddMEulerProduct χ β d' l' s := by
  have ha := (lemma162_odd_m_multipliable χ β hβ (mul_ne_zero hd hd') (mul_ne_zero hl hl') s hs).hasProd
  have hb := (lemma162_odd_m_multipliable χ β hβ (by norm_num : (1:ℕ)≠0) (by norm_num : (1:ℕ)≠0) s hs).hasProd
  have hc := (lemma162_odd_m_multipliable χ β hβ hd hl s hs).hasProd
  have he := (lemma162_odd_m_multipliable χ β hβ hd' hl' s hs).hasProd
  exact ((ha.mul hb).congr_fun (fun q => (lemma162_odd_m_prime_pair_mul χ β d l d' l' h q s).symm)).unique (hc.mul he)

lemma lemma162_odd_m_normalized_pair_mul {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0)
    {d l d' l' : ℕ} (hd : d ≠ 0) (hl : l ≠ 0) (hd' : d' ≠ 0) (hl' : l' ≠ 0)
    (h : (d*l).Coprime (d'*l')) (s : ℂ) (hs : 9/10 ≤ s.re)
    (hB : lemma162OddMEulerProduct χ β 1 1 s ≠ 0) :
    lemma162OddMEulerProduct χ β (d*d') (l*l') s / lemma162OddMEulerProduct χ β 1 1 s =
      (lemma162OddMEulerProduct χ β d l s / lemma162OddMEulerProduct χ β 1 1 s) *
        (lemma162OddMEulerProduct χ β d' l' s / lemma162OddMEulerProduct χ β 1 1 s) := by
  have hh := lemma162_odd_m_pair_mul χ β hβ hd hl hd' hl' h s hs
  field_simp
  exact hh

end ZhangLS.Spec
