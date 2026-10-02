import ZhangLS.Spec.Proposition71Mobius
import ZhangLS.Spec.Proposition71ArithmeticFactors
import ZhangLS.Spec.Proposition71Objects

/-! Exact finite reindexing for the substitutions k=r k₁, l=r m and n=d₁ k₁
in the proof of (7.21). The only generic hypotheses are positivity, downward
closure, and actual vanishing outside the finite support. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 4000000

/-- Finite positive intervals, with any strict endpoint, are adequate here. -/
def Section721PositiveLowerSet (I : Finset ℕ) : Prop :=
  (∀ n ∈ I, 0 < n) ∧ ∀ n ∈ I, ∀ m, 0 < m → m ≤ n → m ∈ I

lemma section721_indices_lower (D : ℕ) :
    Section721PositiveLowerSet (lemma81PolynomialIndices D) := by
  constructor
  · intro n hn
    exact ((proposition71_mem_indices D n).mp hn).1
  · intro n hn m hm hmn
    rw [proposition71_mem_indices] at hn ⊢
    exact ⟨hm, (by exact_mod_cast hmn : (m : ℝ) ≤ (n : ℝ)).trans_lt hn.2⟩

/-- The actual common-divisor substitution, with no coprimality discarded. -/
theorem section721_common_divisor_reindex (I : Finset ℕ)
    (hI : Section721PositiveLowerSet I) (F : ℕ → ℕ → ℂ) (w : ℕ → ℂ)
    (hF : ∀ k l, 0 < k → 0 < l → F k l ≠ 0 → k ∈ I ∧ l ∈ I) :
    (∑ k ∈ I, ∑ l ∈ I, F k l * ∑ r ∈ (Nat.gcd k l).divisors, w r) =
      ∑ r ∈ I, ∑ k ∈ I, ∑ m ∈ I, F (r*k) (r*m) * w r := by
  let s := (I ×ˢ I).sigma (fun kl => (Nat.gcd kl.1 kl.2).divisors)
  let t := I ×ˢ (I ×ˢ I)
  have hh : (∑ x ∈ t, F (x.1*x.2.1) (x.1*x.2.2)*w x.1) =
      ∑ x ∈ s, F x.1.1 x.1.2*w x.2 := by
    apply sum_bij_ne_zero (fun x _ _ => ⟨(x.1*x.2.1,x.1*x.2.2),x.1⟩)
    · intro x hx hn
      rcases mem_product.mp hx with ⟨hr,hh⟩
      rcases mem_product.mp hh with ⟨hk,hm⟩
      have hp := hF _ _ (Nat.mul_pos (hI.1 _ hr) (hI.1 _ hk))
        (Nat.mul_pos (hI.1 _ hr) (hI.1 _ hm)) (mul_ne_zero_iff.mp hn).1
      apply mem_sigma.mpr
      exact ⟨mem_product.mpr hp, Nat.mem_divisors.mpr
        ⟨Nat.dvd_gcd (dvd_mul_right _ _) (dvd_mul_right _ _),
          Nat.ne_of_gt (Nat.gcd_pos_of_pos_left _ (Nat.mul_pos (hI.1 _ hr) (hI.1 _ hk)))⟩⟩
    · intro x hx hnx y hy hny he
      have hr : x.1=y.1 := congrArg (fun z : (Σ _ : ℕ×ℕ, ℕ) => z.2) he
      have hk : x.1*x.2.1=y.1*y.2.1 :=
        congrArg (fun z : (Σ _ : ℕ×ℕ, ℕ) => z.1.1) he
      have hm : x.1*x.2.2=y.1*y.2.2 :=
        congrArg (fun z : (Σ _ : ℕ×ℕ, ℕ) => z.1.2) he
      have hypos := hI.1 y.1 (mem_product.mp hy).1
      rw [hr] at hk hm
      exact Prod.ext hr (Prod.ext (Nat.eq_of_mul_eq_mul_left hypos hk)
        (Nat.eq_of_mul_eq_mul_left hypos hm))
    · intro x hx hn
      rcases mem_sigma.mp hx with ⟨hkl,hr⟩
      rcases mem_product.mp hkl with ⟨hk,hl⟩
      have hrd := (Nat.mem_divisors.mp hr).1
      have hrk := dvd_trans hrd (Nat.gcd_dvd_left x.1.1 x.1.2)
      have hrl := dvd_trans hrd (Nat.gcd_dvd_right x.1.1 x.1.2)
      have hrpos : 0 < x.2 := Nat.pos_of_ne_zero (by
        intro hz
        rw [hz,zero_dvd_iff] at hrk
        exact (Nat.ne_of_gt (hI.1 _ hk)) hrk)
      have hrmem := hI.2 _ hk _ hrpos (Nat.le_of_dvd (hI.1 _ hk) hrk)
      have hkp := Nat.div_pos (Nat.le_of_dvd (hI.1 _ hk) hrk) hrpos
      have hlp := Nat.div_pos (Nat.le_of_dvd (hI.1 _ hl) hrl) hrpos
      have hkmem := hI.2 _ hk _ hkp (Nat.div_le_self _ _)
      have hlmem := hI.2 _ hl _ hlp (Nat.div_le_self _ _)
      have he1 : x.2*(x.1.1/x.2)=x.1.1 := Nat.mul_div_cancel' hrk
      have he2 : x.2*(x.1.2/x.2)=x.1.2 := Nat.mul_div_cancel' hrl
      refine ⟨(x.2,x.1.1/x.2,x.1.2/x.2),
        mem_product.mpr ⟨hrmem,mem_product.mpr ⟨hkmem,hlmem⟩⟩,?_,?_⟩
      · simpa only [he1,he2] using hn
      · simp only [he1,he2,Prod.mk.eta,Sigma.eta]
    · intro x hx hn
      rfl
  simp only [s,t,sum_sigma,sum_product] at hh
  simpa only [mul_sum] using hh.symm

/-- Group the positive pair (d₁,k₁) by its genuine product n. -/
theorem section721_product_reindex (I : Finset ℕ)
    (hI : Section721PositiveLowerSet I) (F : ℕ → ℕ → ℂ)
    (hF : ∀ a ∈ I, ∀ b ∈ I, F a b ≠ 0 → a*b ∈ I) :
    (∑ a ∈ I, ∑ b ∈ I, F a b) =
      ∑ n ∈ I, ∑ ab ∈ n.divisorsAntidiagonal, F ab.1 ab.2 := by
  have hh : (∑ x ∈ I ×ˢ I, F x.1 x.2) =
      ∑ x ∈ I.sigma (fun n => n.divisorsAntidiagonal), F x.2.1 x.2.2 := by
    apply sum_bij_ne_zero (fun x _ _ => ⟨x.1*x.2,x⟩)
    · intro x hx hn
      rcases mem_product.mp hx with ⟨ha,hb⟩
      exact mem_sigma.mpr ⟨hF _ ha _ hb hn,Nat.mem_divisorsAntidiagonal.mpr
        ⟨rfl,Nat.ne_of_gt (Nat.mul_pos (hI.1 _ ha) (hI.1 _ hb))⟩⟩
    · intro x hx hnx y hy hny he
      exact congrArg (fun z : (Σ _ : ℕ, ℕ×ℕ) => z.2) he
    · intro x hx hn
      rcases mem_sigma.mp hx with ⟨hxI,hxab⟩
      rcases Nat.mem_divisorsAntidiagonal.mp hxab with ⟨he,hne⟩
      have hpos : 0 < x.2.1*x.2.2 := he.symm ▸ hI.1 _ hxI
      have ha : 0 < x.2.1 := Nat.pos_of_mul_pos_right hpos
      have hb : 0 < x.2.2 := Nat.pos_of_mul_pos_left hpos
      have ham := hI.2 _ hxI _ ha (by nlinarith)
      have hbm := hI.2 _ hxI _ hb (by nlinarith)
      exact ⟨x.2,mem_product.mpr ⟨ham,hbm⟩,hn,by exact Sigma.ext he (heq_of_eq rfl)⟩
    · intro x hx hn
      rfl
  simpa only [sum_product,sum_sigma] using hh

end ZhangLS.Spec
