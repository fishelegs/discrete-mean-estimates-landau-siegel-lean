import ZhangLS.Spec.Lemma32OddKernelDescent
import Mathlib.GroupTheory.Index
import Mathlib.Data.Nat.Totient
set_option autoImplicit false
namespace ZhangLS.Spec
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma32_units_reduction_kernel_card {m n : ℕ} [NeZero m] [NeZero n]
    (hd : m ∣ n) : Nat.card (ZMod.unitsMap hd).ker * m.totient = n.totient := by
  have he := (ZMod.unitsMap hd).ker.card_mul_index
  have hm : Nat.card (ZMod m)ˣ = m.totient := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have hn : Nat.card (ZMod n)ˣ = n.totient := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  rw [Subgroup.index_ker,
    (ZMod.unitsMap hd).range_eq_top_of_surjective (ZMod.unitsMap_surjective hd),
    Subgroup.card_top, hm, hn] at he
  exact he

lemma lemma32_prime_power_reduction_kernel_card {p : ℕ} (hp : p.Prime) (k : ℕ) :
    Nat.card (ZMod.unitsMap (dvd_pow_self p (Nat.succ_ne_zero k))).ker = p^k := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : NeZero (p^(k+1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have he := lemma32_units_reduction_kernel_card (dvd_pow_self p (Nat.succ_ne_zero k))
  rw [Nat.totient_prime hp, Nat.totient_prime_pow_succ hp] at he
  have hp2 := hp.two_le
  exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < p-1) he

end ZhangLS.Spec
