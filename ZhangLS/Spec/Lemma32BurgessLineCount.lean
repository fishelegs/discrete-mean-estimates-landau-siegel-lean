import Mathlib.Data.Fintype.BigOperators
import ZhangLS.Spec.Lemma32BurgessDeterminant
import ZhangLS.Spec.Lemma32ShortCongruenceClass
import Mathlib.Tactic.Linarith
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset
open scoped Classical

lemma lemma32_equal_determinant_projection_modEq (M : ℤ) {a b N : ℕ} (hb : 0 < b)
    (p q : Fin N × Fin N)
    (he : lemma32BurgessDeterminant M a b p.1 p.2=
      lemma32BurgessDeterminant M a b q.1 q.2) :
    Nat.ModEq (b/(a.gcd b)) p.2.val q.2.val := by
  have hd : (b : ℤ) ∣ (a : ℤ)*((q.2.val : ℤ)-(p.2.val : ℤ)) := by
    refine ⟨(q.1.val : ℤ)-(p.1.val : ℤ), ?_⟩
    unfold lemma32BurgessDeterminant at he
    simp only [mul_add] at he
    rw [mul_sub, mul_sub]
    linarith
  have hm : Nat.ModEq b (a*p.2.val) (a*q.2.val) := by
    apply Nat.modEq_iff_dvd.mpr
    simpa only [Nat.cast_mul, Int.mul_sub] using hd
  simpa only [Nat.gcd_comm] using hm.cancel_left_div_gcd hb

lemma lemma32_equal_determinant_second_projection_injective (M : ℤ) {a b N : ℕ}
    (hb : 0 < b) (p q : Fin N × Fin N)
    (he : lemma32BurgessDeterminant M a b p.1 p.2=
      lemma32BurgessDeterminant M a b q.1 q.2)
    (h2 : p.2=q.2) : p=q := by
  have h1 : p.1=q.1 := by
    have hv : (b : ℤ)*(p.1.val : ℤ)=(b : ℤ)*(q.1.val : ℤ) := by
      unfold lemma32BurgessDeterminant at he
      rw [h2] at he
      simp only [mul_add] at he
      linarith
    have hcast : (p.1.val : ℤ)=(q.1.val : ℤ) :=
      mul_left_cancel₀ (by exact_mod_cast hb.ne') hv
    exact Fin.ext (Int.natCast_inj.mp hcast)
  exact Prod.ext h1 h2

lemma lemma32_burgess_fixed_determinant_card (M : ℤ) {a b N : ℕ}
    (hb : 0 < b) (κ : ℤ) :
    ((Finset.univ : Finset (Fin N × Fin N)).filter
      (fun p => lemma32BurgessDeterminant M a b p.1 p.2=κ)).card ≤
      N/(b/(a.gcd b))+1 := by
  let S : Finset (Fin N × Fin N) := Finset.univ.filter
    (fun p => lemma32BurgessDeterminant M a b p.1 p.2=κ)
  have hinj : Set.InjOn Prod.snd (S : Set (Fin N × Fin N)) := by
    intro p hp q hq heq
    have hdet := (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm
    exact lemma32_equal_determinant_second_projection_injective M hb p q hdet heq
  have hclass : ∀ n ∈ S.image Prod.snd, ∀ m ∈ S.image Prod.snd,
      Nat.ModEq (b/(a.gcd b)) n.val m.val := by
    intro n hn m hm
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hm
    exact lemma32_equal_determinant_projection_modEq M hb p q
      ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm)
  calc
    _ = (S.image Prod.snd).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ N/(b/(a.gcd b))+1 := lemma32_short_congruence_class_card _ hclass

end ZhangLS.Spec
