import ZhangLS.Spec.Lemma32BurgessLineCount
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset
open scoped Classical

lemma lemma32_burgess_fixed_multiplier_congruence_card {D A N a b : ℕ}
    (hsize : 2*A*N < D) (ha : a ≤ A) (hbA : b ≤ A) (hb : 0 < b) (M : ℤ) :
    ((Finset.univ : Finset (Fin N × Fin N)).filter
      (fun p => (D : ℤ) ∣ lemma32BurgessDeterminant M a b p.1 p.2)).card ≤
      N/(b/(a.gcd b))+1 := by
  let S : Finset (Fin N × Fin N) := Finset.univ.filter
    (fun p => (D : ℤ) ∣ lemma32BurgessDeterminant M a b p.1 p.2)
  by_cases hs : S.Nonempty
  · obtain ⟨p, hp⟩ := hs
    have hsub : S ⊆ Finset.univ.filter
        (fun q : Fin N × Fin N => lemma32BurgessDeterminant M a b q.1 q.2=
          lemma32BurgessDeterminant M a b p.1 p.2) := by
      intro q hq
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      exact lemma32_burgess_determinant_unique hsize ha hbA M q.1 q.2 p.1 p.2
        (Finset.mem_filter.mp hq).2 (Finset.mem_filter.mp hp).2
    exact (Finset.card_le_card hsub).trans
      (lemma32_burgess_fixed_determinant_card M hb _)
  · have he : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    change S.card ≤ _
    rw [he, Finset.card_empty]
    exact Nat.zero_le _

lemma lemma32_burgess_fixed_multiplier_real_count {D A N a b : ℕ}
    (hsize : 2*A*N < D) (ha : a ≤ A) (hbA : b ≤ A) (hb : 0 < b) (M : ℤ) :
    (((Finset.univ : Finset (Fin N × Fin N)).filter
      (fun p => (D : ℤ) ∣ lemma32BurgessDeterminant M a b p.1 p.2)).card : ℝ) ≤
      (N : ℝ)*(a.gcd b : ℝ)/(b : ℝ)+1 := by
  let g := a.gcd b
  let q := b/g
  have hg : 0 < g := Nat.gcd_pos_of_pos_right a hb
  have hq : 0 < q := Nat.div_pos (Nat.le_of_dvd hb (Nat.gcd_dvd_right a b)) hg
  have hbg : (b : ℝ)=(q : ℝ)*(g : ℝ) := by
    exact_mod_cast (Nat.div_mul_cancel (Nat.gcd_dvd_right a b)).symm
  have hc : (((Finset.univ : Finset (Fin N × Fin N)).filter
      (fun p => (D : ℤ) ∣ lemma32BurgessDeterminant M a b p.1 p.2)).card : ℝ) ≤
      ((N/q : ℕ) : ℝ)+1 := by
    exact_mod_cast lemma32_burgess_fixed_multiplier_congruence_card hsize ha hbA hb M
  calc
    _ ≤ ((N/q : ℕ) : ℝ)+1 := hc
    _ ≤ (N : ℝ)/(q : ℝ)+1 := add_le_add Nat.cast_div_le le_rfl
    _ = _ := by
      change (N : ℝ)/(q : ℝ)+1=(N : ℝ)*(g : ℝ)/(b : ℝ)+1
      rw [hbg]
      field_simp

end ZhangLS.Spec
