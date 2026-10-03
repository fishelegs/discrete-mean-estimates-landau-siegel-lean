import ZhangLS.Spec.FixedModulusGcdSums
import ZhangLS.Spec.PositiveNatFiniteSupport

/-! The exact fixed-D coprimality split with a finite literal divisor sum.
Nested long-index exchanges retain their genuine summability premise. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Finset
open scoped Classical

/-- Finite divisor form of the genuine fixed-D gcd equivalence. -/
theorem proposition141_fixed_gcd_finite_tsum {E:Type*}
    [NormedAddCommGroup E] [CompleteSpace E] {D:ℕ} (hD:0<D) (k:ℕ) (F:ℕ+→E)
    (hF:Summable (fun l:{l:ℕ+ // Nat.Coprime (l:ℕ) k}=>F l.val)) :
    (∑'l:ℕ+,if Nat.Coprime (l:ℕ) k then F l else 0)=
      ∑d∈D.divisors,if hd:0<d then
        if d.Coprime k then ∑'l:ℕ+,if (l:ℕ).Coprime ((D/d)*k) then F (⟨d,hd⟩*l) else 0
        else 0
      else 0 := by
  let G := fun d:ℕ+=>∑'l:ℕ+,if (l:ℕ).Coprime ((D/(d:ℕ))*k) then F (d*l) else 0
  have he (d:ℕ+) :
      (∑'l:{l:ℕ+ // (l:ℕ).Coprime ((D/(d:ℕ))*k)},F (d*l.val))=G d := by
    simpa only [G,Set.indicator_apply,Set.mem_setOf_eq] using
      (tsum_subtype {l:ℕ+ | (l:ℕ).Coprime ((D/(d:ℕ))*k)} (fun l=>F (d*l)))
  rw [fixedDCoprimeGcd_filtered_nested_tsum D k F hF]
  simp_rw [he]
  have ht := tsum_subtype {d:ℕ+ | (d:ℕ)∣D ∧ (d:ℕ).Coprime k} G
  simp only [Set.indicator_apply,Set.mem_setOf_eq] at ht
  calc
    _=(∑'d:ℕ+,if (d:ℕ)∣D ∧ (d:ℕ).Coprime k then G d else 0) := ht
    _=_ := by
      rw [positiveNat_tsum_eq_finset _ D.divisors (fun d hd=>by
        have hn:¬(d:ℕ)∣D := fun hh=>hd (Nat.mem_divisors.mpr ⟨hh,hD.ne'⟩)
        simp only [hn,false_and,if_false])]
      apply sum_congr rfl
      intro d hd
      have hp:0<d := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1 hD
      rw [dif_pos hp,dif_pos hp]
      simp only [PNat.mk_coe,(Nat.mem_divisors.mp hd).1,true_and,G]
      rfl

end ZhangLS.Spec
