import ZhangLS.Spec.FixedModulusGcdOriginalPhase

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open scoped Classical

/-- An ordinary positive-Nat sum with exactly the source coprimality filter
is the sigma sum over divisors and quotient units. -/
theorem fixedDCoprimeGcd_filtered_tsum {A : Type*} [NormedAddCommGroup A] [CompleteSpace A]
    (D k : ℕ) (F : ℕ+ → A) :
    (∑' l : ℕ+, if Nat.Coprime (l:ℕ) k then F l else 0) =
      ∑' i : fixedDCoprimeGcdIndex D k, F (i.1.val*i.2.val) := by
  have hs := tsum_subtype {l : ℕ+ | Nat.Coprime (l:ℕ) k} F
  simp only [Set.indicator_apply, Set.mem_setOf_eq] at hs
  rw [← hs]
  exact fixedDCoprimeGcd_tsum_reindex D k (fun l => F l.val)

/-- The literal nested source sum, using summability rather than silently
interchanging infinite sums. -/
theorem fixedDCoprimeGcd_filtered_nested_tsum {A : Type*}
    [NormedAddCommGroup A] [CompleteSpace A] (D k : ℕ) (F : ℕ+ → A)
    (hF : Summable (fun l : {l : ℕ+ // Nat.Coprime (l:ℕ) k} => F l.val)) :
    (∑' l : ℕ+, if Nat.Coprime (l:ℕ) k then F l else 0) =
      ∑' d : {d : ℕ+ // (d:ℕ) ∣ D ∧ Nat.Coprime (d:ℕ) k},
        ∑' l : {l : ℕ+ // Nat.Coprime (l:ℕ) ((D/(d.val:ℕ))*k)},
          F (d.val*l.val) := by
  have hI : Summable (fun i : fixedDCoprimeGcdIndex D k => F (i.1.val*i.2.val)) :=
    ((fixedDCoprimeGcdEquiv D k).summable_iff).mpr hF
  exact (fixedDCoprimeGcd_filtered_tsum D k F).trans hI.tsum_sigma

end ZhangLS.Spec
