import ZhangLS.Spec.PositiveGcdReindex

/-! Exact positive gcd sums in the source order d,k,l. Joint convergence is
used before any exchange. The long coprimality restriction stays literal. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open scoped Classical
set_option maxHeartbeats 2000000

/-- The genuine gcd series is summable whenever the original positive pair
series is summable. -/
theorem positiveGcd_summable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (F : ℕ+×ℕ+ → E) (hF : Summable F) :
    Summable (fun i : positiveGcdIndex => F (positiveGcdLift i)) :=
  positiveGcdEquiv.summable_iff.mpr hF

/-- For each genuine common divisor d, zero extension of the coprime pair
fiber is summable. -/
theorem positiveGcd_filtered_pair_summable {E : Type*}
    [NormedAddCommGroup E] [CompleteSpace E]
    (F : ℕ+×ℕ+ → E) (hF : Summable F) (d : ℕ+) :
    Summable (fun lk : ℕ+×ℕ+ =>
      if Nat.Coprime (lk.1 : ℕ) (lk.2 : ℕ) then F (d*lk.1,d*lk.2) else 0) := by
  have hs := (positiveGcd_summable F hF).sigma_factor d
  change Summable (fun lk : {lk : ℕ+×ℕ+ // Nat.Coprime (lk.1 : ℕ) (lk.2 : ℕ)} => F (d*lk.val.1,d*lk.val.2)) at hs
  have ht := (summable_subtype_iff_indicator (s := {lk : ℕ+×ℕ+ | Nat.Coprime (lk.1 : ℕ) (lk.2 : ℕ)})
    (f := fun lk : ℕ+×ℕ+ => F (d*lk.1,d*lk.2))).mp hs
  exact ht.congr (fun lk => by simp only [Set.indicator_apply,Set.mem_setOf_eq])

/-- The literal d,k,l source order; no condition is silently erased. -/
theorem positiveGcd_filtered_nested_tsum {E : Type*}
    [NormedAddCommGroup E] [CompleteSpace E]
    (F : ℕ+×ℕ+ → E) (hF : Summable F) :
    (∑'mn : ℕ+×ℕ+, F mn)=
      ∑'d : ℕ+, ∑'k : ℕ+, ∑'l : ℕ+,
        if Nat.Coprime (l : ℕ) (k : ℕ) then F (d*l,d*k) else 0 := by
  rw [positiveGcd_tsum_reindex, (positiveGcd_summable F hF).tsum_sigma]
  apply tsum_congr
  intro d
  have ht := tsum_subtype {lk : ℕ+×ℕ+ | Nat.Coprime (lk.1 : ℕ) (lk.2 : ℕ)}
    (fun lk : ℕ+×ℕ+ => F (d*lk.1,d*lk.2))
  simp only [Set.indicator,Set.mem_setOf_eq] at ht
  exact ht.trans <| (positiveGcd_filtered_pair_summable F hF d).tsum_prod.trans
    (positiveGcd_filtered_pair_summable F hF d).tsum_comm.symm

end ZhangLS.Spec
