import Mathlib.Data.PNat.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-! # Exact positive-index gcd reindexing

The global pair (m,n) is put in bijection with d>0 and l,k>0 satisfying
(l,k)=1, via m=dl and n=dk. Nested infinite sums are rearranged only under
an explicit absolute-summability hypothesis; the bijection alone is separate.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec

abbrev positiveGcdIndex : Type :=
  Σd:ℕ+, {lk:ℕ+×ℕ+ // Nat.Coprime (lk.1:ℕ) (lk.2:ℕ)}

def positiveGcdLift (i:positiveGcdIndex) : ℕ+×ℕ+ := (i.1*i.2.val.1,i.1*i.2.val.2)

lemma positiveGcd_lift_gcd (i:positiveGcdIndex) :
    Nat.gcd ((positiveGcdLift i).1:ℕ) ((positiveGcdLift i).2:ℕ)=(i.1:ℕ) := by
  rcases i with ⟨d,⟨⟨l,k⟩,hc⟩⟩
  change Nat.gcd ((d:ℕ)*(l:ℕ)) ((d:ℕ)*(k:ℕ))=(d:ℕ)
  rw [Nat.gcd_mul_left,hc.gcd_eq_one,mul_one]

theorem positiveGcd_lift_injective : Function.Injective positiveGcdLift := by
  intro x y he
  have hd : x.1=y.1 := by
    apply PNat.eq
    rw [←positiveGcd_lift_gcd x,←positiveGcd_lift_gcd y,he]
  rcases x with ⟨d,⟨⟨l,k⟩,hc⟩⟩
  rcases y with ⟨e,⟨⟨l',k'⟩,hc'⟩⟩
  change d=e at hd
  subst e
  change (d*l,d*k)=(d*l',d*k') at he
  have hl : l=l' := mul_left_cancel (Prod.mk.inj he).1
  have hk : k=k' := mul_left_cancel (Prod.mk.inj he).2
  subst l'
  subst k'
  rfl

theorem positiveGcd_lift_surjective : Function.Surjective positiveGcdLift := by
  intro mn
  rcases mn with ⟨m,n⟩
  let g := Nat.gcd (m:ℕ) (n:ℕ)
  have hg : 0<g := Nat.gcd_pos_of_pos_left _ m.property
  have hmdiv : g∣(m:ℕ) := Nat.gcd_dvd_left _ _
  have hndiv : g∣(n:ℕ) := Nat.gcd_dvd_right _ _
  let d:ℕ+ := ⟨g,hg⟩
  let l:ℕ+ := ⟨(m:ℕ)/g,Nat.div_pos (Nat.le_of_dvd m.property hmdiv) hg⟩
  let k:ℕ+ := ⟨(n:ℕ)/g,Nat.div_pos (Nat.le_of_dvd n.property hndiv) hg⟩
  have hc : Nat.Coprime (l:ℕ) (k:ℕ) := Nat.gcd_div_gcd_div_gcd_of_pos_left m.property
  refine ⟨⟨d,⟨(l,k),hc⟩⟩,Prod.ext ?_ ?_⟩
  · apply PNat.eq
    exact Nat.mul_div_cancel' hmdiv
  · apply PNat.eq
    exact Nat.mul_div_cancel' hndiv

noncomputable def positiveGcdEquiv : positiveGcdIndex ≃ (ℕ+×ℕ+) :=
  Equiv.ofBijective positiveGcdLift ⟨positiveGcd_lift_injective,positiveGcd_lift_surjective⟩

/-- Global-index equality from the actual bijection. This does not on its
own justify replacing either side by nested infinite sums. -/
theorem positiveGcd_tsum_reindex {A:Type*} [NormedAddCommGroup A] [CompleteSpace A]
    (F:ℕ+×ℕ+→A) :
    (∑'mn:ℕ+×ℕ+,F mn)=∑'i:positiveGcdIndex,F (positiveGcdLift i) := by
  exact (positiveGcdEquiv.tsum_eq F).symm

/-- The actual nested gcd decomposition, with summability checked before
interchanging either the product or sigma-indexed infinite sums. -/
theorem positiveGcd_nested_tsum {A:Type*} [NormedAddCommGroup A] [CompleteSpace A]
    (F:ℕ+×ℕ+→A) (hF:Summable F) :
    (∑'m:ℕ+,∑'n:ℕ+,F (m,n))=
      ∑'d:ℕ+,∑'lk:{lk:ℕ+×ℕ+ // Nat.Coprime (lk.1:ℕ) (lk.2:ℕ)},
        F (d*lk.val.1,d*lk.val.2) := by
  have hI : Summable (fun i:positiveGcdIndex=>F (positiveGcdLift i)) :=
    (positiveGcdEquiv.summable_iff).mpr hF
  calc
    _ = ∑'mn:ℕ+×ℕ+,F mn := hF.tsum_prod.symm
    _ = ∑'i:positiveGcdIndex,F (positiveGcdLift i) := positiveGcd_tsum_reindex F
    _ = _ := hI.tsum_sigma

/-- The argument of the actual Δ kernel keeps the full complementary
scale when the common gcd is canceled. -/
theorem positiveGcd_scaled_ratio (i:positiveGcdIndex) {q:ℝ} (hq:0<q) :
    ((positiveGcdLift i).1:ℝ)/(q*((positiveGcdLift i).2:ℝ))=
      (i.2.val.1:ℝ)/(q*(i.2.val.2:ℝ)) := by
  rcases i with ⟨d,⟨⟨l,k⟩,hc⟩⟩
  have hd : 0<(d:ℝ) := by exact_mod_cast d.property
  simp only [positiveGcdLift,PNat.mul_coe,Nat.cast_mul]
  field_simp

end ZhangLS.Spec
