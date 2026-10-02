import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Positivity
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset
open scoped Classical

noncomputable def lemma32IsolatedRootWeight {A : Type*}
    (f : A → A → ℝ) (j : Fin 4) (v : Fin 4 → A) : ℝ :=
  ∏ i : Fin 3, f (v j) (v (j.succAbove i))

lemma lemma32_isolated_root_weight_nonneg {A : Type*}
    (f : A → A → ℝ) (hf : ∀ a b, 0 ≤ f a b) (j : Fin 4) (v : Fin 4 → A) :
    0 ≤ lemma32IsolatedRootWeight f j v := by
  exact Finset.prod_nonneg fun i hi => hf _ _

lemma lemma32_isolated_root_weight_sum {A : Type*} [Fintype A]
    (f : A → A → ℝ) (j : Fin 4) :
    (∑ v : Fin 4 → A, lemma32IsolatedRootWeight f j v) =
      ∑ a : A, (∑ b : A, f a b)^3 := by
  let e := Fin.insertNthEquiv (fun _ : Fin 4 => A) j
  calc
    _ = ∑ p : A × (Fin 3 → A), lemma32IsolatedRootWeight f j (e p) :=
      (Fintype.sum_equiv e (fun p => lemma32IsolatedRootWeight f j (e p))
        (fun v => lemma32IsolatedRootWeight f j v) (fun p => rfl)).symm
    _ = ∑ a : A, ∑ w : Fin 3 → A, ∏ i : Fin 3, f a (w i) := by
      rw [Fintype.sum_prod_type]
      simp only [e, lemma32IsolatedRootWeight, Fin.insertNthEquiv,
        Equiv.coe_fn_mk, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      exact (Fintype.sum_pow (f a) 3).symm

lemma lemma32_isolated_root_weight_sum_bound {A : Type*} [Fintype A]
    (f : A → A → ℝ) (hf : ∀ a b, 0 ≤ f a b)
    (T : ℝ) (hrow : ∀ a, ∑ b : A, f a b ≤ T) (j : Fin 4) :
    (∑ v : Fin 4 → A, lemma32IsolatedRootWeight f j v) ≤ (Fintype.card A : ℝ)*T^3 := by
  rw [lemma32_isolated_root_weight_sum]
  calc
    _ ≤ ∑ _a : A, T^3 := by
      apply Finset.sum_le_sum
      intro a ha
      exact pow_le_pow_left₀ (Finset.sum_nonneg fun b hb => hf a b) (hrow a) 3
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end ZhangLS.Spec
