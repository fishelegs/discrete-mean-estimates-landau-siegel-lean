import FixedQuadratic.Selection
import OAI.NumberTheory.PiExponent.Approximation.WeightSeparation

namespace FixedQuadratic.ParameterPort
open scoped BigOperators
open OAI

/-- Actual primitive heights supply normalized separated growth for every fixed
finite packet and every previously fixed separation factor. -/
theorem exists_normalized_centers (S : Set ℝ) (hS : S.Infinite)
    (hdegree : ∀ x ∈ S, (minpoly ℚ x).natDegree = 2) (X D : ℝ) :
    ∃ β : ℕ → ℝ, ∃ x : ℕ → ℝ,
      (∀ n, β n ∈ S ∧ β n ≠ 0 ∧ 2 ≤ primitiveMinpolyHeight (β n)) ∧
      x 0 = 1 ∧
      (∀ n, x (n+1) = (Nat.ceil (Real.log (primitiveMinpolyHeight (β n) : ℝ)) : ℝ)) ∧
      (∀ n, 1 ≤ x n) ∧ (∀ n, X < x (n+1)) ∧
      (∀ i, 0 < i → D*(∏ j ∈ Finset.range i, x j) < x i) := by
  classical
  obtain ⟨β,hβ⟩ := exists_successive_primitive_centers S hS hdegree
    (fun L => max X (D*L.prod))
  let w : ℕ → ℝ := fun n => (Nat.ceil (Real.log (primitiveMinpolyHeight (β n) : ℝ)) : ℝ)
  let x : ℕ → ℝ := fun i => Nat.casesOn i 1 w
  have hx0 : x 0 = 1 := rfl
  have hxs (n : ℕ) : x (n+1) = w n := rfl
  have hp (n : ℕ) : ((List.range n).map w).prod = ∏ j ∈ Finset.range n, w j := by
    induction n with
    | zero => simp
    | succ n ih => simp only [List.range_succ, List.map_append, List.map_singleton,
        List.prod_append, List.prod_singleton, Finset.prod_range_succ, ih]
  have hprev (n : ℕ) : (∏ j ∈ Finset.range (n+1), x j) = ∏ j ∈ Finset.range n, w j := by
    rw [Finset.prod_range_succ',hx0,mul_one]
  have ht (n : ℕ) : max X (D*(∏ j ∈ Finset.range n, w j)) < w n := by
    have hh := (hβ n).2.2.2.2
    simpa only [w, List.map_reverse, List.prod_reverse, hp] using hh
  refine ⟨β,x,(fun n => ⟨(hβ n).1,(hβ n).2.1,(hβ n).2.2.1⟩),hx0,
    (fun n => hxs n),?_,?_,?_⟩
  · intro n
    cases n with
    | zero => simp only [hx0,le_refl]
    | succ n =>
      rw [hxs]
      dsimp [w]
      exact_mod_cast (hβ n).2.2.2.1
  · intro n
    exact (le_max_left _ _).trans_lt (ht n)
  · intro i hi
    cases i with
    | zero => omega
    | succ n => rw [hprev,hxs]; exact (le_max_right _ _).trans_lt (ht n)

end FixedQuadratic.ParameterPort
