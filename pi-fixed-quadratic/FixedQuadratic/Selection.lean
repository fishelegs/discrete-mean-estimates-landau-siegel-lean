import FixedQuadratic.PrimitiveHeight
import FixedQuadratic.Weights

namespace FixedQuadratic

set_option maxHeartbeats 1000000

/-- Degree-exactly-two is enough to exclude the zero center. -/
theorem degree_two_ne_zero (x : ℝ) (hx : (minpoly ℚ x).natDegree = 2) : x ≠ 0 := by
  intro hz
  subst x
  simp only [minpoly.zero, Polynomial.natDegree_X] at hx
  omega

/-- No unbounded-height interface is assumed: it follows from the actual
primitive minpoly height on an infinite set of quadratic real numbers. -/
theorem exists_large_primitive_log_height (S : Set ℝ) (hS : S.Infinite)
    (hdegree : ∀ x ∈ S, (minpoly ℚ x).natDegree = 2) (T : ℝ) :
    ∃ x ∈ S, x ≠ 0 ∧ 2 ≤ primitiveMinpolyHeight x ∧
      T < Real.log (primitiveMinpolyHeight x : ℝ) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max 2 (Real.exp T))
  obtain ⟨x, hx, hh⟩ := primitiveMinpolyHeight_unbounded S hS hdegree n
  have hcast : (n : ℝ) < primitiveMinpolyHeight x := by exact_mod_cast hh
  have hH : (2 : ℝ) < primitiveMinpolyHeight x :=
    lt_trans (lt_of_le_of_lt (le_max_left _ _) hn) hcast
  have he : Real.exp T < (primitiveMinpolyHeight x : ℝ) :=
    lt_trans (lt_of_le_of_lt (le_max_right _ _) hn) hcast
  have hl := Real.log_lt_log (Real.exp_pos T) he
  refine ⟨x, hx, degree_two_ne_zero x (hdegree x hx), ?_, ?_⟩
  · exact_mod_cast hH.le
  · simpa only [Real.log_exp] using hl

/-- A center-independent successive threshold may be any function of the
previous weights. The packet is chosen only from the fixed exceptional set S. -/
theorem exists_successive_primitive_centers (S : Set ℝ) (hS : S.Infinite)
    (hdegree : ∀ x ∈ S, (minpoly ℚ x).natDegree = 2) (T : List ℝ → ℝ) :
    ∃ β : ℕ → ℝ, ∀ n, β n ∈ S ∧ β n ≠ 0 ∧ 2 ≤ primitiveMinpolyHeight (β n) ∧
      1 ≤ Nat.ceil (Real.log (primitiveMinpolyHeight (β n) : ℝ)) ∧
      T (((List.range n).reverse).map
        (fun i => (Nat.ceil (Real.log (primitiveMinpolyHeight (β i) : ℝ)) : ℝ))) <
        (Nat.ceil (Real.log (primitiveMinpolyHeight (β n) : ℝ)) : ℝ) := by
  classical
  let wt : ℝ → ℝ := fun x => (Nat.ceil (Real.log (primitiveMinpolyHeight x : ℝ)) : ℝ)
  let Good : ℝ → Prop := fun x => x ∈ S ∧ x ≠ 0 ∧ 2 ≤ primitiveMinpolyHeight x ∧
    1 ≤ Nat.ceil (Real.log (primitiveMinpolyHeight x : ℝ))
  have hex (L : List ℝ) : ∃ x, Good x ∧ T (L.map wt) < wt x := by
    obtain ⟨x, hx, hn, hH, hl⟩ := exists_large_primitive_log_height S hS hdegree
      (max 1 (T (L.map wt)))
    have hc := Nat.le_ceil (Real.log (primitiveMinpolyHeight x : ℝ))
    have h1 : (1 : ℝ) < wt x := lt_of_le_of_lt (le_max_left _ _) (hl.trans_le hc)
    refine ⟨x, ⟨hx, hn, hH, ?_⟩, ?_⟩
    · dsimp [wt] at h1
      exact_mod_cast h1.le
    · exact lt_of_le_of_lt (le_max_right _ _) (hl.trans_le hc)
  let next : List ℝ → ℝ := fun L => (hex L).choose
  have hnext (L : List ℝ) : Good (next L) ∧ T (L.map wt) < wt (next L) :=
    (hex L).choose_spec
  let hist : ℕ → List ℝ := Nat.rec [] (fun _ L => next L :: L)
  let β : ℕ → ℝ := fun n => next (hist n)
  have hhist (n : ℕ) : hist n = (List.range n).reverse.map β := by
    induction n with
    | zero => rfl
    | succ n ih =>
      change β n :: hist n = (List.range (n+1)).reverse.map β
      rw [ih]
      simp [List.range_succ, List.reverse_append]
  refine ⟨β, fun n => ?_⟩
  have hg : Good (β n) := (hnext (hist n)).1
  refine ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2, ?_⟩
  have hb := (hnext (hist n)).2
  have hmap : (hist n).map wt = (List.range n).reverse.map (wt ∘ β) := by
    rw [hhist, List.map_map]
  rw [hmap] at hb
  exact hb

end FixedQuadratic
