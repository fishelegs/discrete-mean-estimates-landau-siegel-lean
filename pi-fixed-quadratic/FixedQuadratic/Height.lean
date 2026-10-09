import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Int.Interval
import Mathlib.Tactic

open Polynomial
namespace FixedQuadratic

noncomputable def realQuadratic (a b c : ℤ) : Polynomial ℝ :=
  C (a : ℝ)*X^2 + C (b : ℝ)*X + C (c : ℝ)

theorem realQuadratic_ne_zero (a b c : ℤ) (ha : a ≠ 0) : realQuadratic a b c ≠ 0 := by
  intro h
  have hc := congrArg (fun P : Polynomial ℝ => P.coeff 2) h
  have he : (realQuadratic a b c).coeff 2 = (a : ℝ) := by
    simp only [realQuadratic, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
    norm_num
  rw [he, coeff_zero] at hc
  exact ha (Int.cast_eq_zero.mp hc)

theorem finite_realQuadratic_roots (a b c : ℤ) (ha : a ≠ 0) :
    Set.Finite {x : ℝ | (a : ℝ)*x^2+(b : ℝ)*x+(c : ℝ)=0} := by
  simpa [Polynomial.IsRoot, realQuadratic] using
    (Polynomial.finite_setOfPred_isRoot (realQuadratic_ne_zero a b c ha))

/-- A superset of all real roots with positive leading coefficient and
integer quadratic max height at most H; irreducibility and primitivity need
not be assumed for bounded-height finiteness. -/
noncomputable def boundedQuadraticRoots (H : ℕ) : Set ℝ :=
  ⋃ a ∈ Set.Icc (1 : ℤ) (H : ℤ),
  ⋃ b ∈ Set.Icc (-(H : ℤ)) (H : ℤ),
  ⋃ c ∈ Set.Icc (-(H : ℤ)) (H : ℤ),
    {x | (a : ℝ)*x^2+(b : ℝ)*x+(c : ℝ)=0}

theorem finite_boundedQuadraticRoots (H : ℕ) : (boundedQuadraticRoots H).Finite := by
  unfold boundedQuadraticRoots
  apply (Set.finite_Icc _ _).biUnion
  intro a ha
  apply (Set.finite_Icc _ _).biUnion
  intro b hb
  apply (Set.finite_Icc _ _).biUnion
  intro c hc
  exact finite_realQuadratic_roots a b c (by have := ha.1; omega)

theorem mem_boundedQuadraticRoots (H : ℕ) (a b c : ℤ) (x : ℝ)
    (ha : 1 ≤ a) (haH : a ≤ (H : ℤ)) (hb : |b| ≤ (H : ℤ)) (hc : |c| ≤ (H : ℤ))
    (hroot : (a : ℝ)*x^2+(b : ℝ)*x+(c : ℝ)=0) : x ∈ boundedQuadraticRoots H := by
  simp only [boundedQuadraticRoots, Set.mem_iUnion]
  exact ⟨a, ⟨ha,haH⟩, b, abs_le.mp hb, c, abs_le.mp hc, hroot⟩

/-- Infinite quadratic sets cannot fit inside any fixed coefficient box. -/
theorem infinite_escape_bounded_height (S : Set ℝ) (hS : S.Infinite) (H : ℕ) :
    ∃ x ∈ S, x ∉ boundedQuadraticRoots H :=
  hS.exists_notMem_finite (finite_boundedQuadraticRoots H)

/-- An actual height function with the coefficient-box property is unbounded
on every infinite set. This makes the selection input precise. -/
theorem height_unbounded_of_infinite (S : Set ℝ) (height : ℝ → ℕ)
    (hS : S.Infinite)
    (hbox : ∀ x ∈ S, ∀ H, height x ≤ H → x ∈ boundedQuadraticRoots H) :
    ∀ H, ∃ x ∈ S, H < height x := by
  intro H
  obtain ⟨x,hx,hnot⟩ := infinite_escape_bounded_height S hS H
  exact ⟨x,hx,lt_of_not_ge (fun h => hnot (hbox x hx H h))⟩

end FixedQuadratic
