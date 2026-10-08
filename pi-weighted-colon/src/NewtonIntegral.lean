import MatrixEntries
import Mathlib.Algebra.Polynomial.Div

noncomputable section

namespace PiWeightedColon

open Polynomial
open scoped BigOperators

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Iterated synthetic division by monic linear polynomials. This definition
is over the original coefficient ring and does not divide by node differences. -/
def newtonQuotient (p : R[X]) (nodes : ℕ → R) : ℕ → R[X]
  | 0 => p
  | k + 1 => newtonQuotient p nodes k /ₘ (X - C (nodes k))

def newtonCoefficient (p : R[X]) (nodes : ℕ → R) (k : ℕ) : R :=
  (newtonQuotient p nodes k).eval (nodes k)

def newtonBasis (nodes : ℕ → R) (k : ℕ) : R[X] :=
  ∏ i ∈ Finset.range k, (X - C (nodes i))

theorem newtonBasis_succ (nodes : ℕ → R) (k : ℕ) :
    newtonBasis nodes (k + 1) = newtonBasis nodes k * (X - C (nodes k)) := by
  simp [newtonBasis, Finset.prod_range_succ]

theorem newton_step (p : R[X]) (nodes : ℕ → R) (k : ℕ) :
    newtonQuotient p nodes k = C (newtonCoefficient p nodes k) +
      (X - C (nodes k)) * newtonQuotient p nodes (k + 1) := by
  have h := (modByMonic_add_div (newtonQuotient p nodes k) (X - C (nodes k))).symm
  rw [modByMonic_X_sub_C_eq_C_eval] at h
  exact h

/-- Exact finite Newton expansion, with an explicit remainder. -/
theorem newton_expansion (p : R[X]) (nodes : ℕ → R) (n : ℕ) :
    p = (∑ k ∈ Finset.range n, C (newtonCoefficient p nodes k) * newtonBasis nodes k) +
      newtonBasis nodes n * newtonQuotient p nodes n := by
  induction n with
  | zero => simp [newtonBasis, newtonQuotient]
  | succ n ih =>
    rw [Finset.sum_range_succ, newtonBasis_succ]
    nth_rw 1 [ih]
    rw [newton_step p nodes n]
    ring

theorem newtonBasis_eval (nodes : ℕ → R) (k : ℕ) (x : R) :
    (newtonBasis nodes k).eval x = ∏ i ∈ Finset.range k, (x - nodes i) := by
  simp [newtonBasis, eval_prod]

theorem newtonBasis_eval_zero (nodes : ℕ → R) (j k : ℕ) (hj : j < k) :
    (newtonBasis nodes k).eval (nodes j) = 0 := by
  rw [newtonBasis_eval]
  exact Finset.prod_eq_zero (Finset.mem_range.mpr hj) (sub_self _)

/-- The evaluation matrix factors through the integral Newton coefficients.
The factor at column j has zero entries for k>j and the stated product for k=j. -/
theorem newton_evaluation (p : R[X]) (nodes : ℕ → R) (j : ℕ) :
    p.eval (nodes j) = ∑ k ∈ Finset.range (j + 1),
      newtonCoefficient p nodes k * ∏ i ∈ Finset.range k, (nodes j - nodes i) := by
  have h := congrArg (fun q : R[X] => q.eval (nodes j)) (newton_expansion p nodes (j + 1))
  simpa [eval_finsetSum, eval_mul, newtonBasis_eval,
    newtonBasis_eval_zero nodes j (j + 1) (by omega)] using h

theorem newtonQuotient_map (f : R →+* S) (p : R[X]) (nodes : ℕ → R) (k : ℕ) :
    (newtonQuotient p nodes k).map f =
      newtonQuotient (p.map f) (fun i => f (nodes i)) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [newtonQuotient]
    rw [map_divByMonic f (monic_X_sub_C _), ih]
    simp

theorem newtonCoefficient_map (f : R →+* S) (p : R[X]) (nodes : ℕ → R) (k : ℕ) :
    f (newtonCoefficient p nodes k) =
      newtonCoefficient (p.map f) (fun i => f (nodes i)) k := by
  unfold newtonCoefficient
  rw [← eval_map_apply, newtonQuotient_map]

theorem shifted_division_coeff (p : R[X]) (a : R) (k : ℕ) :
    ((p /ₘ (X - C a)).comp (X + C a)).coeff k =
      (p.comp (X + C a)).coeff (k + 1) := by
  have h : p = C (p.eval a) + (X - C a) * (p /ₘ (X - C a)) := by
    have h := (modByMonic_add_div p (X - C a)).symm
    rw [modByMonic_X_sub_C_eq_C_eval] at h
    exact h
  have hc := congrArg (fun q : R[X] => (q.comp (X + C a)).coeff (k + 1)) h
  simpa [add_comp, mul_comp, sub_comp, X_comp, C_comp, coeff_X_mul] using hc.symm

theorem newtonQuotient_constant_coeff (p : R[X]) (a : R) (k n : ℕ) :
    ((newtonQuotient p (fun _ => a) k).comp (X + C a)).coeff n =
      (p.comp (X + C a)).coeff (n + k) := by
  induction k generalizing n with
  | zero => simp [newtonQuotient]
  | succ k ih =>
    rw [newtonQuotient, shifted_division_coeff, ih]
    congr 1
    omega

/-- When all reduced nodes coincide, integral Newton coefficients reduce to
the Hasse coefficients at that point. No distinctness is needed in the target. -/
theorem newtonCoefficient_collision (f : R →+* S) (p : R[X]) (nodes : ℕ → R)
    (a : S) (hnodes : ∀ i, f (nodes i) = a) (k : ℕ) :
    f (newtonCoefficient p nodes k) = (p.map f |>.comp (X + C a)).coeff k := by
  rw [newtonCoefficient_map]
  have he : (fun i => f (nodes i)) = (fun _ => a) := funext hnodes
  rw [he, newtonCoefficient]
  have h0 : ∀ q : S[X], (q.comp (X + C a)).coeff 0 = q.eval a := by
    intro q
    rw [coeff_zero_eq_eval_zero, eval_comp]
    simp
  rw [← h0, newtonQuotient_constant_coeff]
  simp

end PiWeightedColon
