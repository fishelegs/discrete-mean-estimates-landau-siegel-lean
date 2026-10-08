import RemainderVanish
import Mathlib.Tactic.NormNum

noncomputable section

namespace PiWeightedColon.Regression

open Polynomial

/-- The sharp low-scale even branch is covered by the same all-scale theorem. -/
theorem remainder_scale_zero (A B : Line)
    (hA : A.natDegree ≤ 1) (hB : B.natDegree ≤ 1)
    (ht : (X : Line) ∣ A) (hc : u ^ 3 ∣ A + u * B) : A = 0 ∧ B = 0 := by
  simpa only [Nat.mul_zero, Nat.zero_add, zero_add, pow_zero, pow_one] using
    remainder_even 0 A B hA hB (by simpa using ht) (by simp)
      (by simp) (by simp) (by simpa using hc)

/-- A nonzero A=X passes the uncoupled scale-zero divisibility and degree tests. -/
theorem missing_even_coupling_counterexample :
    (X : Line).natDegree ≤ 1 ∧ (0 : Line).natDegree ≤ 1 ∧
    (X : Line) ∣ X ∧ u ^ 0 ∣ (X : Line) ∧ u ^ 0 ∣ (0 : Line) ∧
    ¬ ((X : Line) = 0 ∧ (0 : Line) = 0) := by
  simp [X_ne_zero]

/-- The degree bound is substantive: A=X*u^3, B=0 passes every even
divisibility condition at N=0, including the coupled one, and A is nonzero. -/
theorem missing_degree_counterexample :
    (X : Line) ∣ X * u ^ 3 ∧ u ^ 3 ∣ X * u ^ 3 ∧
    X * u ^ 3 ≠ 0 ∧ (X * u ^ 3).natDegree = 4 := by
  refine ⟨dvd_mul_right _ _, dvd_mul_left _ _, ?_, ?_⟩
  · exact mul_ne_zero X_ne_zero (pow_ne_zero _ u_monic.ne_zero)
  · simpa only [pow_one] using t_u_power_degree 1 3

/-- The odd branch's higher A order already makes nonzero A impossible. -/
theorem odd_A_degree_obstruction (N : ℕ) (A : Line)
    (hdeg : A.natDegree ≤ 4 * N + 1)
    (ht : (X : Line) ^ (N + 1) ∣ A) (hu : u ^ (3 * N + 1) ∣ A) : A = 0 := by
  exact eq_zero_of_dvd_of_natDegree_lt
    ((t_u_coprime.pow : IsCoprime ((X : Line) ^ (N + 1)) (u ^ (3 * N + 1))).mul_dvd ht hu)
    (by rw [t_u_power_degree]; omega)

end PiWeightedColon.Regression
