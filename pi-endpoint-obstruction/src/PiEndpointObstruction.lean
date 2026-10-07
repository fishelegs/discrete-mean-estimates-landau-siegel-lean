import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# A small algebraic endpoint obstruction and a conditional arithmetic criterion

This file does not prove bad approximability of pi. It proves:

* the incompatibility of the original elementary endpoint parameter inequalities;
* an integer-determinant estimate;
* a quadratic approximation lower bound, CONDITIONAL on a uniform independent
  companion construction, or on a uniform two-independent-approximants construction.

Neither uniform construction is supplied, for pi or for any other real number.
The stronger finite-dimensional analytic no-go in the independent research report
is not formalized here. No analytic determinant theorem is imported.
-/

set_option autoImplicit false

namespace PiEndpointObstruction

/-- The elementary parameter gap is strictly negative whenever `A^2 < theta`.
No interval assumption on `theta` is needed. -/
theorem endpoint_gap_lt (A theta : ℝ) (hSquare : A ^ 2 < theta) :
    2 * (A - theta) < 1 - theta := by
  nlinarith [sq_nonneg (A - 1)]

/-- Even the corresponding two weak inequalities force the boundary point `(1,1)`. -/
theorem weak_endpoint_boundary (A theta : ℝ) (hSquare : A ^ 2 ≤ theta)
    (hGap : 1 - theta ≤ 2 * (A - theta)) : A = 1 ∧ theta = 1 := by
  have hSq : (A - 1) ^ 2 = 0 := by nlinarith [sq_nonneg (A - 1)]
  have hA : A = 1 := sub_eq_zero.mp (sq_eq_zero_iff.mp hSq)
  constructor
  · exact hA
  · rw [hA] at hSquare hGap
    nlinarith

/-- The original strict endpoint parameter requirements are inconsistent.
This is an elementary algebraic obstruction, not the full analytic no-go theorem. -/
theorem no_original_endpoint_parameters :
    ¬ ∃ A theta : ℝ, 0 < theta ∧ theta < 1 ∧
      A ^ 2 < theta ∧ 1 - theta < 2 * (A - theta) := by
  rintro ⟨A, theta, _, _, hSquare, hGap⟩
  exact (not_lt_of_ge (le_of_lt (endpoint_gap_lt A theta hSquare))) hGap

/-- A nonzero integer determinant has real absolute value at least one. -/
theorem one_le_abs_integer_determinant (p q P Q : ℤ)
    (hdet : p * Q - q * P ≠ 0) :
    (1 : ℝ) ≤ |(p : ℝ) * (Q : ℝ) - (q : ℝ) * (P : ℝ)| := by
  have hint : (1 : ℤ) ≤ |p * Q - q * P| := Int.one_le_abs hdet
  exact_mod_cast hint

/-- Two approximation errors bound their integer determinant. -/
theorem determinant_error_bound (alpha : ℝ) (p q P Q : ℤ)
    (hq : 0 < q) (hQ : 0 ≤ Q) :
    |(p : ℝ) * (Q : ℝ) - (q : ℝ) * (P : ℝ)| ≤
      (Q : ℝ) * |(q : ℝ) * alpha - (p : ℝ)| +
      (q : ℝ) * |(Q : ℝ) * alpha - (P : ℝ)| := by
  have hqr : 0 < (q : ℝ) := by exact_mod_cast hq
  have hQr : 0 ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hid : (p : ℝ) * (Q : ℝ) - (q : ℝ) * (P : ℝ) =
      (q : ℝ) * ((Q : ℝ) * alpha - (P : ℝ)) -
      (Q : ℝ) * ((q : ℝ) * alpha - (p : ℝ)) := by ring
  rw [hid]
  calc
    _ ≤ |(q : ℝ) * ((Q : ℝ) * alpha - (P : ℝ))| +
        |(Q : ℝ) * ((q : ℝ) * alpha - (p : ℝ))| := by
      simpa using abs_sub_le
        ((q : ℝ) * ((Q : ℝ) * alpha - (P : ℝ))) 0
        ((Q : ℝ) * ((q : ℝ) * alpha - (p : ℝ)))
    _ = _ := by rw [abs_mul, abs_mul, abs_of_pos hqr, abs_of_nonneg hQr]; ring

/-- A single independent companion at the same scale yields a lower bound.
The error hypothesis is `q * |Q*alpha-P| ≤ 1/2`, equivalently
`|Q*alpha-P| ≤ 1/(2*q)` because `q > 0`. -/
theorem scaled_lower_bound_of_companion (alpha B : ℝ) (p q P Q : ℤ)
    (hB : 0 < B) (hq : 0 < q) (hQ : 0 ≤ Q)
    (hsize : (Q : ℝ) ≤ B * (q : ℝ))
    (herror : (q : ℝ) * |(Q : ℝ) * alpha - (P : ℝ)| ≤ 1 / 2)
    (hdet : p * Q - q * P ≠ 0) :
    1 / (2 * B) ≤ (q : ℝ) * |(q : ℝ) * alpha - (p : ℝ)| := by
  have hlow := one_le_abs_integer_determinant p q P Q hdet
  have hupp := determinant_error_bound alpha p q P Q hq hQ
  have hsize' := mul_le_mul_of_nonneg_right hsize
    (abs_nonneg ((q : ℝ) * alpha - (p : ℝ)))
  apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hB)).2
  nlinarith

/-- Relates the linear error to the rational approximation error. -/
theorem scaled_error_identity (alpha : ℝ) (p q : ℤ) (hq : 0 < q) :
    (q : ℝ) * |alpha - (p : ℝ) / (q : ℝ)| =
      |(q : ℝ) * alpha - (p : ℝ)| := by
  have hqr : 0 < (q : ℝ) := by exact_mod_cast hq
  calc
    _ = |(q : ℝ)| * |alpha - (p : ℝ) / (q : ℝ)| := by rw [abs_of_pos hqr]
    _ = |(q : ℝ) * (alpha - (p : ℝ) / (q : ℝ))| := (abs_mul _ _).symm
    _ = _ := by
      congr 1
      field_simp [ne_of_gt hqr]

/-- The explicit `c/q^2` bound obtained from one independent companion. -/
theorem quadratic_lower_bound_of_companion (alpha B : ℝ) (p q P Q : ℤ)
    (hB : 0 < B) (hq : 0 < q) (hQ : 0 ≤ Q)
    (hsize : (Q : ℝ) ≤ B * (q : ℝ))
    (herror : (q : ℝ) * |(Q : ℝ) * alpha - (P : ℝ)| ≤ 1 / 2)
    (hdet : p * Q - q * P ≠ 0) :
    (1 / (2 * B)) / (q : ℝ) ^ 2 ≤ |alpha - (p : ℝ) / (q : ℝ)| := by
  have hqr : 0 < (q : ℝ) := by exact_mod_cast hq
  have hscaled := scaled_lower_bound_of_companion alpha B p q P Q
    hB hq hQ hsize herror hdet
  have hid := scaled_error_identity alpha p q hq
  rw [← hid] at hscaled
  apply (div_le_iff₀ (sq_pos_of_pos hqr)).2
  nlinarith

/-- UNPROVED CONSTRUCTION HYPOTHESIS: a uniform independent companion exists
for every integer numerator and positive integer denominator, at a fixed `B`.
This definition does not assert that the hypothesis holds for any `alpha`. -/
def UniformCompanions (alpha B : ℝ) : Prop :=
  ∀ p q : ℤ, 0 < q → ∃ P Q : ℤ,
    0 ≤ Q ∧ (Q : ℝ) ≤ B * (q : ℝ) ∧
    (q : ℝ) * |(Q : ℝ) * alpha - (P : ℝ)| ≤ 1 / 2 ∧
    p * Q - q * P ≠ 0

/-- An explicitly conditional criterion. The hard uniform construction remains
an assumption, and is not supplied by this theorem. -/
theorem quadratic_lower_bound_of_uniform_companions (alpha B : ℝ)
    (hB : 0 < B) (hconstruction : UniformCompanions alpha B) :
    ∀ p q : ℤ, 0 < q →
      (1 / (2 * B)) / (q : ℝ) ^ 2 ≤ |alpha - (p : ℝ) / (q : ℝ)| := by
  intro p q hq
  obtain ⟨P, Q, hQ, hsize, herror, hdet⟩ := hconstruction p q hq
  exact quadratic_lower_bound_of_companion alpha B p q P Q hB hq hQ hsize herror hdet

/-- If two integer pairs are independent, at least one is independent of a pair
whose denominator is nonzero. -/
theorem one_companion_independent (p q P1 Q1 P2 Q2 : ℤ) (hq : q ≠ 0)
    (hind : P1 * Q2 - P2 * Q1 ≠ 0) :
    p * Q1 - q * P1 ≠ 0 ∨ p * Q2 - q * P2 ≠ 0 := by
  by_cases h1 : p * Q1 - q * P1 ≠ 0
  · exact Or.inl h1
  · right
    intro h2
    have h1eq : p * Q1 - q * P1 = 0 := not_ne_iff.mp h1
    have hid : q * (P1 * Q2 - P2 * Q1) =
        Q1 * (p * Q2 - q * P2) - Q2 * (p * Q1 - q * P1) := by ring
    rw [h1eq, h2, mul_zero, mul_zero, sub_self] at hid
    exact hind ((mul_eq_zero.mp hid).resolve_left hq)

/-- UNPROVED CONSTRUCTION HYPOTHESIS at every positive integer scale.
Both denominators are positive, at most `B*q`; both linear errors are at most
`1/(2*q)`; the pairs have nonzero determinant. No construction is given here. -/
def UniformIndependentApproximants (alpha B : ℝ) : Prop :=
  ∀ q : ℤ, 0 < q → ∃ P1 Q1 P2 Q2 : ℤ,
    0 < Q1 ∧ 0 < Q2 ∧
    (Q1 : ℝ) ≤ B * (q : ℝ) ∧ (Q2 : ℝ) ≤ B * (q : ℝ) ∧
    (q : ℝ) * |(Q1 : ℝ) * alpha - (P1 : ℝ)| ≤ 1 / 2 ∧
    (q : ℝ) * |(Q2 : ℝ) * alpha - (P2 : ℝ)| ≤ 1 / 2 ∧
    P1 * Q2 - P2 * Q1 ≠ 0

/-- Conditional passage from two independent approximants to an independent
companion for any specified rational input. -/
theorem companions_of_independent_approximants (alpha B : ℝ)
    (hconstruction : UniformIndependentApproximants alpha B) :
    UniformCompanions alpha B := by
  intro p q hq
  obtain ⟨P1, Q1, P2, Q2, hQ1, hQ2, hs1, hs2, he1, he2, hind⟩ := hconstruction q hq
  rcases one_companion_independent p q P1 Q1 P2 Q2 (ne_of_gt hq) hind with h1 | h2
  · exact ⟨P1, Q1, le_of_lt hQ1, hs1, he1, h1⟩
  · exact ⟨P2, Q2, le_of_lt hQ2, hs2, he2, h2⟩

/-- A conditional bad-approximability criterion with the explicit positive
constant `c = 1/(2*B)`. The uniform construction is an assumption, not a conclusion.
In particular this theorem does not instantiate `alpha` with pi. -/
theorem positive_quadratic_lower_bound_of_two_approximants (alpha B : ℝ)
    (hB : 0 < B) (hconstruction : UniformIndependentApproximants alpha B) :
    ∃ c : ℝ, 0 < c ∧ ∀ p q : ℤ, 0 < q →
      c / (q : ℝ) ^ 2 ≤ |alpha - (p : ℝ) / (q : ℝ)| := by
  refine ⟨1 / (2 * B), div_pos (by norm_num) (mul_pos (by norm_num) hB), ?_⟩
  exact quadratic_lower_bound_of_uniform_companions alpha B hB
    (companions_of_independent_approximants alpha B hconstruction)

end PiEndpointObstruction
