import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic

noncomputable section

namespace PiWeightedColon

/-- A lower bound for every integer numerator and every positive integer denominator. -/
def ApproximationLowerBound (α κ : ℝ) : Prop :=
  ∀ p q : ℤ, 0 < q → κ / (q : ℝ) ^ 2 ≤ |α - (p : ℝ) / (q : ℝ)|

/-- Two independent integer approximants at every positive integer scale. -/
def HasApproximationPairs (α C η : ℝ) : Prop :=
  ∀ Q : ℤ, 0 < Q → ∃ a b c d : ℤ,
    1 ≤ b ∧ 1 ≤ d ∧ (b : ℝ) ≤ C * (Q : ℝ) ∧ (d : ℝ) ≤ C * (Q : ℝ) ∧
    a * d - b * c ≠ 0 ∧
    |(b : ℝ) * α - (a : ℝ)| ≤ η / (Q : ℝ) ∧
    |(d : ℝ) * α - (c : ℝ)| ≤ η / (Q : ℝ)

theorem integer_abs_gap (z : ℤ) (hz : z ≠ 0) : (1 : ℝ) ≤ |(z : ℝ)| := by
  have hi : (1 : ℤ) ≤ |z| := by
    have := abs_pos.mpr hz
    omega
  exact_mod_cast hi

theorem independent_pair_cross_nonzero (p q a b c d : ℤ) (hq : q ≠ 0)
    (hind : a * d - b * c ≠ 0) : b * p - a * q ≠ 0 ∨ d * p - c * q ≠ 0 := by
  by_cases h : b * p - a * q ≠ 0
  · exact Or.inl h
  · right
    intro h'
    have hz : b * p - a * q = 0 := not_ne_iff.mp h
    have he : q * (a * d - b * c) = 0 := by
      calc
        q * (a * d - b * c) = b * (d * p - c * q) - d * (b * p - a * q) := by ring
        _ = 0 := by rw [hz, h']; ring
    exact hind ((mul_eq_zero.mp he).resolve_left hq)

theorem one_approximant_lower_bound (α C η : ℝ) (hC : 0 < C)
    (p q a b : ℤ) (hq : 0 < q) (hb : 1 ≤ b)
    (hb_size : (b : ℝ) ≤ C * (q : ℝ))
    (herror : |(b : ℝ) * α - (a : ℝ)| ≤ η / (q : ℝ))
    (hcross : b * p - a * q ≠ 0) :
    ((1 - η) / C) / (q : ℝ) ^ 2 ≤ |α - (p : ℝ) / (q : ℝ)| := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hbr : (0 : ℝ) < b := by exact_mod_cast (show (0 : ℤ) < b by omega)
  have hq0 : (q : ℝ) ≠ 0 := ne_of_gt hqr
  have hgap := integer_abs_gap (b * p - a * q) hcross
  have hid : ((b * p - a * q : ℤ) : ℝ) =
      (q : ℝ) * ((b : ℝ) * α - a) - (b : ℝ) * ((q : ℝ) * α - p) := by
    push_cast
    ring
  have hlinear : |(q : ℝ) * α - p| = (q : ℝ) * |α - (p : ℝ) / q| := by
    have he : (q : ℝ) * α - p = (q : ℝ) * (α - (p : ℝ) / q) := by field_simp
    rw [he, abs_mul, abs_of_pos hqr]
  have hbound : (1 : ℝ) ≤ η + C * (q : ℝ) ^ 2 * |α - (p : ℝ) / q| := by
    calc
      1 ≤ |((b * p - a * q : ℤ) : ℝ)| := hgap
      _ = |(q : ℝ) * ((b : ℝ) * α - a) - (b : ℝ) * ((q : ℝ) * α - p)| := by rw [hid]
      _ ≤ |(q : ℝ) * ((b : ℝ) * α - a)| + |(b : ℝ) * ((q : ℝ) * α - p)| := abs_sub _ _
      _ = (q : ℝ) * |(b : ℝ) * α - a| + (b : ℝ) * |(q : ℝ) * α - p| := by
        rw [abs_mul, abs_mul, abs_of_pos hqr, abs_of_pos hbr]
      _ ≤ (q : ℝ) * (η / q) + (C * (q : ℝ)) * |(q : ℝ) * α - p| := by
        exact add_le_add (mul_le_mul_of_nonneg_left herror hqr.le)
          (mul_le_mul_of_nonneg_right hb_size (abs_nonneg _))
      _ = η + C * (q : ℝ) ^ 2 * |α - (p : ℝ) / q| := by rw [hlinear]; field_simp
  apply (div_le_iff₀ (sq_pos_of_ne_zero hq0)).mpr
  apply (div_le_iff₀ hC).mpr
  nlinarith [hbound]

theorem approximation_pairs_lower_bound (α C η : ℝ) (hC : 0 < C)
    (_hη0 : 0 ≤ η) (_hη1 : η < 1) (hpairs : HasApproximationPairs α C η) :
    ApproximationLowerBound α ((1 - η) / C) := by
  intro p q hq
  obtain ⟨a, b, c, d, hb, hd, hb_size, hd_size, hind, herr_b, herr_d⟩ := hpairs q hq
  rcases independent_pair_cross_nonzero p q a b c d (ne_of_gt hq) hind with h | h
  · exact one_approximant_lower_bound α C η hC p q a b hq hb hb_size herr_b h
  · exact one_approximant_lower_bound α C η hC p q c d hq hd hd_size herr_d h

theorem approximation_pairs_constant_positive (C η : ℝ) (hC : 0 < C) (hη1 : η < 1) :
    0 < (1 - η) / C := div_pos (sub_pos.mpr hη1) hC

theorem approximation_pairs_positive_lower_bound (α C η : ℝ) (hC : 0 < C)
    (hη0 : 0 ≤ η) (hη1 : η < 1) (hpairs : HasApproximationPairs α C η) :
    0 < (1 - η) / C ∧ ApproximationLowerBound α ((1 - η) / C) := by
  exact ⟨approximation_pairs_constant_positive C η hC hη1,
    approximation_pairs_lower_bound α C η hC hη0 hη1 hpairs⟩

end PiWeightedColon
