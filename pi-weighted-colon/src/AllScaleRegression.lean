import StaircaseNonvanishing

noncomputable section

namespace PiWeightedColon.Regression

open Polynomial

/-- Both even and odd y exponents on the upper staircase edge are included. -/
theorem upper_staircase_edge (N : ℕ) :
    mono (R := F2) 1 (2 * N) ∈ V_N N ∧ mono (R := F2) 1 (2 * N + 1) ∈ V_N N := by
  constructor
  · obtain ⟨ha, hs⟩ := (staircase_index_iff N 1 (2 * N)).mp
      (by unfold stairWeight; omega)
    exact Submodule.subset_span ⟨1, 2 * N, ha, hs, rfl⟩
  · obtain ⟨ha, hs⟩ := (staircase_index_iff N 1 (2 * N + 1)).mp
      (by unfold stairWeight; omega)
    exact Submodule.subset_span ⟨1, 2 * N + 1, ha, hs, rfl⟩

/-- A concrete division at N=2: the quotient is Q itself and the remainder
is t^8+t^4. This checks cancellation of the characteristic-two cross terms. -/
theorem y_four_division :
    (C (X ^ 4) : Plane) = globalQ * globalQ + linearRemainder (X ^ 8 + X ^ 4) 0 := by
  have hm : lineEmbedding ((X : Line) ^ 8 + X ^ 4) = (X : Plane) ^ 8 + X ^ 4 := by
    simp [lineEmbedding]
  rw [linearRemainder, hm, map_zero, mul_zero, add_zero, ← pow_two, globalQ_expanded]
  simp only [CharTwo.add_sq, ← pow_mul, C_pow]
  have he : ∀ p q r : Plane, p + q + r + (p + q) = r := by
    intro p q r
    calc
      _ = (p + p) + (q + q) + r := by ring
      _ = _ := by rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, zero_add, zero_add]
  exact (he _ _ _).symm

/-- The quotient's four-unit loss is sharp here: Q is permitted as the
N=1 quotient of y^4 at N=2, but is outside the N=0 staircase. -/
theorem y_four_quotient_bound : QuotBound 9 globalQ ∧ ¬ StairBound 1 globalQ := by
  constructor
  · have he : globalQ = bimono 4 0 1 + bimono 2 0 1 + bimono 0 2 1 := by
      simp [bimono, monomial_zero_left, ← X_pow_eq_monomial, globalQ_expanded]
    rw [he]
    exact quotBound_add (quotBound_add (quotBound_bimono 1 (by decide))
      (quotBound_bimono 1 (by decide))) (quotBound_bimono 1 (by decide))
  · intro hq
    have hh := hq 4 0 (by decide)
    simp only [coeff, globalQ_expanded, Polynomial.coeff_add, coeff_C] at hh
    simp at hh

/-- Actual intersection membership alone cannot imply vanishing. The product
z(z-1) is nonzero and belongs to I_0, but lies outside V_0. -/
theorem nonzero_intersection_outside_staircase :
    endpointX false * endpointX true ∈ dataIntersection 0 ∧
      endpointX false * endpointX true ≠ 0 ∧
      endpointX false * endpointX true ∉ V_N 0 := by
  have hz0 : endpointX false ∈ endpointJ false := Ideal.subset_span (by simp)
  have hz1 : endpointX true ∈ endpointJ true := Ideal.subset_span (by simp)
  have hI : endpointX false * endpointX true ∈ dataIntersection 0 := by
    simp only [dataIntersection, Submodule.pow_zero, Ideal.one_eq_top, Ideal.mul_top]
    exact ⟨(endpointJ false).mul_mem_right _ hz0, (endpointJ true).mul_mem_left _ hz1⟩
  have hn : ∀ e, endpointX e ≠ 0 := by
    intro e he
    have hh := congrArg (fun p : Plane => p.coeff 1) he
    simp [endpointX] at hh
  have hnon := mul_ne_zero (hn false) (hn true)
  exact ⟨hI, hnon, fun hv => hnon (V_N_dataIntersection_zero 0 _ hv hI)⟩

theorem dataIntersection_proper (N : ℕ) : (1 : Plane) ∉ dataIntersection N := by
  intro hI
  have hV : (1 : Plane) ∈ V_N N := by
    have hm : mono (R := F2) 0 0 ∈ V_N N :=
      Submodule.subset_span ⟨0, 0, by omega, by omega, rfl⟩
    simpa [mono] using hm
  exact one_ne_zero (V_N_dataIntersection_zero N 1 hV hI)

end PiWeightedColon.Regression
