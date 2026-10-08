import EndpointColon
import Mathlib.Tactic.NormNum

noncomputable section

namespace PiWeightedColon.Regression

open Polynomial

def cancellingExample : Plane := mono 2 0 + mono 0 4

/-- Two nonzero lowest-weight terms really can occur in the input. -/
theorem input_boundary : Data 3 2 (coeff cancellingExample) ∧
    ¬ Data 3 3 (coeff cancellingExample) := by
  constructor
  · exact (dataIdeal F2 3 2).add_mem
      (data_mono (by decide)) (data_mono (by decide))
  · intro h
    have hz := h 2 0 (by decide)
    norm_num [coeff, cancellingExample, mono, Polynomial.coeff_monomial] at hz

/-- The mixed coefficient cancels in characteristic two. -/
theorem mixed_term_cancels : coeff (localQ F2 * cancellingExample) 2 4 = 0 := by
  rw [coeff_localQ_mul]
  norm_num [action, coeff, cancellingExample, mono, Polynomial.coeff_monomial]
  decide

/-- Despite that cancellation the exact threshold is raised by two, not three. -/
theorem output_boundary : Data 3 4 (coeff (localQ F2 * cancellingExample)) ∧
    ¬ Data 3 5 (coeff (localQ F2 * cancellingExample)) := by
  constructor
  · exact (weighted_colon (m := 2) (Or.inr rfl) cancellingExample).mpr input_boundary.1
  · intro h
    exact input_boundary.2
      ((weighted_colon (m := 3) (Or.inr rfl) cancellingExample).mp h)

/-- The generator `(z-ε,y^d)` gives the usual y order even at N=0. -/
theorem endpoint_zero_membership (ε : Bool) :
    C (X ^ endpointD ε) ∈ endpointJ ε * endpointK ε ^ 0 := by
  rw [Submodule.pow_zero, Ideal.IsTwoSided.mul_one]
  exact Ideal.subset_span (by simp)

/-- Dropping the positive-scale condition in the predecessor statement is false. -/
theorem zero_scale_colon_not_self :
    (dataIntersection 0).colon {globalQ} ≠ dataIntersection 0 := by
  intro h
  have hg (ε : Bool) : globalQ ∈ endpointJ ε * endpointK ε ^ 0 := by
    apply (endpoint_membership ε 0 globalQ).mpr
    rw [coordinate_globalQ, localJK_eq_dataIdeal (by cases ε <;> decide)]
    have hd : endpointD ε = 1 ∨ endpointD ε = 3 := by cases ε <;> decide
    have hh := (weighted_colon (m := 0) hd (1 : Plane)).mpr
      (by intro k c hkc; omega)
    intro k c hc
    simpa only [mul_one] using hh k c (by omega)
  have hQ : globalQ ∈ dataIntersection 0 := ⟨hg false, hg true⟩
  have hone : (1 : Plane) ∈ (dataIntersection 0).colon {globalQ} := by
    rw [Submodule.mem_colon_singleton, smul_eq_mul, one_mul]
    exact hQ
  rw [h] at hone
  have h0 : (1 : Plane) ∈ endpointJ false * endpointK false ^ 0 := hone.1
  rw [endpoint_membership, localJK_eq_dataIdeal (by decide)] at h0
  rw [map_one] at h0
  have hz := h0 0 0 (by decide)
  norm_num [coeff] at hz

end PiWeightedColon.Regression
