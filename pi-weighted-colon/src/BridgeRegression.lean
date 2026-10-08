import RightRemainderBridge

noncomputable section

namespace PiWeightedColon.Regression

open Polynomial

/-- The quotient's two coefficients distinguish all linear remainders. -/
theorem remainder_coordinates_unique (A B D E : Line)
    (he : quadMk A B = quadMk D E) : A = D ∧ B = E := by
  exact ⟨by simpa only [quadA_mk] using congrArg quadA he,
    by simpa only [quadB_mk] using congrArg quadB he⟩

/-- z^2 really becomes t^4, rather than t^2. -/
theorem endpoint_zero_square_not_t2 :
    reduction ((endpointX false) ^ 2) ≠ quadC (X ^ 2) := by
  intro he
  rw [reduction_endpoint_zero_sq, quadC_eq_mk, quadC_eq_mk] at he
  have hh := congrArg (fun q => (quadA q).coeff 4) he
  simp [quadA_mk, coeff_X_pow] at hh

/-- A real generator product at odd scale passes the actual endpoint ideal,
not an assumed divisibility package. -/
theorem endpoint_one_scale_one_generator :
    reduction (endpointX true * C (X ^ 3)) ∈ rightOddIdeal 3 := by
  have hz : endpointX true ∈ endpointJ true :=
    Ideal.subset_span (Set.mem_insert _ _)
  have hy : C (X ^ 3) ∈ endpointK true :=
    Ideal.subset_span (by change C (X ^ 3) ∈ {(endpointX true) ^ 2, C (X ^ 3)}; simp)
  have hf : endpointX true * C (X ^ 3) ∈ endpointJ true * endpointK true ^ 1 := by
    simpa only [Submodule.pow_one] using Ideal.mul_mem_mul hz hy
  have hm := endpoint_one_image 1 (Ideal.mem_map_of_mem reduction hf)
  simpa using hm

/-- The same y^3 generator applied a second time tests the odd-to-even step. -/
theorem endpoint_one_scale_two_generator :
    reduction (endpointX true * C (X ^ 3) * C (X ^ 3)) ∈ rightEvenIdeal 6 := by
  have hz : endpointX true ∈ endpointJ true :=
    Ideal.subset_span (Set.mem_insert _ _)
  have hy : C (X ^ 3) ∈ endpointK true :=
    Ideal.subset_span (by change C (X ^ 3) ∈ {(endpointX true) ^ 2, C (X ^ 3)}; simp)
  have hf : endpointX true * C (X ^ 3) * C (X ^ 3) ∈ endpointJ true * endpointK true ^ 2 := by
    change endpointX true * C (X ^ 3) * C (X ^ 3) ∈
      endpointJ true * endpointK true ^ (1 + 1)
    rw [Submodule.pow_succ, ← Ideal.mul_assoc]
    exact Ideal.mul_mem_mul (by simpa only [Submodule.pow_one] using Ideal.mul_mem_mul hz hy) hy
  have hm := endpoint_one_image 2 (Ideal.mem_map_of_mem reduction hf)
  simpa using hm

/-- The bounded-remainder result also covers the actual N=0 intersection. -/
theorem intersection_scale_zero (f h : Plane) (A B : Line)
    (hf : f ∈ dataIntersection 0) (he : f = globalQ * h + linearRemainder A B)
    (ha : A.natDegree ≤ 1) (hb : B.natDegree ≤ 1) : f = globalQ * h := by
  exact dataIntersection_factor_Q 0 f h A B hf he (by simpa using ha) (by simpa using hb)

end PiWeightedColon.Regression
