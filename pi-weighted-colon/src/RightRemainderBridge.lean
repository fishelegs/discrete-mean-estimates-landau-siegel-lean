import EndpointRemainderBridge

noncomputable section

namespace PiWeightedColon

open Polynomial

theorem t_sq_in_u : (X : Line) ^ 2 = u ^ 2 + 1 := by
  simp [u, CharTwo.add_sq, CharTwo.add_self_eq_zero, add_assoc]

theorem right_odd_correction : quadW + (X ^ 2 * u) ^ 2 = X ^ 2 * u ^ 4 := by
  calc
    _ = X ^ 2 * u ^ 2 * (1 + X ^ 2) := by simp only [quadW]; ring
    _ = _ := by
      rw [t_sq_in_u]
      rw [show (1 : Line) + (u ^ 2 + 1) = u ^ 2 by
        rw [add_left_comm, CharTwo.add_self_eq_zero, add_zero]]
      ring

theorem coupled_mul_identity (v : Line) (a q : Quad) :
    quadA (a * q) + v * quadB (a * q) =
      (quadA a + v * quadB a) * (quadA q + v * quadB q) +
        (quadW + v ^ 2) * quadB a * quadB q := by
  rw [quadA_mul, quadB_mul]
  have he : quadA a * quadA q + quadW * quadB a * quadB q +
      v * (quadA a * quadB q + quadB a * quadA q) =
      (quadA a + v * quadB a) * (quadA q + v * quadB q) +
        (quadW - v ^ 2) * quadB a * quadB q := by ring
  simpa only [sub_eq_add_neg, CharTwo.neg_eq] using he

def rightCoupledIdeal (m j : ℕ) (v : Line) (hj : j ≤ 2)
    (hv : u ^ 4 ∣ quadW + v ^ 2) : Ideal Quad where
  carrier := {q | u ^ (m + j) ∣ quadA q ∧ u ^ m ∣ quadB q ∧
    u ^ (m + 3) ∣ quadA q + v * quadB q}
  zero_mem' := by simp [quadA_zero, quadB_zero]
  add_mem' := by
    intro q r hq hr
    refine ⟨?_, ?_, ?_⟩
    · rw [quadA_add]; exact dvd_add hq.1 hr.1
    · rw [quadB_add]; exact dvd_add hq.2.1 hr.2.1
    · rw [quadA_add, quadB_add]
      convert dvd_add hq.2.2 hr.2.2 using 1; ring
  smul_mem' := by
    intro a q hq
    change u ^ (m + j) ∣ quadA (a * q) ∧ u ^ m ∣ quadB (a * q) ∧
      u ^ (m + 3) ∣ quadA (a * q) + v * quadB (a * q)
    have hw : u ^ 2 ∣ quadW := by rw [quadW, mul_comm]; exact dvd_mul_right _ _
    refine ⟨?_, ?_, ?_⟩
    · rw [quadA_mul]
      apply dvd_add (dvd_mul_of_dvd_right hq.1 _)
      have hh := power_dvd_lower (show m + j ≤ 2 + m by omega)
        (power_dvd_product hw hq.2.1)
      convert dvd_mul_of_dvd_right hh (quadB a) using 1; ring
    · rw [quadB_mul]
      exact dvd_add (dvd_mul_of_dvd_right hq.2.1 _)
        (dvd_mul_of_dvd_right (power_dvd_lower (by omega) hq.1) _)
    · rw [coupled_mul_identity]
      apply dvd_add (dvd_mul_of_dvd_right hq.2.2 _)
      have hh := power_dvd_lower (show m + 3 ≤ 4 + m by omega)
        (power_dvd_product hv hq.2.1)
      convert dvd_mul_of_dvd_right hh (quadB a) using 1; ring

def rightEvenIdeal (m : ℕ) : Ideal Quad := rightCoupledIdeal m 0 u (by omega)
  (by rw [add_comm, quadW_u_identity])

def rightOddIdeal (m : ℕ) : Ideal Quad := rightCoupledIdeal m 1 (X ^ 2 * u) (by omega)
  (by rw [right_odd_correction]; exact dvd_mul_left _ _)

theorem rightEvenIdeal_mem (m : ℕ) (q : Quad) :
    q ∈ rightEvenIdeal m ↔ u ^ m ∣ quadA q ∧ u ^ m ∣ quadB q ∧
      u ^ (m + 3) ∣ quadA q + u * quadB q := by rfl

theorem rightOddIdeal_mem (m : ℕ) (q : Quad) :
    q ∈ rightOddIdeal m ↔ u ^ (m + 1) ∣ quadA q ∧ u ^ m ∣ quadB q ∧
      u ^ (m + 3) ∣ quadA q + X ^ 2 * u * quadB q := Iff.rfl

theorem rightEven_extra_A (m : ℕ) (q : Quad) (hq : q ∈ rightEvenIdeal m) :
    u ^ (m + 1) ∣ quadA q := by
  rw [rightEvenIdeal_mem] at hq
  have hh := dvd_add (power_dvd_lower (show m + 1 ≤ m + 3 by omega) hq.2.2)
    (by
      convert power_dvd_product (show u ^ 1 ∣ u by simp) hq.2.1 using 1; congr 1; omega)
  have he : quadA q + u * quadB q + u * quadB q = quadA q := by
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  rw [he] at hh
  exact hh

theorem coupled_switch (q : Quad) :
    quadA q + X ^ 2 * u * quadB q = quadA q + u * quadB q + u ^ 3 * quadB q := by
  rw [t_sq_in_u]
  ring

theorem rightEven_u4_step (m : ℕ) (q : Quad) (hq : q ∈ rightEvenIdeal m) :
    q * quadC (u ^ 4) ∈ rightOddIdeal (m + 3) := by
  rw [rightEvenIdeal_mem] at hq
  rw [rightOddIdeal_mem, quadC_eq_mk, quadA_mul, quadB_mul, quadA_mk, quadB_mk]
  simp only [mul_zero, add_zero, zero_add]
  refine ⟨?_, ?_, ?_⟩
  · convert power_dvd_product hq.1 (dvd_refl (u ^ 4)) using 1
  · exact power_dvd_lower (by omega) (power_dvd_product hq.2.1 (dvd_refl _))
  · have hh : u ^ (m + 3) ∣ quadA q + X ^ 2 * u * quadB q := by
      rw [coupled_switch]
      exact dvd_add hq.2.2 (by
        convert power_dvd_product (dvd_refl (u ^ 3)) hq.2.1 using 1; congr 1; omega)
    convert power_dvd_lower (show (m + 3) + 3 ≤ (m + 3) + 4 by omega)
      (power_dvd_product hh (dvd_refl (u ^ 4))) using 1; ring

theorem rightOdd_u4_step (m : ℕ) (q : Quad) (hq : q ∈ rightOddIdeal m) :
    q * quadC (u ^ 4) ∈ rightEvenIdeal (m + 3) := by
  rw [rightOddIdeal_mem] at hq
  rw [rightEvenIdeal_mem, quadC_eq_mk, quadA_mul, quadB_mul, quadA_mk, quadB_mk]
  simp only [mul_zero, add_zero, zero_add]
  refine ⟨power_dvd_lower (by omega) (power_dvd_product hq.1 (dvd_refl _)),
    power_dvd_lower (by omega) (power_dvd_product hq.2.1 (dvd_refl _)), ?_⟩
  have hh : u ^ (m + 3) ∣ quadA q + u * quadB q := by
    have he : quadA q + u * quadB q =
        (quadA q + X ^ 2 * u * quadB q) + u ^ 3 * quadB q := by
      rw [coupled_switch, add_assoc, CharTwo.add_self_eq_zero, add_zero]
    rw [he]
    exact dvd_add hq.2.2 (by
      convert power_dvd_product (dvd_refl (u ^ 3)) hq.2.1 using 1; congr 1; omega)
  convert power_dvd_lower (show (m + 3) + 3 ≤ (m + 3) + 4 by omega)
    (power_dvd_product hh (dvd_refl (u ^ 4))) using 1; ring

theorem rightEven_y3_step (m : ℕ) (q : Quad) (hq : q ∈ rightEvenIdeal m) :
    q * quadMk 0 quadW ∈ rightOddIdeal (m + 3) := by
  have ha := rightEven_extra_A m q hq
  rw [rightEvenIdeal_mem] at hq
  rw [rightOddIdeal_mem, quadA_mul, quadB_mul, quadA_mk, quadB_mk]
  simp only [mul_zero, zero_add, add_zero]
  have hw : u ^ 2 ∣ quadW := by rw [quadW, mul_comm]; exact dvd_mul_right _ _
  refine ⟨?_, ?_, ?_⟩
  · have hh := power_dvd_product (power_dvd_product hw hw) hq.2.1
    convert hh using 1 <;> first | congr 1 <;> omega | ring
  · convert power_dvd_product ha hw using 1
  · have he : quadW * quadB q * quadW + X ^ 2 * u * (quadA q * quadW) =
        X ^ 4 * u ^ 3 * (quadA q + u * quadB q) := by unfold quadW; ring
    rw [he]
    have hh := power_dvd_product (dvd_refl (u ^ 3)) hq.2.2
    convert dvd_mul_of_dvd_right hh (X ^ 4) using 1 <;> first | congr 1 <;> omega | ring

theorem rightOdd_y3_step (m : ℕ) (q : Quad) (hq : q ∈ rightOddIdeal m) :
    q * quadMk 0 quadW ∈ rightEvenIdeal (m + 3) := by
  rw [rightOddIdeal_mem] at hq
  rw [rightEvenIdeal_mem, quadA_mul, quadB_mul, quadA_mk, quadB_mk]
  simp only [mul_zero, zero_add, add_zero]
  have hw : u ^ 2 ∣ quadW := by rw [quadW, mul_comm]; exact dvd_mul_right _ _
  refine ⟨?_, ?_, ?_⟩
  · have hh := power_dvd_lower (show m + 3 ≤ (2 + 2) + m by omega)
      (power_dvd_product (power_dvd_product hw hw) hq.2.1)
    convert hh using 1; ring
  · convert power_dvd_product hq.1 hw using 1
  · have he : quadW * quadB q * quadW + u * (quadA q * quadW) =
        X ^ 2 * u ^ 3 * (quadA q + X ^ 2 * u * quadB q) := by unfold quadW; ring
    rw [he]
    have hh := power_dvd_product (dvd_refl (u ^ 3)) hq.2.2
    convert dvd_mul_of_dvd_right hh (X ^ 2) using 1 <;> first | congr 1 <;> omega | ring

theorem endpoint_one_J_image : (endpointJ true).map reduction ≤ rightEvenIdeal 0 := by
  rw [endpointJ, Ideal.map_span]
  apply Ideal.span_le.mpr
  rintro _ ⟨g, hg, rfl⟩
  rcases hg with (rfl | rfl)
  · change reduction (endpointX true) ∈ rightEvenIdeal 0
    rw [reduction_endpoint_one, rightEvenIdeal_mem, quadA_mk, quadB_mk]
    simp [CharTwo.add_self_eq_zero]
  · change reduction (C (X ^ 3)) ∈ rightEvenIdeal 0
    rw [reduction_y_cube, rightEvenIdeal_mem, quadA_mk, quadB_mk]
    refine ⟨by simp, by simp, ?_⟩
    simp only [zero_add]
    refine ⟨X ^ 2, ?_⟩
    unfold quadW
    ring

theorem endpoint_one_K_even_step (m : ℕ) :
    rightEvenIdeal m * (endpointK true).map reduction ≤ rightOddIdeal (m + 3) := by
  rw [endpointK, Ideal.map_span]
  apply ideal_mul_span_le
  intro q hq g hg
  rcases hg with ⟨a, ha, rfl⟩
  rcases ha with (rfl | rfl)
  · rw [reduction_endpoint_one_sq]
    exact rightEven_u4_step m q hq
  · change q * reduction (C (X ^ 3)) ∈ rightOddIdeal (m + 3)
    rw [reduction_y_cube]
    exact rightEven_y3_step m q hq

theorem endpoint_one_K_odd_step (m : ℕ) :
    rightOddIdeal m * (endpointK true).map reduction ≤ rightEvenIdeal (m + 3) := by
  rw [endpointK, Ideal.map_span]
  apply ideal_mul_span_le
  intro q hq g hg
  rcases hg with ⟨a, ha, rfl⟩
  rcases ha with (rfl | rfl)
  · rw [reduction_endpoint_one_sq]
    exact rightOdd_u4_step m q hq
  · change q * reduction (C (X ^ 3)) ∈ rightEvenIdeal (m + 3)
    rw [reduction_y_cube]
    exact rightOdd_y3_step m q hq

theorem endpoint_one_image (N : ℕ) :
    (endpointJ true * endpointK true ^ N).map reduction ≤
      if Even N then rightEvenIdeal (3 * N) else rightOddIdeal (3 * N) := by
  induction N with
  | zero =>
    rw [Submodule.pow_zero, Ideal.one_eq_top, Ideal.mul_top,
      if_pos (show Even 0 by decide), Nat.mul_zero]
    exact endpoint_one_J_image
  | succ N ih =>
    rw [Submodule.pow_succ, ← Ideal.mul_assoc, Ideal.map_mul]
    by_cases hn : Even N
    · have hn' : ¬ Even (N + 1) := by simpa only [Nat.even_add_one, not_not] using hn
      rw [if_pos hn] at ih
      rw [if_neg hn', show 3 * (N + 1) = 3 * N + 3 by omega]
      exact le_trans (Ideal.mul_mono ih le_rfl) (endpoint_one_K_even_step (3 * N))
    · have hn' : Even (N + 1) := by simpa only [Nat.even_add_one] using hn
      rw [if_neg hn] at ih
      rw [if_pos hn', show 3 * (N + 1) = 3 * N + 3 by omega]
      exact le_trans (Ideal.mul_mono ih le_rfl) (endpoint_one_K_odd_step (3 * N))

theorem endpoint_one_remainder_divisibility (N : ℕ) (f h : Plane) (A B : Line)
    (hf : f ∈ endpointJ true * endpointK true ^ N)
    (he : f = globalQ * h + linearRemainder A B) :
    (if Even N then u ^ (3 * N) ∣ A else u ^ (3 * N + 1) ∣ A) ∧
      u ^ (3 * N) ∣ B ∧
      (if Even N then u ^ (3 * N + 3) ∣ A + u * B
        else u ^ (3 * N + 3) ∣ A + X ^ 2 * u * B) := by
  have hm := endpoint_one_image N (Ideal.mem_map_of_mem reduction hf)
  rw [reduction_remainder_eq f h A B he] at hm
  by_cases hn : Even N
  · rw [if_pos hn, rightEvenIdeal_mem, quadA_mk, quadB_mk] at hm
    simpa only [if_pos hn] using hm
  · rw [if_neg hn, rightOddIdeal_mem, quadA_mk, quadB_mk] at hm
    simpa only [if_neg hn] using hm

/-- The actual intersection membership supplies every local divisibility input
needed by the previously verified remainder theorem. -/
theorem dataIntersection_remainder_zero (N : ℕ) (f h : Plane) (A B : Line)
    (hf : f ∈ dataIntersection N)
    (he : f = globalQ * h + linearRemainder A B)
    (hAdeg : A.natDegree ≤ 4 * N + 1) (hBdeg : B.natDegree ≤ 4 * N + 1) :
    A = 0 ∧ B = 0 := by
  have ht := endpoint_zero_remainder_divisibility N f h A B hf.1 he
  have hu := endpoint_one_remainder_divisibility N f h A B hf.2 he
  exact remainder_by_parity N A B hAdeg hBdeg ht.1 ht.2 hu.1 hu.2.1 hu.2.2

/-- With bounded remainder data, actual intersection membership gives an
explicit Q factor, before any staircase induction is attempted. -/
theorem dataIntersection_factor_Q (N : ℕ) (f h : Plane) (A B : Line)
    (hf : f ∈ dataIntersection N)
    (he : f = globalQ * h + linearRemainder A B)
    (hAdeg : A.natDegree ≤ 4 * N + 1) (hBdeg : B.natDegree ≤ 4 * N + 1) :
    f = globalQ * h := by
  obtain ⟨ha, hb⟩ := dataIntersection_remainder_zero N f h A B hf he hAdeg hBdeg
  simpa [ha, hb, linearRemainder] using he

end PiWeightedColon
