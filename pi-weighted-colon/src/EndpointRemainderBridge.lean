import QuadraticRemainder

noncomputable section

namespace PiWeightedColon

open Polynomial

theorem power_dvd_lower {p f : Line} {m n : ℕ} (hm : m ≤ n)
    (hf : p ^ n ∣ f) : p ^ m ∣ f :=
  dvd_trans (pow_dvd_pow p hm) hf

theorem power_dvd_product {p a b : Line} {m n : ℕ}
    (ha : p ^ m ∣ a) (hb : p ^ n ∣ b) : p ^ (m + n) ∣ a * b := by
  rw [pow_add]
  exact mul_dvd_mul ha hb

theorem quadC_eq_mk (A : Line) : quadC A = quadMk A 0 := by simp [quadMk]

theorem quadY_eq_mk : quadY = quadMk 0 1 := by simp [quadMk]

theorem reduction_endpoint_zero : reduction (endpointX false) = quadMk X 1 := by
  simp [endpointX, endpoint, reduction_t, reduction_y, quadMk]

theorem reduction_endpoint_one : reduction (endpointX true) = quadMk u 1 := by
  simp only [endpointX, endpoint, ↓reduceIte, map_sub, map_add,
    reduction_t, reduction_y, map_one]
  rw [show (1 : Quad) = quadC 1 by simp]
  simp only [quadMk, map_one, one_mul, u, map_add, map_one]
  have he : -(1 : Quad) = 1 := by
    have h : -(1 : Line) = 1 := CharTwo.neg_eq _
    simpa only [map_neg, map_one] using congrArg quadC h
  rw [sub_eq_add_neg, he]
  ac_rfl

theorem quadW_t_identity : (X : Line) ^ 2 + quadW = X ^ 4 := by
  simp only [quadW, u, CharTwo.add_sq, one_pow, mul_add, mul_one, ← pow_add]
  rw [show (2 : ℕ) + 2 = 4 by decide]
  rw [add_left_comm, CharTwo.add_self_eq_zero, add_zero]

theorem quadW_u_identity : u ^ 2 + quadW = u ^ 4 := by
  have ht : (X : Line) ^ 2 = u ^ 2 + 1 := by
    simp [u, CharTwo.add_sq, CharTwo.add_self_eq_zero, add_assoc]
  rw [quadW, ht]
  simp only [add_mul, one_mul, ← pow_add]
  rw [show (2 : ℕ) + 2 = 4 by decide]
  rw [add_left_comm, CharTwo.add_self_eq_zero, add_zero]

theorem reduction_endpoint_zero_sq : reduction ((endpointX false) ^ 2) = quadC (X ^ 4) := by
  rw [map_pow, pow_two, reduction_endpoint_zero, quadMk_mul]
  simp only [mul_one, one_mul, CharTwo.add_self_eq_zero, quadW_t_identity, ← pow_two]
  exact (quadC_eq_mk _).symm

theorem reduction_endpoint_one_sq : reduction ((endpointX true) ^ 2) = quadC (u ^ 4) := by
  rw [map_pow, pow_two, reduction_endpoint_one, quadMk_mul]
  simp only [mul_one, one_mul, CharTwo.add_self_eq_zero, quadW_u_identity, ← pow_two]
  exact (quadC_eq_mk _).symm

theorem reduction_y_cube : reduction (C (X ^ 3)) = quadMk 0 quadW := by
  rw [show C ((X : Line) ^ 3) = (C X : Plane) ^ 3 by simp, map_pow, reduction_y, show (3 : ℕ) = 2 + 1 by decide, pow_add,
    quadY_sq, pow_one]
  simp [quadMk]

def leftRemainderIdeal (N : ℕ) : Ideal Quad where
  carrier := {q | X ^ (N + 1) ∣ quadA q ∧ X ^ N ∣ quadB q}
  zero_mem' := by simp [quadA_zero, quadB_zero]
  add_mem' := by
    intro q r hq hr
    exact ⟨by rw [quadA_add]; exact dvd_add hq.1 hr.1,
      by rw [quadB_add]; exact dvd_add hq.2 hr.2⟩
  smul_mem' := by
    intro a q hq
    change X ^ (N + 1) ∣ quadA (a * q) ∧ X ^ N ∣ quadB (a * q)
    rw [quadA_mul, quadB_mul]
    have hw : (X : Line) ^ 2 ∣ quadW := ⟨u ^ 2, rfl⟩
    have hwb : (X : Line) ^ (N + 1) ∣ quadW * quadB q :=
      power_dvd_lower (by omega) (power_dvd_product hw hq.2)
    constructor
    · apply dvd_add (dvd_mul_of_dvd_right hq.1 _)
      convert dvd_mul_of_dvd_right hwb (quadB a) using 1; ring
    · exact dvd_add (dvd_mul_of_dvd_right hq.2 _)
        (dvd_mul_of_dvd_right (power_dvd_lower (by omega) hq.1) _)

theorem leftRemainderIdeal_mem (N : ℕ) (q : Quad) :
    q ∈ leftRemainderIdeal N ↔ X ^ (N + 1) ∣ quadA q ∧ X ^ N ∣ quadB q := Iff.rfl

theorem leftRemainderIdeal_y_step (N : ℕ) (q : Quad)
    (hq : q ∈ leftRemainderIdeal N) : q * quadY ∈ leftRemainderIdeal (N + 1) := by
  rw [leftRemainderIdeal_mem] at hq ⊢
  rw [quadY_eq_mk, quadA_mul, quadB_mul, quadA_mk, quadB_mk]
  simp only [mul_zero, zero_add, mul_one, add_zero]
  have hw : (X : Line) ^ 2 ∣ quadW := ⟨u ^ 2, rfl⟩
  constructor
  · convert power_dvd_product hw hq.2 using 1; congr 1; omega
  · exact hq.1

theorem leftRemainderIdeal_t4_step (N : ℕ) (q : Quad)
    (hq : q ∈ leftRemainderIdeal N) : q * quadC (X ^ 4) ∈ leftRemainderIdeal (N + 1) := by
  rw [leftRemainderIdeal_mem] at hq ⊢
  rw [quadC_eq_mk, quadA_mul, quadB_mul, quadA_mk, quadB_mk]
  simp only [mul_zero, add_zero, zero_add]
  exact ⟨power_dvd_lower (by omega) (power_dvd_product hq.1 (dvd_refl _)),
    power_dvd_lower (by omega) (power_dvd_product hq.2 (dvd_refl _))⟩

theorem ideal_mul_span_le {R : Type*} [CommRing R] (I T : Ideal R) (s : Set R)
    (h : ∀ q ∈ I, ∀ g ∈ s, q * g ∈ T) : I * Ideal.span s ≤ T := by
  apply Ideal.mul_le.mpr
  intro q hq r hr
  have hc : Ideal.span s ≤ T.colon {q} := Ideal.span_le.mpr (by
    intro g hg
    change g ∈ T.colon {q}
    rw [Submodule.mem_colon_singleton, smul_eq_mul]
    simpa only [mul_comm] using h q hq g hg)
  have hm := hc hr
  rw [Submodule.mem_colon_singleton, smul_eq_mul] at hm
  simpa only [mul_comm] using hm

theorem endpoint_zero_J_image : (endpointJ false).map reduction ≤ leftRemainderIdeal 0 := by
  rw [endpointJ, Ideal.map_span]
  apply Ideal.span_le.mpr
  rintro _ ⟨g, hg, rfl⟩
  rcases hg with (rfl | rfl)
  · change reduction (endpointX false) ∈ leftRemainderIdeal 0
    rw [reduction_endpoint_zero, leftRemainderIdeal_mem, quadA_mk, quadB_mk]
    simp
  · simp only [show endpointD false = 1 from rfl, pow_one, reduction_y]
    change quadY ∈ leftRemainderIdeal 0
    rw [quadY_eq_mk, leftRemainderIdeal_mem, quadA_mk, quadB_mk]
    simp

theorem endpoint_zero_K_step (N : ℕ) :
    leftRemainderIdeal N * (endpointK false).map reduction ≤ leftRemainderIdeal (N + 1) := by
  rw [endpointK, Ideal.map_span]
  apply ideal_mul_span_le
  intro q hq g hg
  rcases hg with ⟨a, ha, rfl⟩
  rcases ha with (rfl | rfl)
  · rw [reduction_endpoint_zero_sq]
    exact leftRemainderIdeal_t4_step N q hq
  · simp only [show endpointD false = 1 from rfl, pow_one, reduction_y]
    exact leftRemainderIdeal_y_step N q hq

theorem endpoint_zero_image (N : ℕ) :
    (endpointJ false * endpointK false ^ N).map reduction ≤ leftRemainderIdeal N := by
  induction N with
  | zero => simpa only [Submodule.pow_zero, Ideal.one_eq_top, Ideal.mul_top] using endpoint_zero_J_image
  | succ N ih =>
    rw [Submodule.pow_succ, ← Ideal.mul_assoc, Ideal.map_mul]
    exact le_trans (Ideal.mul_mono ih le_rfl) (endpoint_zero_K_step N)

theorem endpoint_zero_remainder_divisibility (N : ℕ) (f h : Plane) (A B : Line)
    (hf : f ∈ endpointJ false * endpointK false ^ N)
    (he : f = globalQ * h + linearRemainder A B) :
    X ^ (N + 1) ∣ A ∧ X ^ N ∣ B := by
  have hm := endpoint_zero_image N (Ideal.mem_map_of_mem reduction hf)
  rw [leftRemainderIdeal_mem, reduction_remainder_eq f h A B he, quadA_mk, quadB_mk] at hm
  exact hm

end PiWeightedColon
