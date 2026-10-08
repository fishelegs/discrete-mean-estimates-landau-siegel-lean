import EndpointColon
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.Coprime.Lemmas

/-! The univariate remainder step. Divisibility conditions are explicit inputs;
this file does not derive them from the quotient ring or endpoint data ideals.
The two condition packages suffice for every N, independent of parity. -/

noncomputable section

namespace PiWeightedColon

open Polynomial

instance f2_isPrime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

abbrev Line := Polynomial F2

def u : Line := X + 1

theorem u_monic : u.Monic := by simpa [u] using monic_X_add_C (1 : F2)

theorem u_degree : u.natDegree = 1 := by simpa [u] using natDegree_X_add_C (1 : F2)

theorem t_u_coprime : IsCoprime (X : Line) u := by
  refine ⟨-1, 1, ?_⟩
  unfold u
  ring

theorem t_u_power_degree (n m : ℕ) :
    ((X : Line) ^ n * u ^ m).natDegree = n + m := by
  rw [(monic_X.pow n).natDegree_mul' (pow_ne_zero m u_monic.ne_zero),
    natDegree_X_pow, u_monic.natDegree_pow, u_degree, mul_one]

theorem bounded_factor {p f : Line} (hp : p.Monic) (hpf : p ∣ f) {r : ℕ}
    (hdeg : f.natDegree ≤ p.natDegree + r) :
    ∃ g : Line, f = p * g ∧ g.natDegree ≤ r := by
  obtain ⟨g, rfl⟩ := hpf
  refine ⟨g, rfl, ?_⟩
  by_cases hg : g = 0
  · simp [hg]
  · rw [hp.natDegree_mul' hg] at hdeg
    omega

theorem factor_from_endpoint_powers {f : Line} (n m r : ℕ)
    (ht : (X : Line) ^ n ∣ f) (hu : u ^ m ∣ f)
    (hdeg : f.natDegree ≤ n + m + r) :
    ∃ g : Line, f = X ^ n * u ^ m * g ∧ g.natDegree ≤ r := by
  apply bounded_factor ((monic_X.pow n).mul (u_monic.pow m))
    ((t_u_coprime.pow : IsCoprime ((X : Line) ^ n) (u ^ m)).mul_dvd ht hu)
  rwa [t_u_power_degree]

theorem cancel_endpoint_powers (n r m : ℕ) (f : Line)
    (h : u ^ (n + r) ∣ (X : Line) ^ m * u ^ n * f) : u ^ r ∣ f := by
  have he : (X : Line) ^ m * u ^ n * f = u ^ n * (X ^ m * f) := by ring
  rw [pow_add, he, mul_dvd_mul_iff_left (pow_ne_zero n u_monic.ne_zero)] at h
  exact (t_u_coprime.symm.pow : IsCoprime (u ^ r) ((X : Line) ^ m)).dvd_of_dvd_mul_left h

/-- Vanishing from the divisibility package needed when N is even.
The implication itself is stronger: it holds for every natural N, including 0. -/
theorem remainder_even (N : ℕ) (A B : Line)
    (hAdeg : A.natDegree ≤ 4 * N + 1) (hBdeg : B.natDegree ≤ 4 * N + 1)
    (hAt : (X : Line) ^ (N + 1) ∣ A) (hBt : (X : Line) ^ N ∣ B)
    (hAu : u ^ (3 * N) ∣ A) (hBu : u ^ (3 * N) ∣ B)
    (hAB : u ^ (3 * N + 3) ∣ A + u * B) : A = 0 ∧ B = 0 := by
  obtain ⟨a, hA, hadeg⟩ := factor_from_endpoint_powers (N + 1) (3 * N) 0 hAt hAu
    (by omega)
  obtain ⟨b, hB, hbdeg⟩ := factor_from_endpoint_powers N (3 * N) 1 hBt hBu (by omega)
  have hac : a = C (a.coeff 0) := eq_C_of_natDegree_le_zero hadeg
  rw [hac] at hA
  have he : A + u * B = X ^ N * u ^ (3 * N) * (C (a.coeff 0) * X + u * b) := by
    rw [hA, hB, pow_succ]
    ring
  rw [he] at hAB
  have hdiv := cancel_endpoint_powers (3 * N) 3 N (C (a.coeff 0) * X + u * b) hAB
  have hleft := natDegree_mul_le (p := C (a.coeff 0)) (q := (X : Line))
  have hright := natDegree_mul_le (p := u) (q := b)
  simp only [natDegree_C, natDegree_X, u_degree] at hleft hright
  have hdeg : (C (a.coeff 0) * X + u * b).natDegree ≤ 2 :=
    (natDegree_add_le _ _).trans (max_le (by omega) (by omega))
  have hz : C (a.coeff 0) * X + u * b = 0 :=
    eq_zero_of_dvd_of_natDegree_lt hdiv (by rw [u_monic.natDegree_pow, u_degree]; omega)
  have ha0 : a.coeff 0 = 0 := by
    have hh := congrArg (Polynomial.eval (1 : F2)) hz
    simpa [u, CharTwo.add_self_eq_zero] using hh
  have hb0 : b = 0 := by
    rw [ha0, C_0, zero_mul, zero_add] at hz
    exact (mul_eq_zero.mp hz).resolve_left u_monic.ne_zero
  constructor
  · simp [hA, ha0]
  · simp [hB, hb0]

/-- Vanishing from the divisibility package needed when N is odd.
Again parity is unnecessary once these explicit hypotheses have been supplied. -/
theorem remainder_odd (N : ℕ) (A B : Line)
    (hAdeg : A.natDegree ≤ 4 * N + 1) (hBdeg : B.natDegree ≤ 4 * N + 1)
    (hAt : (X : Line) ^ (N + 1) ∣ A) (hBt : (X : Line) ^ N ∣ B)
    (hAu : u ^ (3 * N + 1) ∣ A) (hBu : u ^ (3 * N) ∣ B)
    (hAB : u ^ (3 * N + 3) ∣ A + X ^ 2 * u * B) : A = 0 ∧ B = 0 := by
  have hA : A = 0 := eq_zero_of_dvd_of_natDegree_lt
    ((t_u_coprime.pow : IsCoprime ((X : Line) ^ (N + 1)) (u ^ (3 * N + 1))).mul_dvd hAt hAu)
    (by rw [t_u_power_degree]; omega)
  obtain ⟨b, hB, hbdeg⟩ := factor_from_endpoint_powers N (3 * N) 1 hBt hBu (by omega)
  have he : A + X ^ 2 * u * B = X ^ (N + 2) * u ^ (3 * N + 1) * b := by
    rw [hA, hB, pow_add, pow_succ]
    ring
  rw [he] at hAB
  have hdiv : u ^ 2 ∣ b := cancel_endpoint_powers (3 * N + 1) 2 (N + 2) b
    (by have ht : (3 * N + 1) + 2 = 3 * N + 3 := by omega
        rw [ht]; exact hAB)
  have hb0 : b = 0 := eq_zero_of_dvd_of_natDegree_lt hdiv
    (by rw [u_monic.natDegree_pow, u_degree]; omega)
  exact ⟨hA, by simp [hB, hb0]⟩

/-- The parity-selected form of the remainder step, with the unproved local
divisibility bridge exposed in the hypotheses. -/
theorem remainder_by_parity (N : ℕ) (A B : Line)
    (hAdeg : A.natDegree ≤ 4 * N + 1) (hBdeg : B.natDegree ≤ 4 * N + 1)
    (hAt : (X : Line) ^ (N + 1) ∣ A) (hBt : (X : Line) ^ N ∣ B)
    (hAu : if Even N then u ^ (3 * N) ∣ A else u ^ (3 * N + 1) ∣ A)
    (hBu : u ^ (3 * N) ∣ B)
    (hAB : if Even N then u ^ (3 * N + 3) ∣ A + u * B
      else u ^ (3 * N + 3) ∣ A + X ^ 2 * u * B) : A = 0 ∧ B = 0 := by
  by_cases hN : Even N
  · rw [if_pos hN] at hAu hAB
    exact remainder_even N A B hAdeg hBdeg hAt hBt hAu hBu hAB
  · rw [if_neg hN] at hAu hAB
    exact remainder_odd N A B hAdeg hBdeg hAt hBt hAu hBu hAB

end PiWeightedColon
