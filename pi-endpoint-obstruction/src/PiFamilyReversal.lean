import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

/-!
# Eventual reversal for one explicit polynomial family

This file concerns the displayed polynomial family only. It does not identify
that family with a matrix determinant, prove source separation assumptions, or
claim anything about bad approximability of pi or other minor-selection rules.
-/

set_option autoImplicit false

namespace PiFamilyReversal

/-- The natural quotient is exact; see `three_mul_exponent`. -/
def exponent (N : ℕ) : ℕ := 2 * (N + 1) * (2 * (N + 1)^2 + 1) / 3

lemma numerator_dvd_three (N : ℕ) : 3 ∣ 2 * (N + 1) * (2 * (N + 1)^2 + 1) := by
  apply Nat.dvd_of_mod_eq_zero
  have h : (N + 1) % 3 < 3 := Nat.mod_lt _ (by decide)
  interval_cases hrem : (N + 1) % 3 <;>
    norm_num [Nat.mul_mod, Nat.add_mod, Nat.pow_mod, hrem]

/-- Exact integer meaning of the exponent, with no truncation ambiguity. -/
theorem three_mul_exponent (N : ℕ) :
    3 * exponent N = 2 * (N + 1) * (2 * (N + 1)^2 + 1) := by
  exact Nat.mul_div_cancel' (numerator_dvd_three N)

lemma exponent_ge_four (N : ℕ) (hN : 3 ≤ N) : 4 ≤ exponent N := by
  have hsq : 16 ≤ (N + 1)^2 := by nlinarith
  have hnum : 12 ≤ 2 * (N + 1) * (2 * (N + 1)^2 + 1) := by nlinarith
  have he := three_mul_exponent N
  omega

/-- Real coefficient; subtraction is in the reals, not truncated naturals. -/
noncomputable def coefficient (N : ℕ) : ℝ := 764 * (4 * (N : ℝ)^2 - 1)

lemma coefficient_lower (N : ℕ) (hN : 3 ≤ N) : 26740 ≤ coefficient N := by
  have hn : (3 : ℝ) ≤ N := by exact_mod_cast hN
  unfold coefficient
  nlinarith

/-- The explicitly given polynomial function over the complex numbers. -/
noncomputable def family (N : ℕ) (z : ℂ) : ℂ :=
  (-1 : ℂ)^N * (N : ℂ)^2 * z^(exponent N) *
    (289 * z^2 + (coefficient N : ℂ))

/-- A useful algebraic monotonicity bound for the degree-six base case. -/
lemma base_strict {A a b : ℝ} (hA : 26740 ≤ A)
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 49) :
    a^2 * (A - 289*a) < b^2 * (A - 289*b) := by
  have hb0 : 0 < b := lt_trans ha hab
  have ha49 : a ≤ 49 := le_trans hab.le hb
  have h1 := mul_nonneg ha.le (sub_nonneg.mpr ha49)
  have h2 := mul_nonneg hb0.le (sub_nonneg.mpr hb)
  have h3 := mul_nonneg ha.le (sub_nonneg.mpr hb)
  have h4 := mul_nonneg hb0.le (sub_nonneg.mpr ha49)
  have hsum : a^2 + a*b + b^2 ≤ 74*(a+b) := by nlinarith
  have hcoef := mul_nonneg (sub_nonneg.mpr hA) (show 0 ≤ a+b by positivity)
  have hpos : 0 < A*(a+b) - 289*(a^2+a*b+b^2) := by nlinarith
  have hd := mul_pos (sub_pos.mpr hab) hpos
  nlinarith

/-- Strict increase on `(0,7]`, uniform in every natural exponent at least four. -/
theorem radial_strict {A u t : ℝ} {n : ℕ}
    (hA : 26740 ≤ A) (hn : 4 ≤ n)
    (hu : 0 < u) (hut : u < t) (ht : t ≤ 7) :
    u^n * (A - 289*u^2) < t^n * (A - 289*t^2) := by
  have ht0 : 0 < t := lt_trans hu hut
  have hu7 : u ≤ 7 := le_trans hut.le ht
  have hu2 : 0 < u^2 := sq_pos_of_pos hu
  have hut2 : u^2 < t^2 := by nlinarith
  have ht2 : t^2 ≤ 49 := by nlinarith
  have hb := base_strict hA hu2 hut2 ht2
  have hb4 : u^4 * (A - 289*u^2) < t^4 * (A - 289*t^2) := by
    nlinarith [hb]
  have hres : 0 < A - 289*t^2 := by linarith
  have hpow : u^(n-4) ≤ t^(n-4) := pow_le_pow_left₀ hu.le hut.le _
  have hleft : 0 < u^(n-4) := pow_pos hu _
  have hright : 0 ≤ t^4 * (A - 289*t^2) := by positivity
  have hh := lt_of_lt_of_le (mul_lt_mul_of_pos_left hb4 hleft)
    (mul_le_mul_of_nonneg_right hpow hright)
  have hn' : n - 4 + 4 = n := Nat.sub_add_cancel hn
  simpa only [← mul_assoc, ← pow_add, hn'] using hh

/-- A polynomial object with the displayed coefficients. -/
noncomputable def familyPolynomial (N : ℕ) : Polynomial ℂ :=
  Polynomial.C ((-1 : ℂ)^N * (N : ℂ)^2) * Polynomial.X^(exponent N) *
    (Polynomial.C 289 * Polynomial.X^2 + Polynomial.C (coefficient N : ℂ))

/-- Evaluation connects the polynomial object to the displayed family. -/
theorem familyPolynomial_eval (N : ℕ) (z : ℂ) :
    (familyPolynomial N).eval z = family N z := by
  simp [familyPolynomial, family]

/-- Norm on the positive imaginary axis below the residual root. -/
theorem family_norm (N : ℕ) {t : ℝ} (ht : 0 ≤ t)
    (hres : 0 ≤ coefficient N - 289*t^2) :
    ‖family N ((t : ℂ) * Complex.I)‖ =
      (N : ℝ)^2 * t^(exponent N) * (coefficient N - 289*t^2) := by
  have hz : 289*((t : ℂ)*Complex.I)^2 + (coefficient N : ℂ) =
      ((coefficient N - 289*t^2 : ℝ) : ℂ) := by
    push_cast
    rw [mul_pow, Complex.I_sq]
    ring
  unfold family
  rw [hz]
  simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Complex.norm_natCast, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg ht, abs_of_nonneg hres]

/-- Uses the genuine mathlib pi constant and its certified upper bound. -/
theorem actual_period_bounds :
    0 < 2 * Real.pi ∧ 2 * Real.pi < (44 : ℝ)/7 ∧ (44 : ℝ)/7 ≤ 7 := by
  constructor
  · positivity
  constructor
  · linarith [Real.pi_lt_d4]
  · norm_num

/-- The magnitude at the fixed rational center exceeds that at the actual period
for every N >= 3. Only this explicit polynomial family is quantified over. -/
theorem family_reversal (N : ℕ) (hN : 3 ≤ N) :
    ‖family N (2 * (Real.pi : ℂ) * Complex.I)‖ <
      ‖family N ((44 : ℂ) / 7 * Complex.I)‖ := by
  obtain ⟨hu, hut, ht⟩ := actual_period_bounds
  have hA := coefficient_lower N hN
  have hn := exponent_ge_four N hN
  have h44 : 0 ≤ (44 : ℝ)/7 := by norm_num
  have hp : 0 ≤ coefficient N - 289*(2*Real.pi)^2 := by
    have hsq : (2*Real.pi)^2 ≤ 49 := by nlinarith
    linarith
  have hr : 0 ≤ coefficient N - 289*((44 : ℝ)/7)^2 := by linarith
  have hu_cast : (2 * (Real.pi : ℂ) * Complex.I) =
      ((2 * Real.pi : ℝ) : ℂ) * Complex.I := by push_cast; rfl
  have ht_cast : ((44 : ℂ) / 7 * Complex.I) =
      (((44 : ℝ)/7 : ℝ) : ℂ) * Complex.I := by push_cast; rfl
  rw [hu_cast, ht_cast, family_norm N hu.le hp, family_norm N h44 hr]
  have hNpos : 0 < (N : ℝ)^2 := by
    have hnpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    positivity
  have h := radial_strict hA hn hu hut ht
  simpa only [mul_assoc] using mul_lt_mul_of_pos_left h hNpos

/-- Signed logarithmic gain for this family and these two centers. -/
noncomputable def signedGain (N : ℕ) : ℝ :=
  Real.log (‖family N (2 * (Real.pi : ℂ) * Complex.I)‖ /
    ‖family N ((44 : ℂ) / 7 * Complex.I)‖)

/-- Both compared values are genuinely nonzero for N >= 3. -/
theorem family_norm_pos (N : ℕ) (hN : 3 ≤ N) {t : ℝ}
    (ht : 0 < t) (ht7 : t ≤ 7) :
    0 < ‖family N ((t : ℂ) * Complex.I)‖ := by
  have hA := coefficient_lower N hN
  have ht2 : t^2 ≤ 49 := by nlinarith
  have hres : 0 < coefficient N - 289*t^2 := by linarith
  rw [family_norm N ht.le hres.le]
  have hnpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  positivity

/-- The signed logarithmic gain is strictly negative throughout the tail. -/
theorem signedGain_neg (N : ℕ) (hN : 3 ≤ N) : signedGain N < 0 := by
  have hp : 0 < ‖family N (2 * (Real.pi : ℂ) * Complex.I)‖ := by
    have h := family_norm_pos N hN actual_period_bounds.1
      (le_trans actual_period_bounds.2.1.le actual_period_bounds.2.2)
    simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using h
  have hcmp := family_reversal N hN
  have hr : 0 < ‖family N ((44 : ℂ)/7 * Complex.I)‖ := lt_trans hp hcmp
  exact Real.log_neg (div_pos hp hr) ((div_lt_one hr).mpr hcmp)

/-- In particular, positive signed gain cannot occur at any N >= 3. -/
theorem not_positive_signedGain (N : ℕ) (hN : 3 ≤ N) : ¬ 0 < signedGain N :=
  not_lt_of_ge (signedGain_neg N hN).le

/-- Eventual negativity has the explicit cutoff N = 3. -/
theorem eventually_signedGain_neg :
    ∀ᶠ N : ℕ in Filter.atTop, signedGain N < 0 := by
  filter_upwards [Filter.eventually_ge_atTop 3] with N hN
  exact signedGain_neg N hN

end PiFamilyReversal
