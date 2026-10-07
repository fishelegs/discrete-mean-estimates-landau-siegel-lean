import Splice.CharacterArithmetic
import Splice.LFunctionIdentity
import Splice.HyperbolaAbel
import Splice.ExplicitMertens
import Splice.PrimeMassAssembly

/-!
# Elementary prime mass for the actual analytic L-value

No small-L assumption, real-zero premise, primitivity assumption, prime-mass
hypothesis, or analytic axiom appears in the final theorem. The only character
hypotheses are reality and nonprincipality, with conductor at least 97.
-/

namespace Splice

open Finset
open scoped BigOperators

variable {D : ℕ}

theorem sqrt_conductor_div_fourth {d : ℝ} (hd : 0 < d) :
    Real.sqrt (d / d ^ 4) = d ^ (-(3 / 2 : ℝ)) := by
  calc
    Real.sqrt (d / d ^ 4) = (d ^ ((1 : ℝ) - 4)) ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_sub hd, Real.rpow_one, Real.rpow_ofNat]
    _ = d ^ (((1 : ℝ) - 4) * (1 / 2)) := (Real.rpow_mul hd.le _ _).symm
    _ = d ^ (-(3 / 2 : ℝ)) := by norm_num

theorem character_nu_harmonic_conductor_interval [NeZero D] (hD : 1 ≤ D)
    (χ : DirichletCharacter ℂ D) (hne : χ ≠ 1) :
    harmonicNuInterval χ (D ^ 4) (D ^ 32) ≤
      28 * Real.log D * LOne χ + 18 * (D : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hDT : (D : ℝ) ≤ (D : ℝ) ^ 4 := by
    exact_mod_cast Nat.le_self_pow (by norm_num : 4 ≠ 0) D
  have hTX : (D : ℝ) ^ 4 ≤ (D : ℝ) ^ 32 := by
    exact_mod_cast Nat.pow_le_pow_right (show 0 < D by omega) (by norm_num : 4 ≤ 32)
  have h := nu_harmonic_tail_eighteen_sqrt χ hne hDT hTX
  have hlog : Real.log ((D : ℝ) ^ 32 / (D : ℝ) ^ 4) = 28 * Real.log D := by
    rw [Real.log_div (pow_pos hD0 32).ne' (pow_pos hD0 4).ne', Real.log_pow, Real.log_pow]
    norm_num <;> ring
  rw [hlog, sqrt_conductor_div_fourth hD0] at h
  simpa only [← Nat.cast_pow, Nat.floor_natCast, harmonicNuInterval, mul_comm,
    mul_left_comm, mul_assoc] using h

/-- The desired actual-prime first-moment lower bound, retaining the true
L-value rather than imposing the small-L assumption A. -/
theorem elementary_prime_mass [NeZero D] (hD : 97 ≤ D)
    (χ : DirichletCharacter ℂ D) (hne : χ ≠ 1)
    (hreal : ∀ x : ZMod D, (χ x).im = 0) :
    goodPrimeMass D χ / (32 * Real.log D) ≥
      7 / 8 - 1 / (4 * Real.log D) - 14 * Real.log D * LOne χ -
        9 * (D : ℝ) ^ (-(3 / 2 : ℝ)) := by
  apply prime_mass_from_mertens_and_harmonic hD χ hreal
  · have h := (abs_le.mp (ExplicitMertens.prime_log_div_abs_error_le_four_nat
        (n := D ^ 4) (one_le_pow₀ (show 1 ≤ D by omega)))).2
    simp only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] at h
    unfold primeLogMass
    linarith
  · have h := (abs_le.mp (ExplicitMertens.prime_log_div_abs_error_le_four_nat
        (n := D ^ 32) (one_le_pow₀ (show 1 ≤ D by omega)))).1
    simp only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] at h
    unfold primeLogMass
    linarith
  · exact character_nu_harmonic_conductor_interval (by omega) χ hne

end Splice

#print axioms Splice.elementary_prime_mass
