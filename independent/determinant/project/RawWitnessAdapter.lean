import FiniteGreedyBridge
import ExplicitCutoffAdapter

/-!
# Fixed-parameter extraction from the raw same-witness theorem

The finite source theorem is invoked exactly once. Its arithmetic field, selected
rows and nonzero integral determinant are retained together. Finite coordinate
and weight-sorted enumerations are constructed from cardinality and the existing
finite sorting theorem; neither a global row enumeration nor a determinant
existence hypothesis is supplied by the caller.

The parameters are H = 86713344, N = D^24, U = (D : ℝ)^32,
M = (D : ℝ)^96, and kappa = ExplicitCutoffAdapter.explicitKappa.
The prime mass is the exact good-prime sum in the raw finite-place theorem.
The final lower-bound corollary is still conditional on its explicitly stated
prime-mass inequality; it makes no identification of t with an L-function.

This adapter is being prepared source-first. Its validation status must be
reported separately from the mathematical content of its declarations.
-/

namespace RawWitnessAdapter

open OAI.SiegelZeros.WeightedTorusJets
open EarlyDeterminantAdapter ExplicitCutoffAdapter
open scoped BigOperators NumberField

/-- The prime mass with precisely the same filter as the raw finite-place bound. -/
noncomputable def goodPrimeMass (D : ℕ) (χ : DirichletCharacter ℂ D) : ℝ := by
  classical
  exact ∑ p ∈ (Nat.primesLE ⌊(D : ℝ) ^ 32⌋₊).filter
    (fun p => 86713344 < p ∧ ¬ p ∣ 2 * D ∧ χ p = -1),
    Real.log p / (p : ℝ)

/-- Both finite size hypotheses follow already from D >= 97. -/
theorem finite_parameter_sizes {D : ℕ} (hD : 97 ≤ D) :
    86713344 ≤ D ^ 24 ∧ 18818 ≤ D ^ 24 := by
  have hfour : (97 : ℕ) ^ 4 ≤ D ^ 4 := pow_le_pow_left' hD 4
  have hlarge : D ^ 4 ≤ D ^ 24 :=
    pow_le_pow_right' (show 1 ≤ D by omega) (by norm_num)
  norm_num at hfour
  constructor <;> omega

/-- The natural row count agrees with the real parameter M. -/
theorem parameter_M (D : ℕ) :
    ((D ^ 24 : ℕ) : ℝ) ^ 4 = (D : ℝ) ^ 96 := by
  rw [Nat.cast_pow, ← pow_mul] <;> norm_num

/-- The rectangle scale agrees with the chosen U, with nonnegativity explicit. -/
theorem parameter_U (D : ℕ) :
    ((D ^ 24 : ℕ) : ℝ) ^ (4 / 3 : ℝ) = (D : ℝ) ^ 32 := by
  calc
    ((D ^ 24 : ℕ) : ℝ) ^ (4 / 3 : ℝ) =
        ((D : ℝ) ^ (24 : ℝ)) ^ (4 / 3 : ℝ) := by
      norm_num [Nat.cast_pow, Real.rpow_natCast]
    _ = (D : ℝ) ^ ((24 : ℝ) * (4 / 3)) :=
      (Real.rpow_mul (Nat.cast_nonneg D) _ _).symm
    _ = (D : ℝ) ^ 32 := by norm_num [Real.rpow_natCast]

theorem parameter_log_N (D : ℕ) :
    Real.log ((D ^ 24 : ℕ) : ℝ) = 24 * Real.log (D : ℝ) := by
  rw [Nat.cast_pow, Real.log_pow] <;> norm_num

theorem parameter_log_M (D : ℕ) :
    Real.log (((D ^ 24 : ℕ) : ℝ) ^ 4) = 96 * Real.log (D : ℝ) := by
  rw [parameter_M, Real.log_pow] <;> norm_num

/-- Pure numerical packaging of the raw bounds. S1, S2 and Q are supplied once;
all powers, logarithms, the mass scale and the row ratio are specialized here.
The bounds in this definition are exactly those returned by the raw theorem,
not a supplied DET bound or an assumed FiniteWitness. -/
noncomputable def finiteWitnessOfRawBounds
    {D : ℕ} (hD : 97 ≤ D) {m S1 S2 Q : ℝ}
    (hS2nonneg : 0 ≤ S2)
    (hprimary : ((D ^ 24 : ℕ) : ℝ) ^ 4 * (86713344 : ℝ) ^ (2 / 3 : ℝ) *
      ((D ^ 24 : ℕ) : ℝ) ^ (4 / 3 : ℝ) / (4 * 97 ^ 2) ≤ S1)
    (hsecondary : S2 ≤ 192 * ((D ^ 24 : ℕ) : ℝ) ^ 4 *
      (86713344 : ℝ) ^ (-(1 / 3 : ℝ)) * ((D ^ 24 : ℕ) : ℝ) ^ (4 / 3 : ℝ))
    (hfinite : S1 * m - Real.log 4 * ((D ^ 24 : ℕ) : ℝ) ^ 4 *
      (D : ℝ) ^ 32 ≤ Q)
    (harch : Q ≤ ((D ^ 24 : ℕ) : ℝ) ^ 4 / 2 *
      Real.log (((D ^ 24 : ℕ) : ℝ) ^ 4) + (S1 + S2) *
        (Real.log ((D ^ 24 : ℕ) : ℝ) + 1 / 2 * Real.log (D : ℝ) + Real.log 8)) :
    FiniteWitness (Real.log (D : ℝ)) explicitKappa ((D : ℝ) ^ 96)
      ((D : ℝ) ^ 32) m (Real.log 8) (Real.log 4) := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hNpos : (0 : ℝ) < (D ^ 24 : ℕ) := by
    rw [Nat.cast_pow]
    positivity
  have hscale := pivot_primary_scale
    (U := ((D ^ 24 : ℕ) : ℝ) ^ (4 / 3 : ℝ))
    (show (0 : ℝ) < 86713344 by norm_num)
  have hratio : S2 / S1 ≤ 1 / 12 := by
    apply pivot_ratio_le_twelfth
      (M := ((D ^ 24 : ℕ) : ℝ) ^ 4) (H := (86713344 : ℝ))
      (t := (86713344 : ℝ) ^ (-(1 / 3 : ℝ)) *
        ((D ^ 24 : ℕ) : ℝ) ^ (4 / 3 : ℝ))
      (by positivity) (by norm_num) (by positivity)
    · simpa only [mul_assoc, hscale] using hprimary
    · simpa only [mul_assoc] using hsecondary
  have hmass : explicitKappa * (D : ℝ) ^ 96 * (D : ℝ) ^ 32 ≤ S1 := by
    calc
      explicitKappa * (D : ℝ) ^ 96 * (D : ℝ) ^ 32 =
          (D : ℝ) ^ 96 * (86713344 : ℝ) ^ (2 / 3 : ℝ) *
            (D : ℝ) ^ 32 / (4 * 97 ^ 2) := by
        unfold explicitKappa
        ring
      _ ≤ S1 := by simpa only [parameter_M, parameter_U] using hprimary
  have hkpos : 0 < explicitKappa := lt_of_lt_of_le (by norm_num) explicitKappa_ge_one
  have hS1pos : 0 < S1 :=
    lt_of_lt_of_le
      (mul_pos (mul_pos hkpos (pow_pos hDpos _)) (pow_pos hDpos _)) hmass
  refine {
    S1 := S1
    S2 := S2
    Q := Q
    mass_lower := hmass
    row_ratio := ⟨div_nonneg hS2nonneg hS1pos.le, hratio⟩
    finite_lower := ?_
    arch_upper := ?_
  }
  · simpa only [parameter_M] using hfinite
  · rw [parameter_log_M, parameter_log_N, parameter_M] at harch
    convert harch using 1 <;> ring

attribute [local instance] canonicalCyclotomicLevelNeZero canonicalCyclotomicExtension
  canonicalCyclotomicNumberField canonicalCyclotomicAbelian

/-- The arithmetic FiniteWitness exists for every real primitive nonprincipal
character of conductor D >= 97. No finite-witness or DET premise is used.
The single raw theorem call supplies the same alpha and Delta to every field
of the record through `finiteWitnessOfRawBounds`. -/
theorem source_character_finiteWitness_nonempty
    (D : ℕ) (hD : 97 ≤ D) (χ : DirichletCharacter ℂ D)
    (hreal : ∀ x : ZMod D, (χ x).im = 0)
    (hprim : χ.IsPrimitive) (hne : χ ≠ 1) :
    Nonempty (FiniteWitness (Real.log (D : ℝ)) explicitKappa
      ((D : ℝ) ^ 96) ((D : ℝ) ^ 32) (goodPrimeMass D χ)
      (Real.log 8) (Real.log 4)) := by
  classical
  letI : NeZero D := ⟨by omega⟩
  obtain ⟨d, a, b, hd, hbound, hddiv, hns, ha, hb, hchar, hdisc, hfund, hformula,
    v, hv, hint, hdegree, σ, τ, hσa, hσb, hτa, hτb, hcard, hall, hcomm, hsource⟩ :=
    source_character_finite_greedy_determinant_same_witness_bounds_of_ninety_seven_le
      D hD χ hreal hprim hne
  let N : ℕ := D ^ 24
  let n : Fin (N ^ 4) ≃ (Fin 4 → Fin N) :=
    (Fintype.equivFinOfCardEq
      (show Fintype.card (Fin 4 → Fin N) = N ^ 4 by simp)).symm
  obtain ⟨e, he⟩ := exists_weight_sorted_enumeration
    (weightedJetIndices 86713344 (N ^ 4 - 1))
    (fun α : Fin 3 → ℕ => α 0 + 86713344 * α 1 + 86713344 * α 2)
  have hparams := finite_parameter_sizes hD
  obtain ⟨g, α, hg, hα, hrange, hmono, hweight, hprimary, hsecondary,
    Δ, hΔ, hneΔ, harch, hdiv, hfinite⟩ :=
    hsource N 86713344 (by norm_num) hparams.1 hparams.2 n e he
  let B := IntermediateField.adjoin ℚ ({a, b} : Set (CyclotomicField (8 * D) ℚ))
  have hfiniteU := hfinite ((D : ℝ) ^ 32) (by positivity)
  refine ⟨finiteWitnessOfRawBounds hD
    (m := goodPrimeMass D χ)
    (S1 := ∑ i, (α i 0 : ℝ))
    (S2 := ∑ i, ((α i 1 : ℝ) + α i 2))
    (Q := (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (Δ : B) : ℝ)|)
    ?_ ?_ ?_ ?_ ?_⟩
  · exact Finset.sum_nonneg fun i hi =>
      add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · simpa only [N, Nat.cast_ofNat] using hprimary
  · simpa only [N, Nat.cast_ofNat] using hsecondary
  · simpa only [N, goodPrimeMass] using hfiniteU.2.2
  · simpa only [N] using harch

/-- A chosen record, whose existence was proved directly from the raw source. -/
noncomputable def source_character_finiteWitness
    (D : ℕ) (hD : 97 ≤ D) (χ : DirichletCharacter ℂ D)
    (hreal : ∀ x : ZMod D, (χ x).im = 0)
    (hprim : χ.IsPrimitive) (hne : χ ≠ 1) :
    FiniteWitness (Real.log (D : ℝ)) explicitKappa
      ((D : ℝ) ^ 96) ((D : ℝ) ^ 32) (goodPrimeMass D χ)
      (Real.log 8) (Real.log 4) :=
  Classical.choice (source_character_finiteWitness_nonempty D hD χ hreal hprim hne)

/-- The unconditional determinant upper bound for the exact raw good-prime mass.
Here "unconditional" refers to the determinant input: the character assumptions
and the explicit conductor range remain in the statement. -/
theorem source_character_determinant_upper
    (D : ℕ) (hD : 97 ≤ D) (χ : DirichletCharacter ℂ D)
    (hreal : ∀ x : ZMod D, (χ x).im = 0)
    (hprim : χ.IsPrimitive) (hne : χ ≠ 1) :
    goodPrimeMass D χ / (32 * Real.log (D : ℝ)) ≤
      637 / 768 + ((13 / 12) * Real.log 8 + Real.log 4 / explicitKappa) /
        (32 * Real.log (D : ℝ)) + 3 / (2 * explicitKappa * (D : ℝ) ^ 32) := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hell : 0 < Real.log (D : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < D by omega))
  have hkpos : 0 < explicitKappa := lt_of_lt_of_le (by norm_num) explicitKappa_ge_one
  exact determinant_upper_log hell hkpos (pow_pos hDpos _) (pow_pos hDpos _)
    (source_character_finiteWitness D hD χ hreal hprim hne)

/-- At the larger cutoff, the same prime mass now needs only its analytic lower
estimate. There is no remaining finite determinant witness hypothesis. -/
theorem lower_bound_of_prime_mass
    (D : ℕ) (hD : 2 ^ 24 ≤ D) (χ : DirichletCharacter ℂ D)
    (hreal : ∀ x : ZMod D, (χ x).im = 0)
    (hprim : χ.IsPrimitive) (hne : χ ≠ 1) {t : ℝ}
    (hprime : 7 / 8 - 1 / (4 * Real.log (D : ℝ)) -
      14 * Real.log (D : ℝ) * t - 9 * (D : ℝ) ^ (-(3 / 2 : ℝ)) ≤
      goodPrimeMass D χ / (32 * Real.log (D : ℝ))) :
    1 / (1536 * Real.log (D : ℝ)) < t ∧
      1 / (4096 * Real.log (D : ℝ)) < t := by
  have h97 : 97 ≤ D := le_trans (by norm_num) hD
  exact lower_bound_from_same_witness_nat hD explicitKappa_ge_one hprime
    (source_character_finiteWitness D h97 χ hreal hprim hne)

#check goodPrimeMass
#check finite_parameter_sizes
#check parameter_M
#check parameter_U
#check parameter_log_N
#check parameter_log_M
#check finiteWitnessOfRawBounds
#check source_character_finiteWitness_nonempty
#check source_character_finiteWitness
#check source_character_determinant_upper
#check lower_bound_of_prime_mass

#print axioms finite_parameter_sizes
#print axioms parameter_M
#print axioms parameter_U
#print axioms parameter_log_N
#print axioms parameter_log_M
#print axioms finiteWitnessOfRawBounds
#print axioms source_character_finiteWitness_nonempty
#print axioms source_character_finiteWitness
#print axioms source_character_determinant_upper
#print axioms lower_bound_of_prime_mass

end RawWitnessAdapter
