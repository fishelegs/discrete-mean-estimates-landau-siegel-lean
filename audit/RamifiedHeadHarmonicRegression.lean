import ZhangLS.Spec.RamifiedHeadHarmonicBound

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Finset
open scoped Classical

/-- An inhabited, actual primitive real conductor-one endpoint. -/
noncomputable def ramifiedHeadUnitCharacter : RealPrimitiveCharacter 1 where
  chi := 1
  primitive := DirichletCharacter.isPrimitive_one_level_one
  real_valued := by
    intro a
    have ha : a = 1 := Subsingleton.elim _ _
    rw [ha]
    simp
  quadratic := by simp
  modulus_pos := by norm_num

/-- At D=X=1 the literal actual sum equals its sharp upper bound one. -/
theorem ramifiedHead_unit_endpoint :
    (∑ d ∈ Icc 1 1, ∑ m ∈ (Icc 1 1).filter (fun m => 1 ∣ d*m),
      ‖lemma23UpsilonArithmeticFunction ramifiedHeadUnitCharacter d‖ *
        ‖lemma23NuArithmeticFunction ramifiedHeadUnitCharacter m‖ *
        (lemma34Tau 4 d : ℝ) * (lemma34Tau 4 m : ℝ) /
        ((d : ℝ)*(m : ℝ))) = 1 := by
  have hu := (lemma36_upsilon_multiplicative ramifiedHeadUnitCharacter).map_one
  have hn := lemma31_actual_nu_one ramifiedHeadUnitCharacter
  have ht := (lemma34_tau_multiplicative 4).map_one
  change lemma34Tau 4 1 = 1 at ht
  simp [hu, hn, ht]

/-- The literal X=1 sum has no terms for any larger conductor. -/
theorem ramifiedHead_one_cutoff_empty {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) :
    (∑ d ∈ Icc 1 1, ∑ m ∈ (Icc 1 1).filter (fun m => D ∣ d*m),
      ‖lemma23UpsilonArithmeticFunction χ d‖ * ‖lemma23NuArithmeticFunction χ m‖ *
        (lemma34Tau 4 d : ℝ) * (lemma34Tau 4 m : ℝ) / ((d : ℝ)*(m : ℝ))) = 0 := by
  have h : ¬ D ∣ 1 := by intro h; have := Nat.le_of_dvd (by omega : 0 < 1) h; omega
  simp [sum_filter, h]

/-- Non-squarefree and overlapping ramification: neither q nor n is a unit
modulo the composite conductor twelve. -/
theorem ramifiedHead_composite_overlap (χ : RealPrimitiveCharacter 12) :
    lemma23NuArithmeticFunction χ 36 = lemma23NuArithmeticFunction χ 6 := by
  exact ramifiedHead_nu_mul_divisor (n := 6) χ (by omega) (by norm_num : 6 ∣ 12)

/-- A conductor prime-square may overlap the argument at still higher order. -/
theorem ramifiedHead_prime_power_overlap (χ : RealPrimitiveCharacter 8) :
    lemma23NuArithmeticFunction χ 32 = lemma23NuArithmeticFunction χ 4 := by
  exact ramifiedHead_nu_mul_divisor (n := 4) χ (by omega) (by norm_num : 8 ∣ 8)

/-- The zero convention is handled before factorization is used. -/
theorem ramifiedHead_zero_argument (χ : RealPrimitiveCharacter 12) :
    lemma23NuArithmeticFunction χ (6*0) = lemma23NuArithmeticFunction χ 0 :=
  ramifiedHead_nu_mul_divisor χ (by omega) (by norm_num : 6 ∣ 12)

/-- The actual logarithmic capstone is applied at the inhabited unit endpoint. -/
example :
    (∑ d ∈ Icc 1 1, ∑ m ∈ (Icc 1 1).filter (fun m => 1 ∣ d*m),
      ‖lemma23UpsilonArithmeticFunction ramifiedHeadUnitCharacter d‖ *
        ‖lemma23NuArithmeticFunction ramifiedHeadUnitCharacter m‖ *
        (lemma34Tau 4 d : ℝ) * (lemma34Tau 4 m : ℝ) / ((d : ℝ)*(m : ℝ))) ≤
      (lemma34Tau 8 1 : ℝ)/(1 : ℝ)*(1+Real.log (1 : ℝ))^16 := by
  simpa only [Nat.cast_one] using
    ramifiedHead_actual_log_le (X := 1) ramifiedHeadUnitCharacter (by omega) (by omega)

/-- Composite conductor regression invokes the actual coefficient capstone. -/
example (χ : RealPrimitiveCharacter 12) :
    (∑ d ∈ Icc 1 36, ∑ m ∈ (Icc 1 36).filter (fun m => 12 ∣ d*m),
      ‖lemma23UpsilonArithmeticFunction χ d‖ * ‖lemma23NuArithmeticFunction χ m‖ *
        (lemma34Tau 4 d : ℝ) * (lemma34Tau 4 m : ℝ) / ((d : ℝ)*(m : ℝ))) ≤
      (lemma34Tau 8 12 : ℝ)/(12 : ℝ)*(harmonic 36 : ℝ)^16 :=
  ramifiedHead_actual_harmonic_le (X := 36) χ (by omega) (by omega)

/-- The split retains a quotient sharing a prime with D; it requires only
coprimality with D/g. -/
theorem ramifiedHead_composite_split :
    ramifiedHeadSplit 12 (18, 4) = (6, 3, 2) := by
  norm_num [ramifiedHeadSplit]

/-- The finite source set admits the retained overlapping tuple. -/
theorem ramifiedHead_composite_pair_retained :
    (18, 4) ∈ ramifiedHeadPairs 12 18 := by
  norm_num [ramifiedHeadPairs, mem_filter, mem_product, mem_Icc]

/-- Excluding zero is a literal property of the source index set. -/
theorem ramifiedHead_zero_index_excluded (D X : ℕ) :
    (0, 1) ∉ ramifiedHeadPairs D X := by
  simp [ramifiedHeadPairs]

end ZhangLS.Spec
