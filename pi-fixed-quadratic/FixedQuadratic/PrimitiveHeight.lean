import FixedQuadratic.Height
import FixedQuadratic.Mahler
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.GaussLemma

open Polynomial
namespace FixedQuadratic

noncomputable def integerMinpoly (x : ℝ) : Polynomial ℤ :=
  IsLocalization.integerNormalization (nonZeroDivisors ℤ) (minpoly ℚ x)

noncomputable def primitiveMinpoly (x : ℝ) : Polynomial ℤ :=
  let p := (integerMinpoly x).primPart
  if 0 < p.leadingCoeff then p else -p

/-- Maximum coefficient height, with no square-root Weil-height convention. -/
noncomputable def primitiveMinpolyHeight (x : ℝ) : ℕ :=
  max ((primitiveMinpoly x).coeff 2).natAbs
    (max ((primitiveMinpoly x).coeff 1).natAbs ((primitiveMinpoly x).coeff 0).natAbs)

theorem integerMinpoly_natDegree (x : ℝ) :
    (integerMinpoly x).natDegree = (minpoly ℚ x).natDegree := by
  obtain ⟨d, hd, he⟩ := IsLocalization.integerNormalization_spec
    (nonZeroDivisors ℤ) (minpoly ℚ x)
  have hh := congrArg Polynomial.natDegree he
  rw [natDegree_map_eq_of_injective (IsFractionRing.injective ℤ ℚ),
    natDegree_smul _ (nonZeroDivisors.ne_zero hd)] at hh
  exact hh

theorem primitiveMinpoly_natDegree (x : ℝ) :
    (primitiveMinpoly x).natDegree = (minpoly ℚ x).natDegree := by
  dsimp only [primitiveMinpoly]
  split_ifs <;> simp [natDegree_primPart, integerMinpoly_natDegree, natDegree_neg]

theorem primitiveMinpoly_primitive (x : ℝ) : (primitiveMinpoly x).IsPrimitive := by
  dsimp only [primitiveMinpoly]
  split_ifs
  · exact isPrimitive_primPart _
  · apply isPrimitive_of_dvd (isPrimitive_primPart _)
    exact neg_dvd.mpr dvd_rfl

theorem primitiveMinpoly_leadingCoeff_pos (x : ℝ) :
    0 < (primitiveMinpoly x).leadingCoeff := by
  have hn := leadingCoeff_ne_zero.mpr (primPart_ne_zero (integerMinpoly x))
  dsimp only [primitiveMinpoly]
  split_ifs with hp
  · exact hp
  · rw [leadingCoeff_neg]
    omega

theorem integral_of_minpoly_degree_two (x : ℝ) (hx : (minpoly ℚ x).natDegree = 2) :
    IsIntegral ℚ x := by
  apply minpoly.ne_zero_iff.mp
  intro hz
  rw [hz, natDegree_zero] at hx
  omega

theorem primitiveMinpoly_aeval (x : ℝ) (hx : (minpoly ℚ x).natDegree = 2) :
    aeval x (primitiveMinpoly x) = 0 := by
  have hraw := IsLocalization.integerNormalization_aeval_eq_zero
    (nonZeroDivisors ℤ) (minpoly ℚ x) (minpoly.aeval ℚ x)
  have hraw0 : integerMinpoly x ≠ 0 := by
    intro hz
    have hh := integerMinpoly_natDegree x
    rw [hz, natDegree_zero, hx] at hh
    omega
  have hp := aeval_primPart_eq_zero hraw0 hraw
  dsimp only [primitiveMinpoly]
  split_ifs <;> simp [hp]

theorem quadratic_eq_coefficients (p : Polynomial ℤ) (hp : p.natDegree = 2) :
    p = C (p.coeff 2)*X^2+C (p.coeff 1)*X+C (p.coeff 0) := by
  have hh := p.as_sum_range_C_mul_X_pow
  rw [hp] at hh
  simp only [Nat.reduceAdd, Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add, pow_zero, pow_one, mul_one] at hh
  convert hh using 1
  ring

theorem primitiveMinpoly_coeff_two_pos (x : ℝ) (hx : (minpoly ℚ x).natDegree = 2) :
    0 < (primitiveMinpoly x).coeff 2 := by
  have hh := primitiveMinpoly_leadingCoeff_pos x
  rwa [leadingCoeff, primitiveMinpoly_natDegree, hx] at hh

theorem primitiveMinpoly_map_associated (x : ℝ) (hx : (minpoly ℚ x).natDegree = 2) :
    Associated (minpoly ℚ x) ((primitiveMinpoly x).map (algebraMap ℤ ℚ)) := by
  have hd : minpoly ℚ x ∣ (primitiveMinpoly x).map (algebraMap ℤ ℚ) := by
    apply minpoly.dvd ℚ x
    rw [aeval_map_algebraMap]
    exact primitiveMinpoly_aeval x hx
  apply associated_of_dvd_of_natDegree_le hd
  · intro hz
    apply (primitiveMinpoly_primitive x).ne_zero
    apply Polynomial.map_injective (algebraMap ℤ ℚ) (IsFractionRing.injective ℤ ℚ)
    simpa using hz
  · rw [natDegree_map_eq_of_injective (IsFractionRing.injective ℤ ℚ), primitiveMinpoly_natDegree]

theorem primitiveMinpoly_irreducible (x : ℝ) (hx : (minpoly ℚ x).natDegree = 2) :
    Irreducible (primitiveMinpoly x) := by
  apply (primitiveMinpoly_primitive x).irreducible_of_irreducible_map_of_injective
    (IsFractionRing.injective ℤ ℚ)
  exact (primitiveMinpoly_map_associated x hx).irreducible
    (minpoly.irreducible (integral_of_minpoly_degree_two x hx))

theorem primitiveMinpoly_three_gcd (x : ℝ) (hx : (minpoly ℚ x).natDegree = 2) :
    Int.gcd (Int.gcd ((primitiveMinpoly x).coeff 2) ((primitiveMinpoly x).coeff 1) : ℤ)
      ((primitiveMinpoly x).coeff 0) = 1 := by
  have hc := (primitiveMinpoly_primitive x).content_eq_one
  rw [content_eq_gcd_range_succ, primitiveMinpoly_natDegree, hx] at hc
  norm_num [Finset.range_add_one, Finset.gcd_insert] at hc
  apply Nat.cast_injective (R := ℤ)
  simp only [Int.coe_gcd, Nat.cast_one]
  rw [gcd_assoc, (associated_normalize ((primitiveMinpoly x).coeff 0)).gcd_eq_right]
  exact hc

/-- Discharges the earlier coefficient-box interface for this actual
primitive integer minpoly construction on degree-exactly-two real elements. -/
theorem primitiveMinpolyHeight_box (x : ℝ) (hx : (minpoly ℚ x).natDegree = 2)
    (H : ℕ) (hH : primitiveMinpolyHeight x ≤ H) : x ∈ boundedQuadraticRoots H := by
  have h2 : ((primitiveMinpoly x).coeff 2).natAbs ≤ H := (le_max_left _ _).trans hH
  have h1 : ((primitiveMinpoly x).coeff 1).natAbs ≤ H :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hH)
  have h0 : ((primitiveMinpoly x).coeff 0).natAbs ≤ H :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hH)
  have h2Z : |(primitiveMinpoly x).coeff 2| ≤ (H : ℤ) := by
    simpa only [Int.natCast_natAbs] using (Nat.cast_le.mpr h2 :
      (((primitiveMinpoly x).coeff 2).natAbs : ℤ) ≤ H)
  have h1Z : |(primitiveMinpoly x).coeff 1| ≤ (H : ℤ) := by
    simpa only [Int.natCast_natAbs] using (Nat.cast_le.mpr h1 :
      (((primitiveMinpoly x).coeff 1).natAbs : ℤ) ≤ H)
  have h0Z : |(primitiveMinpoly x).coeff 0| ≤ (H : ℤ) := by
    simpa only [Int.natCast_natAbs] using (Nat.cast_le.mpr h0 :
      (((primitiveMinpoly x).coeff 0).natAbs : ℤ) ≤ H)
  apply mem_boundedQuadraticRoots H ((primitiveMinpoly x).coeff 2)
    ((primitiveMinpoly x).coeff 1) ((primitiveMinpoly x).coeff 0) x
    (by have := primitiveMinpoly_coeff_two_pos x hx; omega)
    ((le_abs_self _).trans h2Z) h1Z h0Z
  have hh := primitiveMinpoly_aeval x hx
  rw [quadratic_eq_coefficients (primitiveMinpoly x) (by rw [primitiveMinpoly_natDegree, hx])] at hh
  simpa using hh

theorem primitiveMinpolyHeight_unbounded (S : Set ℝ) (hS : S.Infinite)
    (hdegree : ∀ x ∈ S, (minpoly ℚ x).natDegree = 2) :
    ∀ H, ∃ x ∈ S, H < primitiveMinpolyHeight x := by
  apply height_unbounded_of_infinite S primitiveMinpolyHeight hS
  intro x hx H hH
  exact primitiveMinpolyHeight_box x (hdegree x hx) H hH

noncomputable def primitiveConjugate (x : ℝ) : ℝ :=
  -((primitiveMinpoly x).coeff 1 : ℝ)/((primitiveMinpoly x).coeff 2 : ℝ)-x

theorem primitiveMinpoly_root_relations (x : ℝ) (hx : (minpoly ℚ x).natDegree = 2) :
    ((primitiveMinpoly x).coeff 1 : ℝ) =
      -((primitiveMinpoly x).coeff 2 : ℝ)*(x+primitiveConjugate x) ∧
    ((primitiveMinpoly x).coeff 0 : ℝ) =
      ((primitiveMinpoly x).coeff 2 : ℝ)*x*primitiveConjugate x := by
  have ha : ((primitiveMinpoly x).coeff 2 : ℝ) ≠ 0 := by
    exact_mod_cast (primitiveMinpoly_coeff_two_pos x hx).ne'
  have hr := primitiveMinpoly_aeval x hx
  rw [quadratic_eq_coefficients (primitiveMinpoly x)
    (by rw [primitiveMinpoly_natDegree, hx])] at hr
  simp only [map_add, map_mul, map_pow, aeval_C, aeval_X] at hr
  change ((primitiveMinpoly x).coeff 2 : ℝ)*x^2+
    ((primitiveMinpoly x).coeff 1 : ℝ)*x+((primitiveMinpoly x).coeff 0 : ℝ) = 0 at hr
  have hb : ((primitiveMinpoly x).coeff 1 : ℝ) =
      -((primitiveMinpoly x).coeff 2 : ℝ)*(x+primitiveConjugate x) := by
    unfold primitiveConjugate
    field_simp
    ring
  refine ⟨hb, ?_⟩
  rw [hb] at hr
  nlinarith only [hr]

/-- An actual maximum-coefficient height, rather than a height supplied as a
hypothesis, bounds the Mahler measure of the actual primitive minpoly. -/
theorem primitiveMinpoly_mahler_le (x : ℝ) (hx : (minpoly ℚ x).natDegree = 2) :
    quadraticMahler ((primitiveMinpoly x).coeff 2 : ℝ) x (primitiveConjugate x) ≤
      Real.sqrt 3*(primitiveMinpolyHeight x : ℝ) := by
  have h2 : ((primitiveMinpoly x).coeff 2).natAbs ≤ primitiveMinpolyHeight x :=
    le_max_left _ _
  have h1 : ((primitiveMinpoly x).coeff 1).natAbs ≤ primitiveMinpolyHeight x :=
    (le_max_left _ _).trans (le_max_right _ _)
  have h0 : ((primitiveMinpoly x).coeff 0).natAbs ≤ primitiveMinpolyHeight x :=
    (le_max_right _ _).trans (le_max_right _ _)
  have ha : 0 < ((primitiveMinpoly x).coeff 2 : ℝ) := by
    exact_mod_cast primitiveMinpoly_coeff_two_pos x hx
  have h2R : |((primitiveMinpoly x).coeff 2 : ℝ)| ≤ (primitiveMinpolyHeight x : ℝ) := by
    exact_mod_cast (show |(primitiveMinpoly x).coeff 2| ≤ (primitiveMinpolyHeight x : ℤ) by
      simpa only [Int.natCast_natAbs] using (Nat.cast_le.mpr h2 :
        (((primitiveMinpoly x).coeff 2).natAbs : ℤ) ≤ primitiveMinpolyHeight x))
  have h1R : |((primitiveMinpoly x).coeff 1 : ℝ)| ≤ (primitiveMinpolyHeight x : ℝ) := by
    exact_mod_cast (show |(primitiveMinpoly x).coeff 1| ≤ (primitiveMinpolyHeight x : ℤ) by
      simpa only [Int.natCast_natAbs] using (Nat.cast_le.mpr h1 :
        (((primitiveMinpoly x).coeff 1).natAbs : ℤ) ≤ primitiveMinpolyHeight x))
  have h0R : |((primitiveMinpoly x).coeff 0 : ℝ)| ≤ (primitiveMinpolyHeight x : ℝ) := by
    exact_mod_cast (show |(primitiveMinpoly x).coeff 0| ≤ (primitiveMinpolyHeight x : ℤ) by
      simpa only [Int.natCast_natAbs] using (Nat.cast_le.mpr h0 :
        (((primitiveMinpoly x).coeff 0).natAbs : ℤ) ≤ primitiveMinpolyHeight x))
  obtain ⟨hb, hc⟩ := primitiveMinpoly_root_relations x hx
  exact quadraticMahler_le_sqrt_three_height _ _ _ _ _ _ ha.le (by positivity)
    ((le_abs_self _).trans h2R) h1R h0R hb hc

theorem primitiveMinpolyHeight_pos (x : ℝ) (hx : (minpoly ℚ x).natDegree = 2) :
    0 < primitiveMinpolyHeight x := by
  have hh : 0 < ((primitiveMinpoly x).coeff 2).natAbs :=
    Int.natAbs_pos.mpr (primitiveMinpoly_coeff_two_pos x hx).ne'
  exact hh.trans_le (le_max_left _ _)

theorem primitiveMinpoly_real_factorization (x : ℝ) (hx : (minpoly ℚ x).natDegree = 2) :
    (primitiveMinpoly x).map (algebraMap ℤ ℝ) =
      C ((primitiveMinpoly x).coeff 2 : ℝ)*((X-C x)*(X-C (primitiveConjugate x))) := by
  conv_lhs => rw [quadratic_eq_coefficients (primitiveMinpoly x)
    (by rw [primitiveMinpoly_natDegree, hx])]
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_C, Polynomial.map_X]
  change C ((primitiveMinpoly x).coeff 2 : ℝ)*X^2+
    C ((primitiveMinpoly x).coeff 1 : ℝ)*X+C ((primitiveMinpoly x).coeff 0 : ℝ) = _
  obtain ⟨hb, hc⟩ := primitiveMinpoly_root_relations x hx
  rw [hb, hc]
  simp only [map_neg, map_mul, map_add]
  ring

/-- Directly connects actual primitive max height to the selected ceiling
weight used by the determinant argument. -/
theorem primitiveMinpoly_mahler_log_le (x : ℝ) (hx : (minpoly ℚ x).natDegree = 2) :
    Real.log (quadraticMahler ((primitiveMinpoly x).coeff 2 : ℝ) x (primitiveConjugate x)) ≤
      (Nat.ceil (Real.log (primitiveMinpolyHeight x : ℝ)) : ℝ)+Real.log (Real.sqrt 3) := by
  have ha : 0 < ((primitiveMinpoly x).coeff 2 : ℝ) := by
    exact_mod_cast primitiveMinpoly_coeff_two_pos x hx
  have hH : 0 < (primitiveMinpolyHeight x : ℝ) := by
    exact_mod_cast primitiveMinpolyHeight_pos x hx
  have hM : 0 < quadraticMahler ((primitiveMinpoly x).coeff 2 : ℝ) x (primitiveConjugate x) := by
    unfold quadraticMahler
    exact mul_pos (mul_pos ha (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))
      (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  have hs : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hh := Real.log_le_log hM (primitiveMinpoly_mahler_le x hx)
  rw [Real.log_mul hs.ne' hH.ne'] at hh
  have hc := Nat.le_ceil (Real.log (primitiveMinpolyHeight x : ℝ))
  linarith

end FixedQuadratic
