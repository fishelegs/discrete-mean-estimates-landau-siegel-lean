import FixedQuadratic.MinorEnvelope
import FixedQuadratic.MultiLower

open scoped BigOperators
open Polynomial
namespace FixedQuadratic

noncomputable def formalMinor {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (T : Fin m → ℕ) (j s h : ι → ℕ) (b a : ι → Fin m → ℕ) : MvPolynomial (Fin m) ℂ :=
  Matrix.det (fun r c => formalEntry (fun _ => 2*(j r : ℂ)*Complex.I)
    (fun i => truncatedLog (T i)) (s r) (h c) (b r) (a c))

noncomputable def minorDegrees {ι : Type*} [Fintype ι] {m : ℕ}
    (a b : ι → Fin m → ℕ) (i : Fin m) : ℕ := (∑ c, a c i)-(∑ r, b r i)

noncomputable def minorDenominator {ι : Type*} [Fintype ι] {m : ℕ}
    (T : Fin m → ℕ) (a b : ι → Fin m → ℕ) : ℕ :=
  ∏ i, (logDenominator (T i))^(minorDegrees a b i)

theorem minorDenominator_pos {ι : Type*} [Fintype ι] {m : ℕ}
    (T : Fin m → ℕ) (a b : ι → Fin m → ℕ) : 0 < minorDenominator T a b :=
  Finset.prod_pos (fun _ _ => pow_pos (logDenominator_pos _) _)

theorem gaussian_degreeOf_of_map {m : ℕ} (P : MvPolynomial (Fin m) GaussianInt)
    (e : Fin m → ℕ) (he : ∀ i, (MvPolynomial.map GaussianInt.toComplex P).degreeOf i ≤ e i) :
    ∀ i, P.degreeOf i ≤ e i := by
  intro i
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro α hα
  apply MvPolynomial.degreeOf_le_iff.mp (he i) α
  apply MvPolynomial.mem_support_iff.mpr
  rw [MvPolynomial.coeff_map]
  exact fun hh => (MvPolynomial.mem_support_iff.mp hα)
    (GaussianInt.toComplex_injective (by simpa using hh))

/-- Constructs an actual Gaussian coefficient polynomial from the actual
truncated-log minor, preserving its coordinate degree rebate. -/
theorem exists_gaussian_cleared_minor {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (T : Fin m → ℕ) (j s h : ι → ℕ) (b a : ι → Fin m → ℕ) :
    ∃ P : MvPolynomial (Fin m) GaussianInt,
      MvPolynomial.map GaussianInt.toComplex P =
        MvPolynomial.C (minorDenominator T a b : ℂ)*formalMinor T j s h b a ∧
      ∀ i, P.degreeOf i ≤ minorDegrees a b i := by
  classical
  obtain ⟨P, hP⟩ := formal_minor_truncatedLog_cleared_gaussian T j s h b a
  have hQ : (∏ i, (MvPolynomial.C (logDenominator (T i) : ℂ))^
      ((∑ c, a c i)-(∑ r, b r i)) : MvPolynomial (Fin m) ℂ) =
      MvPolynomial.C (minorDenominator T a b : ℂ) := by
    simp [minorDenominator, minorDegrees]
  rw [hQ] at hP
  refine ⟨P, hP, gaussian_degreeOf_of_map P _ ?_⟩
  intro i
  rw [hP]
  exact (MvPolynomial.degreeOf_C_mul_le _ i _).trans
    (formal_minor_degree _ _ _ _ _ _ _)

/-- The actual log minor arithmetic replacement: Q occurs twice, the
coefficient envelope once, and each Mahler factor to the exact rebate e_i.
The field/minimal-polynomial data and the minor's nonvanishing are explicit;
no pi finiteness theorem or interpolation existence is asserted. -/
theorem formal_minor_fixed_field_arithmetic {G K ι : Type*} [Field G] [Field K]
    [NumberField K] [Algebra GaussianInt G] [IsFractionRing GaussianInt G]
    [Algebra G K] [Algebra GaussianInt K] [IsScalarTower GaussianInt G K]
    [FiniteDimensional G K] [IsGalois G K] [Fintype ι] [DecidableEq ι] {m : ℕ}
    (hdegree : Module.finrank G K = 2) (τ : K ≃ₐ[G] K) (hτ : τ ≠ 1)
    (T : Fin m → ℕ) (k : ℕ) (j s h : ι → ℕ) (b a : ι → Fin m → ℕ)
    (hj : ∀ r, j r ≤ k) (la lb lc : Fin m → ℤ) (x : Fin m → K)
    (hprim : ∀ i, Int.gcd (Int.gcd (la i) (lb i) : ℤ) (lc i) = 1)
    (hf : ∀ i, C (la i : K)*X^2+C (lb i : K)*X+C (lc i : K) =
      C (la i : K)*((X-C (x i))*(X-C (τ (x i)))))
    (ha : ∀ i, la i ≠ 0) (φ : K →+* ℂ)
    (hφ : φ.comp (algebraMap GaussianInt K) = GaussianInt.toComplex)
    (hne : MvPolynomial.eval (fun i => φ (x i)) (formalMinor T j s h b a) ≠ 0) :
    (∏ i, (max 1 ‖φ (x i)‖)^(minorDegrees a b i)) ≤
      (minorDenominator T a b : ℝ)^2 *
      ((Fintype.card ι).factorial * 2^(∑ r, s r) * (3/2)^(∑ c, h c) *
        2^(∑ c, ∑ i, a c i) * (2*k+2)^(∑ i, minorDegrees a b i)) *
      (∏ i, (‖φ (la i : K)‖ * max 1 ‖φ (x i)‖ * max 1 ‖φ (τ (x i))‖)^(minorDegrees a b i)) *
      ‖MvPolynomial.eval (fun i => φ (x i)) (formalMinor T j s h b a)‖ := by
  classical
  obtain ⟨P, hP, he⟩ := exists_gaussian_cleared_minor T j s h b a
  have hEval : φ (MvPolynomial.eval₂ (algebraMap GaussianInt K) x P) =
      (minorDenominator T a b : ℂ) *
        MvPolynomial.eval (fun i => φ (x i)) (formalMinor T j s h b a) := by
    rw [MvPolynomial.eval₂_comp_left, hφ, ← MvPolynomial.eval_map, hP,
      MvPolynomial.eval_mul, MvPolynomial.eval_C]
    rfl
  have hQ : 0 < (minorDenominator T a b : ℝ) := by exact_mod_cast minorDenominator_pos T a b
  have hQC : (minorDenominator T a b : ℂ) ≠ 0 := by
    exact_mod_cast (minorDenominator_pos T a b).ne'
  have hx : MvPolynomial.eval₂ (algebraMap GaussianInt K) x P ≠ 0 := by
    intro hz
    have hh := congrArg φ hz
    rw [hEval, map_zero] at hh
    exact mul_ne_zero hQC hne hh
  have hlower := quadratic_multi_l1_mahler_lower hdegree τ hτ P la lb lc x
    (minorDegrees a b) he hprim hf ha hx φ hφ
  have hB := multiCoefficientL1_pos_of_eval_ne_zero (MvPolynomial.map GaussianInt.toComplex P)
    (fun i => φ (x i)) (by rw [hP, MvPolynomial.eval_mul, MvPolynomial.eval_C]; exact mul_ne_zero hQC hne)
  have hM : 0 < ∏ i, (‖φ (la i : K)‖ * max 1 ‖φ (x i)‖ *
      max 1 ‖φ (τ (x i))‖)^(minorDegrees a b i) := by
    apply Finset.prod_pos
    intro i hi
    apply pow_pos
    have hc : 0 < ‖φ (la i : K)‖ := norm_pos_iff.mpr ((_root_.map_ne_zero φ).mpr
      (by exact_mod_cast ha i))
    have hR : 0 < max 1 ‖φ (x i)‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have hS : 0 < max 1 ‖φ (τ (x i))‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    exact mul_pos (mul_pos hc hR) hS
  have hp := (div_le_iff₀ (mul_pos hB hM)).mp hlower
  rw [hEval, norm_mul, Complex.norm_natCast] at hp
  have hcoef := cleared_formal_minor_truncatedLog_l1_le T k j s h b a hj
  have hQpoly : (∏ i, (MvPolynomial.C (logDenominator (T i) : ℂ))^
      ((∑ c, a c i)-(∑ r, b r i)) : MvPolynomial (Fin m) ℂ) =
      MvPolynomial.C (minorDenominator T a b : ℂ) := by simp [minorDenominator, minorDegrees]
  rw [hQpoly] at hcoef
  have hQreal : (∏ i, (logDenominator (T i) : ℝ)^((∑ c, a c i)-(∑ r, b r i))) =
      (minorDenominator T a b : ℝ) := by simp [minorDenominator, minorDegrees]
  rw [hQreal] at hcoef
  change multiCoefficientL1 (MvPolynomial.C (minorDenominator T a b : ℂ)*
    formalMinor T j s h b a) ≤ _ at hcoef
  rw [← hP] at hcoef
  have hh := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hcoef hM.le)
    (show 0 ≤ (minorDenominator T a b : ℝ)*
      ‖MvPolynomial.eval (fun i => φ (x i)) (formalMinor T j s h b a)‖ by positivity)
  apply hp.trans
  convert hh using 1
  simp only [minorDegrees]
  ring

end FixedQuadratic
