import FixedQuadratic.FormalEntry
import FixedQuadratic.Clearing
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Algebra.Polynomial.Eval.Subring
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.Trunc

open Polynomial
namespace FixedQuadratic

noncomputable def truncatedLog (T : ℕ) : Polynomial ℂ :=
  PowerSeries.trunc T (PowerSeries.log ℂ)

/-- Exact lcm of 1,...,T-1; it is 1 for T=0 or T=1. -/
def logDenominator (T : ℕ) : ℕ := Nat.lcmUpto (T-1)

theorem logDenominator_pos (T : ℕ) : 0 < logDenominator T := Nat.lcmUpto_pos _

theorem logDenominator_log_coeff (T k : ℕ) (hk : k < T) :
    (logDenominator T : ℂ)*PowerSeries.coeff k (PowerSeries.log ℂ) ∈
      GaussianInt.toComplex.range := by
  by_cases hk0 : k = 0
  · simp [hk0]
  have hd : k ∣ logDenominator T :=
    Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  obtain ⟨n, hn⟩ := hd
  refine ⟨(-1 : GaussianInt)^(k+1)*(n : GaussianInt), ?_⟩
  rw [PowerSeries.coeff_log, ite_eq_right hk0, hn]
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk0
  simp only [map_mul, map_pow, map_neg, map_one, map_natCast, map_div₀, Nat.cast_mul]
  field_simp

theorem cleared_truncatedLog_gaussian (T : ℕ) :
    C (logDenominator T : ℂ)*truncatedLog T ∈
      (Polynomial.mapRingHom GaussianInt.toComplex).range := by
  apply (Polynomial.mem_map_range GaussianInt.toComplex).mpr
  intro k
  rw [Polynomial.coeff_C_mul, truncatedLog, PowerSeries.coeff_trunc]
  split_ifs with hk
  · exact logDenominator_log_coeff T k hk
  · simp

theorem scalar_product_mul_coeff {R : Type*} [CommRing R] {m : ℕ}
    (q : Fin m → R) (d : Fin m → ℕ) (P : Polynomial R)
    (F : Fin m → Polynomial R) (s : ℕ) :
    (∏ i, q i^d i)*(P*∏ i, (F i)^d i).coeff s =
      (P*∏ i, (C (q i)*F i)^d i).coeff s := by
  have he : P*∏ i, (C (q i)*F i)^d i =
      C (∏ i, q i^d i)*(P*∏ i, (F i)^d i) := by
    simp only [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod]
    ring
  rw [he, Polynomial.coeff_C_mul]

theorem cleared_lifted_truncatedLog_gaussian {m : ℕ} (T : ℕ) :
    C (MvPolynomial.C (logDenominator T : ℂ)) *
      (truncatedLog T).map MvPolynomial.C ∈
        (Polynomial.mapRingHom (MvPolynomial.map GaussianInt.toComplex :
          MvPolynomial (Fin m) GaussianInt →+* MvPolynomial (Fin m) ℂ)).range := by
  apply (Polynomial.mem_map_range _).mpr
  intro k
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_map]
  have h := (Polynomial.mem_map_range GaussianInt.toComplex).mp
    (cleared_truncatedLog_gaussian T) k
  rw [Polynomial.coeff_C_mul] at h
  obtain ⟨z, hz⟩ := h
  refine ⟨MvPolynomial.C z, ?_⟩
  simpa [← map_mul] using congrArg (MvPolynomial.C : ℂ →+* MvPolynomial (Fin m) ℂ) hz

theorem cleared_center_gaussian {m : ℕ} (T j : ℕ) (i : Fin m) :
    C (MvPolynomial.C (logDenominator T : ℂ)) *
      C (MvPolynomial.C (2*(j : ℂ)*Complex.I)*MvPolynomial.X i) ∈
        (Polynomial.mapRingHom (MvPolynomial.map GaussianInt.toComplex :
          MvPolynomial (Fin m) GaussianInt →+* MvPolynomial (Fin m) ℂ)).range := by
  have hc : ((⟨0, 2*(j : ℤ)*(logDenominator T : ℤ)⟩ : GaussianInt) : ℂ) =
      (logDenominator T : ℂ)*(2*(j : ℂ)*Complex.I) := by
    simp [GaussianInt.toComplex_def']; ring
  refine ⟨C (MvPolynomial.C (⟨0, 2*(j : ℤ)*(logDenominator T : ℤ)⟩ : GaussianInt)*
    MvPolynomial.X i), ?_⟩
  simp only [Polynomial.coe_mapRingHom, Polynomial.map_C, map_mul,
    MvPolynomial.map_C, MvPolynomial.map_X, hc]
  ring

theorem cleared_shifted_truncatedLog_gaussian {m : ℕ} (T j : ℕ) (i : Fin m) :
    C (MvPolynomial.C (logDenominator T : ℂ)) *
      (C (MvPolynomial.C (2*(j : ℂ)*Complex.I)*MvPolynomial.X i) +
        (truncatedLog T).map MvPolynomial.C) ∈
        (Polynomial.mapRingHom (MvPolynomial.map GaussianInt.toComplex :
          MvPolynomial (Fin m) GaussianInt →+* MvPolynomial (Fin m) ℂ)).range := by
  rw [mul_add]
  exact Subring.add_mem _ (cleared_center_gaussian T j i)
    (cleared_lifted_truncatedLog_gaussian T)

/-- Every actual truncated-log formal entry is cleared with its coordinate
differences. No abstract entry-membership hypothesis remains. -/
theorem formalEntry_truncatedLog_cleared_gaussian {m : ℕ}
    (T : Fin m → ℕ) (j s h : ℕ) (b a : Fin m → ℕ) :
    (∏ i, (MvPolynomial.C (logDenominator (T i) : ℂ))^(a i-b i)) *
      formalEntry (fun _ => 2*(j : ℂ)*Complex.I) (fun i => truncatedLog (T i)) s h b a ∈
        (MvPolynomial.map GaussianInt.toComplex :
          MvPolynomial (Fin m) GaussianInt →+* MvPolynomial (Fin m) ℂ).range := by
  let f := (MvPolynomial.map GaussianInt.toComplex :
    MvPolynomial (Fin m) GaussianInt →+* MvPolynomial (Fin m) ℂ)
  let S := (Polynomial.mapRingHom f).range
  have hP : ((1+Polynomial.X)^h : Polynomial (MvPolynomial (Fin m) ℂ)) ∈ S := by
    exact ⟨(1+Polynomial.X)^h, by simp⟩
  have hpoly := S.mul_mem hP (S.prod_mem (t := Finset.univ) (fun i _ => S.pow_mem
    (cleared_shifted_truncatedLog_gaussian (T i) j i) (a i-b i)))
  have hcoeff := (Polynomial.mem_map_range f).mp hpoly s
  have hchoose : MvPolynomial.C (∏ i, ((a i).choose (b i) : ℂ)) ∈ f.range := by
    exact ⟨MvPolynomial.C (∏ i, ((a i).choose (b i) : GaussianInt)), by simp⟩
  have hmul := f.range.mul_mem hchoose hcoeff
  rw [formalEntry_split]
  have he := scalar_product_mul_coeff (fun i => MvPolynomial.C (logDenominator (T i) : ℂ))
    (fun i => a i-b i) ((1+Polynomial.X)^h)
    (fun i => C (MvPolynomial.C (2*(j : ℂ)*Complex.I)*MvPolynomial.X i) +
      (truncatedLog (T i)).map MvPolynomial.C) s
  rw [← he] at hmul
  convert hmul using 1
  ring

/-- Exact whole determinant polynomial clearing for the actual log entries. -/
theorem formal_minor_truncatedLog_cleared_gaussian {ι : Type*}
    [Fintype ι] [DecidableEq ι] {m : ℕ} (T : Fin m → ℕ)
    (j s h : ι → ℕ) (b a : ι → Fin m → ℕ) :
    (∏ i, (MvPolynomial.C (logDenominator (T i) : ℂ))^((∑ k, a k i)-(∑ r, b r i))) *
      Matrix.det (fun r k => formalEntry (fun _ => 2*(j r : ℂ)*Complex.I)
        (fun i => truncatedLog (T i)) (s r) (h k) (b r) (a k)) ∈
        (MvPolynomial.map GaussianInt.toComplex :
          MvPolynomial (Fin m) GaussianInt →+* MvPolynomial (Fin m) ℂ).range := by
  apply determinant_clearing
  · intro r k hab
    exact formalEntry_zero_of_incompatible _ _ _ _ _ _ hab
  · intro r k
    exact formalEntry_truncatedLog_cleared_gaussian _ _ _ _ _ _

end FixedQuadratic
