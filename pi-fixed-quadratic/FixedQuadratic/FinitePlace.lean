import Mathlib.RingTheory.Polynomial.GaussNorm
import Mathlib.Data.Int.GCD
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic

open Polynomial
namespace FixedQuadratic

theorem primitive_quadratic_bezout (a b c : ℤ)
    (h : Int.gcd (Int.gcd a b : ℤ) c = 1) :
    ∃ u v w : ℤ, u*a + v*b + w*c = 1 := by
  have hab := Int.gcd_eq_gcd_ab a b
  have hc := Int.gcd_eq_gcd_ab (Int.gcd a b : ℤ) c
  rw [h] at hc
  refine ⟨Int.gcdA a b * Int.gcdA (Int.gcd a b : ℤ) c,
    Int.gcdB a b * Int.gcdA (Int.gcd a b : ℤ) c,
    Int.gcdB (Int.gcd a b : ℤ) c, ?_⟩
  calc
    _ = (Int.gcd a b : ℤ) * Int.gcdA (Int.gcd a b : ℤ) c +
        c * Int.gcdB (Int.gcd a b : ℤ) c := by rw [hab]; ring
    _ = 1 := by simpa using hc.symm

theorem primitive_quadratic_max_one {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    (a b c : ℤ) (h : Int.gcd (Int.gcd a b : ℤ) c = 1) :
    max (v (a : K)) (max (v (b : K)) (v (c : K))) = 1 := by
  have hi : ∀ n : ℤ, v (n : K) ≤ 1 := fun _ =>
    hv.apply_intCast_le_one (by simp) (by simp) v.map_neg
  apply le_antisymm (max_le (hi a) (max_le (hi b) (hi c)))
  obtain ⟨u, t, w, hb⟩ := primitive_quadratic_bezout a b c h
  have hk : (u : K)*(a : K) + (t : K)*(b : K) + (w : K)*(c : K) = 1 := by
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_one] using
      congrArg (fun n : ℤ => (n : K)) hb
  have h1 := hv ((u : K)*(a : K) + (t : K)*(b : K)) ((w : K)*(c : K))
  have h2 := hv ((u : K)*(a : K)) ((t : K)*(b : K))
  rw [hk, map_one] at h1
  have hu : v ((u : K)*(a : K)) ≤ v (a : K) := by
    rw [map_mul]; simpa using mul_le_mul_of_nonneg_right (hi u) (v.nonneg _)
  have ht : v ((t : K)*(b : K)) ≤ v (b : K) := by
    rw [map_mul]; simpa using mul_le_mul_of_nonneg_right (hi t) (v.nonneg _)
  have hw : v ((w : K)*(c : K)) ≤ v (c : K) := by
    rw [map_mul]; simpa using mul_le_mul_of_nonneg_right (hi w) (v.nonneg _)
  exact h1.trans (max_le
    (h2.trans (max_le (hu.trans (le_max_left _ _))
      (ht.trans ((le_max_left _ _).trans (le_max_right _ _)))))
    (hw.trans ((le_max_right _ _).trans (le_max_right _ _))))

theorem gaussNorm_linear {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ) (x : K) :
    (X - C x).gaussNorm v 1 = max 1 (v x) := by
  apply le_antisymm
  · obtain ⟨n, hn⟩ := (X - C x).exists_eq_gaussNorm v 1
    rw [hn]
    rcases n with _ | n
    · simp
    · rcases n with _ | n <;> simp [coeff_sub, coeff_X]
  · apply max_le
    · have hl := (X - C x : K[X]).le_gaussNorm v (c := 1) (by norm_num : (0 : ℝ) ≤ 1) 1
      simpa [coeff_sub] using hl
    · have hl := (X - C x : K[X]).le_gaussNorm v (c := 1) (by norm_num : (0 : ℝ) ≤ 1) 0
      simpa [coeff_sub] using hl

theorem gaussNorm_quadratic {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ) (a b c : K) :
    (C a * X^2 + C b * X + C c).gaussNorm v 1 =
      max (v a) (max (v b) (v c)) := by
  apply le_antisymm
  · obtain ⟨n, hn⟩ := (C a * X^2 + C b * X + C c).exists_eq_gaussNorm v 1
    rw [hn]
    rcases n with _ | n
    · simp
    · rcases n with _ | n
      · simp
      · rcases n with _ | n <;> simp
  · apply max_le
    · have hl := (C a * X^2 + C b * X + C c : K[X]).le_gaussNorm v (c := 1) (by norm_num : (0 : ℝ) ≤ 1) 2
      simpa using hl
    · apply max_le
      · have hl := (C a * X^2 + C b * X + C c : K[X]).le_gaussNorm v (c := 1) (by norm_num : (0 : ℝ) ≤ 1) 1
        simpa using hl
      · have hl := (C a * X^2 + C b * X + C c : K[X]).le_gaussNorm v (c := 1) (by norm_num : (0 : ℝ) ≤ 1) 0
        simpa using hl

/-- The local root identity includes every nonarchimedean absolute value,
including those above 2. Primitivity is an explicit gcd condition. -/
theorem primitive_quadratic_root_identity {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    (a b c : ℤ) (h : Int.gcd (Int.gcd a b : ℤ) c = 1) (x y : K)
    (hf : C (a : K)*X^2 + C (b : K)*X + C (c : K) =
      C (a : K)*((X - C x)*(X - C y))) :
    v (a : K) * max 1 (v x) * max 1 (v y) = 1 := by
  have he := congrArg (fun p : K[X] => p.gaussNorm v 1) hf
  rw [gaussNorm_quadratic, primitive_quadratic_max_one v hv a b c h,
    gaussNorm_mul hv (by norm_num), gaussNorm_C,
    gaussNorm_mul hv (by norm_num), gaussNorm_linear, gaussNorm_linear] at he
  simpa [mul_assoc] using he.symm

theorem gaussian_nonarch_le_one {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    (g : GaussianInt →+* K) (z : GaussianInt) : v (g z) ≤ 1 := by
  have hi : ∀ n : ℤ, v (n : K) ≤ 1 := fun _ =>
    hv.apply_intCast_le_one (by simp) (by simp) v.map_neg
  have hs : v (g (Zsqrtd.sqrtd (d := -1)))^2 = 1 := by
    rw [pow_two, ← map_mul, ← map_mul, Zsqrtd.dmuld]
    simp
  have hI : v (g (Zsqrtd.sqrtd (d := -1))) = 1 := by
    nlinarith [v.nonneg (g (Zsqrtd.sqrtd (d := -1)))]
  obtain ⟨r, t⟩ := z
  rw [Zsqrtd.decompose, map_add, map_mul, map_intCast, map_intCast]
  apply (hv _ _).trans
  rw [map_mul, hI, one_mul]
  exact max_le (hi r) (hi t)

/-- Ultrametric evaluation has no coefficient-count cost. -/
theorem multi_eval_nonarch_le {K : Type*} [Field K] {m : ℕ}
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    (g : GaussianInt →+* K) (P : MvPolynomial (Fin m) GaussianInt)
    (x : Fin m → K) (e : Fin m → ℕ) (he : ∀ i, P.degreeOf i ≤ e i) :
    v (MvPolynomial.eval₂ g x P) ≤ ∏ i, (max 1 (v (x i)))^(e i) := by
  classical
  rw [MvPolynomial.eval₂_eq']
  by_cases hs : P.support.Nonempty
  · obtain ⟨α, hα, hsum⟩ := hv.finset_image_add_of_nonempty
      (fun α => g (P.coeff α) * ∏ i, x i ^ α i) hs
    apply hsum.trans
    rw [map_mul, map_prod]
    apply (mul_le_mul_of_nonneg_right (gaussian_nonarch_le_one v hv g _) ?_).trans
    · rw [one_mul]
      apply Finset.prod_le_prod₀
      · intro i _; positivity
      · intro i _
        rw [map_pow]
        calc
          v (x i) ^ α i ≤ (max 1 (v (x i)))^α i :=
            pow_le_pow_left₀ (v.nonneg _) (le_max_right _ _) _
          _ ≤ (max 1 (v (x i)))^e i := pow_le_pow_right₀ (le_max_left _ _)
            (MvPolynomial.degreeOf_le_iff.mp (he i) α hα)
    · positivity
  · simp only [Finset.not_nonempty_iff_eq_empty] at hs
    simp [hs]; positivity

/-- Exact local two-embedding norm bound with exponent e_i, for any number
of dependent coordinates. Gaussian integrality is not a hypothesis. -/
theorem cleared_product_nonarch_le_one {K : Type*} [Field K] {m : ℕ}
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    (g : GaussianInt →+* K) (P : MvPolynomial (Fin m) GaussianInt)
    (a b c : Fin m → ℤ) (x y : Fin m → K) (e : Fin m → ℕ)
    (he : ∀ i, P.degreeOf i ≤ e i)
    (hprim : ∀ i, Int.gcd (Int.gcd (a i) (b i) : ℤ) (c i) = 1)
    (hf : ∀ i, C (a i : K)*X^2 + C (b i : K)*X + C (c i : K) =
      C (a i : K)*((X - C (x i))*(X - C (y i)))) :
    v ((∏ i, (a i : K)^e i) * MvPolynomial.eval₂ g x P *
      MvPolynomial.eval₂ g y P) ≤ 1 := by
  have hx := multi_eval_nonarch_le v hv g P x e he
  have hy := multi_eval_nonarch_le v hv g P y e he
  rw [map_mul, map_mul, map_prod]
  calc
    _ ≤ (∏ i, v ((a i : K)^e i)) *
        (∏ i, (max 1 (v (x i)))^e i) * (∏ i, (max 1 (v (y i)))^e i) := by
      gcongr
    _ = ∏ i, (v (a i : K) * max 1 (v (x i)) * max 1 (v (y i)))^e i := by
      simp only [map_pow, Finset.prod_mul_distrib, mul_pow]
    _ = 1 := by
      have hl : ∀ i, v (a i : K) * max 1 (v (x i)) * max 1 (v (y i)) = 1 :=
        fun i => primitive_quadratic_root_identity v hv (a i) (b i) (c i)
          (hprim i) (x i) (y i) (hf i)
      simp only [hl, one_pow, Finset.prod_const_one]

end FixedQuadratic
