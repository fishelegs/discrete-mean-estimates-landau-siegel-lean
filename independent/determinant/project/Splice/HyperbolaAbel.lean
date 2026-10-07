import Splice.CharacterArithmetic
import Splice.LFunctionIdentity
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# Finite hyperbola decomposition and explicit Abel estimates

The input here is an arithmetic function `f`, a bound for its finite partial
sums, and the *ordered* harmonic-tail estimate.  There is no prime-mass,
zero-free-region, positivity, or nonvanishing hypothesis.

The character specialization uses `f n = Re (χ n)` for positive `n`; convolution
with ζ is exactly `Re (DirichletCharacter.zetaMul χ n)`.
-/

noncomputable section

open Finset MeasureTheory
open scoped BigOperators

namespace Splice

/-- Positive-index summation with a real cutoff, including the upper endpoint. -/
def positiveSum (c : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ n ∈ Ioc 0 ⌊x⌋₊, c n

private theorem filtered_hyperbola_fiber (N b : ℕ) (hb : 0 < b) :
    {u ∈ Ioc 0 N | b * u ≤ N} = Ioc 0 (N / b) := by
  ext u
  simp only [mem_filter, mem_Ioc]
  constructor
  · rintro ⟨⟨hu, _⟩, hbu⟩
    exact ⟨hu, (Nat.le_div_iff_mul_le hb).mpr (by simpa [mul_comm] using hbu)⟩
  · rintro ⟨hu, hub⟩
    exact ⟨⟨hu, hub.trans (Nat.div_le_self N b)⟩,
      by simpa [mul_comm] using (Nat.le_div_iff_mul_le hb).mp hub⟩

private theorem sum_hyperbola_rows (f : ℕ → ℝ) (K N : ℕ) :
    (∑ p ∈ (Ioc 0 K ×ˢ Ioc 0 N).filter (fun p : ℕ × ℕ => p.1 * p.2 ≤ N),
      f p.1) = ∑ b ∈ Ioc 0 K, f b * (N / b : ℕ) := by
  rw [sum_filter, sum_product]
  refine sum_congr rfl fun b hb => ?_
  rw [← sum_filter, filtered_hyperbola_fiber N b (mem_Ioc.mp hb).1]
  simp [mul_comm]

private theorem sum_hyperbola_columns (f : ℕ → ℝ) (K N : ℕ) :
    (∑ p ∈ (Ioc 0 N ×ˢ Ioc 0 K).filter (fun p : ℕ × ℕ => p.1 * p.2 ≤ N),
      f p.1) = ∑ u ∈ Ioc 0 K, ∑ b ∈ Ioc 0 (N / u), f b := by
  rw [sum_filter, sum_product_right]
  refine sum_congr rfl fun u hu => ?_
  simp_rw [mul_comm (a := _) (b := u)]
  rw [← sum_filter, filtered_hyperbola_fiber N u (mem_Ioc.mp hu).1]

/-- Exact finite Dirichlet hyperbola identity, with separate integer cutoffs.
The two geometric hypotheses say that the intersection is a full rectangle
and that the two pieces cover the hyperbola. -/
theorem finite_hyperbola (f : ArithmeticFunction ℝ) (N y z : ℕ)
    (hy : y ≤ N) (hz : z ≤ N) (hrect : y * z ≤ N)
    (hcover : N < (y + 1) * (z + 1)) :
    (∑ n ∈ Ioc 0 N, (f * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) : ArithmeticFunction ℝ) n) =
      (∑ b ∈ Ioc 0 z, f b * (N / b : ℕ)) +
      (∑ u ∈ Ioc 0 y, ∑ b ∈ Ioc 0 (N / u), f b) -
      (y : ℝ) * ∑ b ∈ Ioc 0 z, f b := by
  let H := (Ioc 0 N ×ˢ Ioc 0 N).filter (fun p : ℕ × ℕ => p.1 * p.2 ≤ N)
  let A := (Ioc 0 z ×ˢ Ioc 0 N).filter (fun p : ℕ × ℕ => p.1 * p.2 ≤ N)
  let B := (Ioc 0 N ×ˢ Ioc 0 y).filter (fun p : ℕ × ℕ => p.1 * p.2 ≤ N)
  have hU : A ∪ B = H := by
    ext p
    simp only [A, B, H, mem_union, mem_filter, mem_product, mem_Ioc]
    constructor
    · rintro (⟨⟨⟨hb, hbz⟩, hu⟩, hp⟩ | ⟨⟨hb, ⟨hu, huy⟩⟩, hp⟩)
      · exact ⟨⟨⟨hb, hbz.trans hz⟩, hu⟩, hp⟩
      · exact ⟨⟨hb, ⟨hu, huy.trans hy⟩⟩, hp⟩
    · rintro ⟨⟨⟨hb, hbN⟩, ⟨hu, huN⟩⟩, hp⟩
      by_cases hbz : p.1 ≤ z
      · exact Or.inl ⟨⟨⟨hb, hbz⟩, ⟨hu, huN⟩⟩, hp⟩
      · have huy : p.2 ≤ y := by
          by_contra huy
          have hmul := Nat.mul_le_mul (show y + 1 ≤ p.2 by omega)
            (show z + 1 ≤ p.1 by omega)
          nlinarith
        exact Or.inr ⟨⟨⟨hb, hbN⟩, ⟨hu, huy⟩⟩, hp⟩
  have hI : A ∩ B = Ioc 0 z ×ˢ Ioc 0 y := by
    ext p
    simp only [A, B, mem_inter, mem_filter, mem_product, mem_Ioc]
    constructor
    · rintro ⟨⟨⟨hb, _⟩, _⟩, ⟨⟨_, hu⟩, _⟩⟩
      exact ⟨hb, hu⟩
    · rintro ⟨⟨hb, hbz⟩, ⟨hu, huy⟩⟩
      have hp : p.1 * p.2 ≤ N := by
        calc p.1 * p.2 ≤ z * y := Nat.mul_le_mul hbz huy
             _ = y * z := Nat.mul_comm _ _
             _ ≤ N := hrect
      exact ⟨⟨⟨⟨hb, hbz⟩, ⟨hu, huy.trans hy⟩⟩, hp⟩,
        ⟨⟨⟨hb, hbz.trans hz⟩, ⟨hu, huy⟩⟩, hp⟩⟩
  have hH : (∑ p ∈ H, f p.1) = ∑ n ∈ Ioc 0 N, (f * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) : ArithmeticFunction ℝ) n := by
    rw [ArithmeticFunction.sum_Ioc_mul_eq_sum_prod_filter]
    refine sum_congr rfl fun p hp => ?_
    have hp2 : p.2 ≠ 0 := (mem_Ioc.mp (mem_product.mp (mem_filter.mp hp).1).2).1.ne'
    simp [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, hp2]
  have hsum := Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := fun p => f p.1)
  rw [hU, hI, hH, sum_product_right] at hsum
  simp only [sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul] at hsum
  rw [sum_hyperbola_rows, sum_hyperbola_columns] at hsum
  linarith

/-- The usual choice `z = N / y` satisfies the hyperbola geometry exactly. -/
theorem finite_hyperbola_div (f : ArithmeticFunction ℝ) (N y : ℕ)
    (hy0 : 0 < y) (hyN : y ≤ N) :
    (∑ n ∈ Ioc 0 N, (f * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) : ArithmeticFunction ℝ) n) =
      (∑ b ∈ Ioc 0 (N / y), f b * (N / b : ℕ)) +
      (∑ u ∈ Ioc 0 y, ∑ b ∈ Ioc 0 (N / u), f b) -
      (y : ℝ) * ∑ b ∈ Ioc 0 (N / y), f b := by
  apply finite_hyperbola f N y (N / y) hyN (Nat.div_le_self _ _)
  · simpa [mul_comm] using Nat.div_mul_le_self N y
  · have hlt : N < (N / y + 1) * y := (Nat.div_lt_iff_lt_mul hy0).mp (Nat.lt_succ_self _)
    nlinarith

/-- Real-cutoff version, preserving the closed upper endpoints even when
`x / y` is an integer. -/
theorem real_hyperbola (f : ArithmeticFunction ℝ) {x : ℝ} {y : ℕ}
    (hy0 : 0 < y) (hyx : (y : ℝ) ≤ x) :
    positiveSum (f * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) : ArithmeticFunction ℝ) x =
      (∑ b ∈ Ioc 0 ⌊x / y⌋₊, f b * (⌊x / b⌋₊ : ℝ)) +
      (∑ u ∈ Ioc 0 y, positiveSum f (x / u)) -
      (y : ℝ) * positiveSum f (x / y) := by
  have hyN : y ≤ ⌊x⌋₊ := (Nat.le_floor_iff' hy0.ne').mpr hyx
  simpa only [positiveSum, Nat.floor_div_natCast] using finite_hyperbola_div f ⌊x⌋₊ y hy0 hyN

/-- Replacing the floor in a truncated divisor sum costs at most its length. -/
theorem hyperbola_floor_error (f : ArithmeticFunction ℝ) {x T : ℝ}
    (hx : 0 ≤ x) (hT : 0 ≤ T)
    (hf : ∀ n : ℕ, 0 < n → |f n| ≤ 1) :
    |(∑ b ∈ Ioc 0 ⌊T⌋₊, f b * (⌊x / b⌋₊ : ℝ)) -
      x * positiveSum (fun b => f b / b) T| ≤ T := by
  have heq : (∑ b ∈ Ioc 0 ⌊T⌋₊, f b * (⌊x / b⌋₊ : ℝ)) -
      x * positiveSum (fun b => f b / b) T =
      ∑ b ∈ Ioc 0 ⌊T⌋₊, f b * ((⌊x / b⌋₊ : ℝ) - x / b) := by
    simp only [positiveSum, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro b hb
    ring
  rw [heq]
  calc
    |∑ b ∈ Ioc 0 ⌊T⌋₊, f b * ((⌊x / b⌋₊ : ℝ) - x / b)| ≤
        ∑ b ∈ Ioc 0 ⌊T⌋₊, |f b * ((⌊x / b⌋₊ : ℝ) - x / b)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ b ∈ Ioc 0 ⌊T⌋₊, (1 : ℝ) := by
      apply sum_le_sum
      intro b hb
      rw [abs_mul]
      exact mul_le_one₀ (hf b (mem_Ioc.mp hb).1) (abs_nonneg _)
        (Nat.abs_floor_sub_le (div_nonneg hx (Nat.cast_nonneg b)))
    _ = (⌊T⌋₊ : ℝ) := by simp
    _ ≤ T := Nat.floor_le hT

/-- The unoptimized explicit hyperbola error, before choosing the square-root
cutoff.  The harmonic hypothesis is an ordered truncation estimate. -/
theorem summatory_error_at_cutoff (f : ArithmeticFunction ℝ) {D a x : ℝ} {y : ℕ}
    (hD : 0 ≤ D) (hy0 : 0 < y) (hyx : (y : ℝ) ≤ x)
    (hf : ∀ n : ℕ, 0 < n → |f n| ≤ 1)
    (hpartial : ∀ T : ℝ, 0 ≤ T → |positiveSum f T| ≤ D)
    (htail : ∀ T : ℝ, 0 < T → |positiveSum (fun n => f n / n) T - a| ≤ 2 * D / T) :
    |positiveSum (f * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) : ArithmeticFunction ℝ) x - a * x| ≤
      x / y + 4 * D * y := by
  have hyR : (0 : ℝ) < y := Nat.cast_pos.mpr hy0
  have hx : 0 < x := hyR.trans_le hyx
  let T : ℝ := x / y
  have hT : 0 < T := div_pos hx hyR
  let F : ℝ := ∑ b ∈ Ioc 0 ⌊T⌋₊, f b * (⌊x / b⌋₊ : ℝ)
  let H : ℝ := positiveSum (fun n => f n / n) T
  let B : ℝ := ∑ u ∈ Ioc 0 y, positiveSum f (x / u)
  have hF : |F - x * H| ≤ T := hyperbola_floor_error f hx.le hT.le hf
  have hH : |x * (H - a)| ≤ 2 * D * y := by
    rw [abs_mul, abs_of_pos hx]
    calc
      x * |H - a| ≤ x * (2 * D / T) := mul_le_mul_of_nonneg_left (htail T hT) hx.le
      _ = 2 * D * y := by dsimp [T]; field_simp [hyR.ne', hx.ne']
  have hB : |B| ≤ D * y := by
    calc
      |B| ≤ ∑ u ∈ Ioc 0 y, |positiveSum f (x / u)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ u ∈ Ioc 0 y, D := by
        apply sum_le_sum
        intro u hu
        exact hpartial _ (div_nonneg hx.le (Nat.cast_nonneg u))
      _ = D * y := by simp [mul_comm]
  have hR : |(y : ℝ) * positiveSum f T| ≤ D * y := by
    rw [abs_mul, abs_of_pos hyR]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left (hpartial T hT.le) hyR.le
  have hid : positiveSum (f * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) : ArithmeticFunction ℝ) x - a * x =
      (F - x * H) + x * (H - a) + B - (y : ℝ) * positiveSum f T := by
    rw [real_hyperbola f hy0 hyx]
    dsimp [F, H, B, T]
    ring
  rw [hid]
  calc
    |(F - x * H) + x * (H - a) + B - (y : ℝ) * positiveSum f T| ≤
        |F - x * H| + |x * (H - a)| + |B| + |(y : ℝ) * positiveSum f T| := by
      have h₁ := abs_add_le (F - x * H) (x * (H - a))
      have h₂ := abs_add_le ((F - x * H) + x * (H - a)) B
      have h₃ := abs_sub ((F - x * H) + x * (H - a) + B)
        ((y : ℝ) * positiveSum f T)
      linarith only [h₁, h₂, h₃]
    _ ≤ T + 2 * D * y + D * y + D * y := by linarith
    _ = x / y + 4 * D * y := by dsimp [T]; ring

/-- A simple floor estimate retaining the endpoint `r = 1`. -/
theorem half_le_nat_floor {r : ℝ} (hr : 1 ≤ r) : r / 2 ≤ (⌊r⌋₊ : ℝ) := by
  have hfloor : 1 ≤ ⌊r⌋₊ := (Nat.one_le_floor_iff r).mpr hr
  have hfloorR : (1 : ℝ) ≤ ⌊r⌋₊ := Nat.one_le_cast.mpr hfloor
  have hlt := Nat.lt_floor_add_one r
  linarith

/-- Explicit `6 √(Dx)` summatory error from bounded partial sums and the
ordered harmonic-tail bound. -/
theorem summatory_error_six_sqrt (f : ArithmeticFunction ℝ) {D a x : ℝ}
    (hD : 1 ≤ D) (hx : D ≤ x)
    (hf : ∀ n : ℕ, 0 < n → |f n| ≤ 1)
    (hpartial : ∀ T : ℝ, 0 ≤ T → |positiveSum f T| ≤ D)
    (htail : ∀ T : ℝ, 0 < T → |positiveSum (fun n => f n / n) T - a| ≤ 2 * D / T) :
    |positiveSum (f * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) : ArithmeticFunction ℝ) x - a * x| ≤ 6 * Real.sqrt (D * x) := by
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hx0 : 0 < x := hD0.trans_le hx
  let r : ℝ := Real.sqrt (x / D)
  let y : ℕ := ⌊r⌋₊
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrsq : r ^ 2 = x / D := Real.sq_sqrt (div_nonneg hx0.le hD0.le)
  have hr1 : 1 ≤ r := by
    exact Real.one_le_sqrt.mpr ((le_div_iff₀ hD0).mpr (by simpa using hx))
  have hy0 : 0 < y := Nat.floor_pos.mpr hr1
  have hyr : (y : ℝ) ≤ r := Nat.floor_le hr0
  have hry : r / 2 ≤ (y : ℝ) := half_le_nat_floor hr1
  have hrx : r ≤ x := by
    have hquot : x / D ≤ x := div_le_self hx0.le hD
    nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hr1)]
  have hyx : (y : ℝ) ≤ x := hyr.trans hrx
  have hbase := summatory_error_at_cutoff f hD0.le hy0 hyx hf hpartial htail
  have hroot : D * r = Real.sqrt (D * x) := by
    symm
    apply (Real.sqrt_eq_iff_eq_sq (mul_nonneg hD0.le hx0.le)
      (mul_nonneg hD0.le hr0)).mpr
    have hmul : r ^ 2 * D = x := (eq_div_iff hD0.ne').mp hrsq
    rw [← hmul]
    ring
  have hDy : D * (y : ℝ) ≤ Real.sqrt (D * x) := by
    rw [← hroot]
    exact mul_le_mul_of_nonneg_left hyr hD0.le
  have hxy : x / (y : ℝ) ≤ 2 * Real.sqrt (D * x) := by
    rw [div_le_iff₀ (Nat.cast_pos.mpr hy0), ← hroot]
    have hmul : r ^ 2 * D = x := (eq_div_iff hD0.ne').mp hrsq
    have := mul_le_mul_of_nonneg_left hry (mul_nonneg hD0.le hr0)
    nlinarith
  linarith

private theorem positiveSum_eq_sum_Icc (c : ℕ → ℝ) (hc : c 0 = 0) (x : ℝ) :
    positiveSum c x = ∑ n ∈ Icc 0 ⌊x⌋₊, c n := by
  rw [Icc_eq_cons_Ioc (Nat.zero_le _), sum_cons, hc, zero_add]
  rfl

private theorem continuousOn_inv_sq {T X : ℝ} (hT : 0 < T) :
    ContinuousOn (fun u : ℝ => (u ^ 2)⁻¹) (Set.Icc T X) := by
  exact (continuousOn_id.pow 2).inv₀ fun u hu => pow_ne_zero _ (ne_of_gt (hT.trans_le hu.1))

/-- Exact partial summation for the harmonic weight. -/
theorem harmonic_abel_identity (c : ℕ → ℝ) (hc : c 0 = 0)
    {T X : ℝ} (hT : 0 < T) (hTX : T ≤ X) :
    (∑ n ∈ Ioc ⌊T⌋₊ ⌊X⌋₊, c n / n) =
      positiveSum c X / X - positiveSum c T / T +
      ∫ u in T..X, positiveSum c u / u ^ 2 := by
  have hd : ∀ u ∈ Set.Icc T X, DifferentiableAt ℝ (fun v : ℝ => v⁻¹) u := by
    intro u hu
    exact (hasDerivAt_inv (ne_of_gt (hT.trans_le hu.1))).differentiableAt
  have hi : IntegrableOn (deriv (fun u : ℝ => u⁻¹)) (Set.Icc T X) := by
    have hcont : ContinuousOn (fun u : ℝ => -(u ^ 2)⁻¹) (Set.Icc T X) := by
      intro u hu
      exact ((continuousOn_inv_sq hT) u hu).neg
    rw [deriv_inv']
    exact hcont.integrableOn_Icc
  have hab := sum_mul_eq_sub_sub_integral_mul c hT.le hTX hd hi
  simp_rw [← positiveSum_eq_sum_Icc c hc, deriv_inv] at hab
  rw [← intervalIntegral.integral_of_le hTX] at hab
  have heq : (fun u : ℝ => -(u ^ 2)⁻¹ * positiveSum c u) =
      (fun u : ℝ => -(positiveSum c u / u ^ 2)) := by funext u; ring
  rw [heq, intervalIntegral.integral_neg] at hab
  simpa only [div_eq_mul_inv, mul_comm, sub_neg_eq_add] using hab

/-- Abel summation after separating the linear main term. -/
theorem harmonic_abel_error_identity (c : ℕ → ℝ) (hc : c 0 = 0)
    {a T X : ℝ} (hT : 0 < T) (hTX : T ≤ X) :
    (∑ n ∈ Ioc ⌊T⌋₊ ⌊X⌋₊, c n / n) =
      a * Real.log (X / T) +
      (positiveSum c X - a * X) / X - (positiveSum c T - a * T) / T +
      ∫ u in T..X, (positiveSum c u - a * u) / u ^ 2 := by
  have hX : 0 < X := hT.trans_le hTX
  have hsumInt : IntervalIntegrable (fun u => positiveSum c u / u ^ 2) volume T X := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hTX]
    simpa only [positiveSum_eq_sum_Icc c hc, div_eq_mul_inv, mul_comm] using
      integrableOn_mul_sum_Icc c hT.le (continuousOn_inv_sq hT).integrableOn_Icc
  have hinv : IntervalIntegrable (fun u : ℝ => 1 / u) volume T X := by
    apply ContinuousOn.intervalIntegrable_of_Icc hTX
    exact continuousOn_const.div continuousOn_id fun u hu => ne_of_gt (hT.trans_le hu.1)
  have hI : (∫ u in T..X, (positiveSum c u - a * u) / u ^ 2) =
      (∫ u in T..X, positiveSum c u / u ^ 2) - a * Real.log (X / T) := by
    calc
      (∫ u in T..X, (positiveSum c u - a * u) / u ^ 2) =
          ∫ u in T..X, positiveSum c u / u ^ 2 - a * (1 / u) := by
        apply intervalIntegral.integral_congr
        intro u hu
        have hu0 : u ≠ 0 := ne_of_gt (hT.trans_le ((Set.uIcc_of_le hTX ▸ hu).1))
        field_simp [hu0]
        <;> ring
      _ = (∫ u in T..X, positiveSum c u / u ^ 2) -
          ∫ u in T..X, a * (1 / u) :=
        intervalIntegral.integral_sub hsumInt (hinv.const_mul a)
      _ = (∫ u in T..X, positiveSum c u / u ^ 2) - a * Real.log (X / T) := by
        rw [intervalIntegral.integral_const_mul, integral_one_div_of_pos hT hX]
  rw [harmonic_abel_identity c hc hT hTX, hI]
  field_simp [hT.ne', hX.ne']
  <;> ring

private theorem sqrt_product_div {D u : ℝ} (hD : 0 ≤ D) (hu : 0 < u) :
    Real.sqrt (D * u) / u = Real.sqrt D / Real.sqrt u := by
  rw [Real.sqrt_mul hD]
  rw [mul_div_assoc, Real.sqrt_div_self']
  ring

private theorem sqrt_error_majorant_integrable {D T X : ℝ} (hT : 0 < T) (hTX : T ≤ X) :
    IntervalIntegrable (fun u => 6 * Real.sqrt D / (u * Real.sqrt u)) volume T X := by
  apply ContinuousOn.intervalIntegrable_of_Icc hTX
  exact continuousOn_const.div (continuousOn_id.mul Real.continuous_sqrt.continuousOn)
    fun u hu => mul_ne_zero (ne_of_gt (hT.trans_le hu.1))
      (ne_of_gt (Real.sqrt_pos.mpr (hT.trans_le hu.1)))

/-- Exact integral of the square-root error majorant. -/
theorem integral_sqrt_error_majorant {D T X : ℝ} (hT : 0 < T) (hTX : T ≤ X) :
    (∫ u in T..X, 6 * Real.sqrt D / (u * Real.sqrt u)) =
      12 * Real.sqrt D / Real.sqrt T - 12 * Real.sqrt D / Real.sqrt X := by
  have hd : ∀ u ∈ Set.uIcc T X,
      HasDerivAt (fun v => -(12 * Real.sqrt D) / Real.sqrt v)
        (6 * Real.sqrt D / (u * Real.sqrt u)) u := by
    intro u hu
    have hu0 : 0 < u := hT.trans_le ((Set.uIcc_of_le hTX ▸ hu).1)
    have hs0 : Real.sqrt u ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hu0)
    convert (hasDerivAt_const u (-(12 * Real.sqrt D))).div
      (Real.hasDerivAt_sqrt hu0.ne') hs0 using 1
    have hsq := Real.sq_sqrt hu0.le
    have hsqD : 12 * Real.sqrt D * (Real.sqrt u) ^ 2 = 12 * Real.sqrt D * u := by rw [hsq]
    field_simp [hs0, hu0.ne']
    nlinarith [hsqD]
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (sqrt_error_majorant_integrable hT hTX (D := D))
  convert heq using 1 <;> ring

/-- An explicit weighted tail bound from the pointwise summatory error.
The stronger negative upper-endpoint correction is retained internally. -/
theorem harmonic_tail_eighteen_sqrt (c : ℕ → ℝ) (hc : c 0 = 0)
    {D a T X : ℝ} (hD : 0 ≤ D) (hT : 0 < T) (hTX : T ≤ X)
    (herror : ∀ u ∈ Set.Icc T X,
      |positiveSum c u - a * u| ≤ 6 * Real.sqrt (D * u)) :
    (∑ n ∈ Ioc ⌊T⌋₊ ⌊X⌋₊, c n / n) ≤
      a * Real.log (X / T) + 18 * Real.sqrt (D / T) := by
  let E : ℝ → ℝ := fun u => positiveSum c u - a * u
  have hX : 0 < X := hT.trans_le hTX
  have hend : ∀ u ∈ Set.Icc T X, |E u / u| ≤ 6 * Real.sqrt D / Real.sqrt u := by
    intro u hu
    have hu0 : 0 < u := hT.trans_le hu.1
    rw [abs_div, abs_of_pos hu0]
    calc
      |E u| / u ≤ (6 * Real.sqrt (D * u)) / u :=
        div_le_div_of_nonneg_right (herror u hu) hu0.le
      _ = 6 * Real.sqrt D / Real.sqrt u := by rw [mul_div_assoc, sqrt_product_div hD hu0]; ring
  have hInt : |∫ u in T..X, E u / u ^ 2| ≤
      12 * Real.sqrt D / Real.sqrt T - 12 * Real.sqrt D / Real.sqrt X := by
    rw [← integral_sqrt_error_majorant hT hTX]
    rw [← Real.norm_eq_abs]
    apply intervalIntegral.norm_integral_le_of_norm_le hTX
      (Filter.Eventually.of_forall _) (sqrt_error_majorant_integrable hT hTX)
    intro u hu
    have hu0 : 0 < u := hT.trans hu.1
    have hs0 : Real.sqrt u ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hu0)
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg u)]
    calc
      |E u| / u ^ 2 ≤ 6 * Real.sqrt (D * u) / u ^ 2 :=
        div_le_div_of_nonneg_right (herror u ⟨hu.1.le, hu.2⟩) (sq_nonneg u)
      _ = 6 * Real.sqrt D / (u * Real.sqrt u) := by
        rw [Real.sqrt_mul hD]
        have hsq := Real.sq_sqrt hu0.le
        have hsqD : 6 * Real.sqrt D * (Real.sqrt u) ^ 2 = 6 * Real.sqrt D * u := by rw [hsq]
        field_simp [hs0, hu0.ne']
        nlinarith [hsqD]
  have hXT := hend X ⟨hTX, le_rfl⟩
  have hTT := hend T ⟨le_rfl, hTX⟩
  have hdrop : 0 ≤ 6 * Real.sqrt D / Real.sqrt X := by positivity
  have hsqrt : Real.sqrt (D / T) = Real.sqrt D / Real.sqrt T := Real.sqrt_div hD T
  rw [harmonic_abel_error_identity c hc hT hTX]
  change a * Real.log (X / T) + E X / X - E T / T +
    (∫ u in T..X, E u / u ^ 2) ≤ _
  rw [hsqrt]
  have h1 := le_abs_self (E X / X)
  have h2 := neg_le_abs (E T / T)
  have h3 := le_abs_self (∫ u in T..X, E u / u ^ 2)
  simp only [mul_div_assoc] at hInt hXT hTT hdrop
  linarith only [hInt, hXT, hTT, hdrop, h1, h2, h3]

/-- The two elementary steps composed, with the only analytic input being
an explicit ordered harmonic-tail estimate for `f`. -/
theorem convolution_harmonic_tail (f : ArithmeticFunction ℝ) {D a T X : ℝ}
    (hD : 1 ≤ D) (hDT : D ≤ T) (hTX : T ≤ X)
    (hf : ∀ n : ℕ, 0 < n → |f n| ≤ 1)
    (hpartial : ∀ u : ℝ, 0 ≤ u → |positiveSum f u| ≤ D)
    (htail : ∀ u : ℝ, 0 < u → |positiveSum (fun n => f n / n) u - a| ≤ 2 * D / u) :
    (∑ n ∈ Ioc ⌊T⌋₊ ⌊X⌋₊, (f * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) : ArithmeticFunction ℝ) n / n) ≤
      a * Real.log (X / T) + 18 * Real.sqrt (D / T) := by
  apply harmonic_tail_eighteen_sqrt (f * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) : ArithmeticFunction ℝ)
    (by simp) (le_trans zero_le_one hD)
    (lt_of_lt_of_le zero_lt_one (hD.trans hDT)) hTX
  intro u hu
  exact summatory_error_six_sqrt f hD (hDT.trans hu.1) hf hpartial htail

/-- The real part of a character as a real arithmetic function. The value at
zero is discarded by `toArithmeticFunction`; all positive coefficients agree. -/
def realCharacterArithmetic {D : ℕ} (χ : DirichletCharacter ℂ D) : ArithmeticFunction ℝ :=
  toArithmeticFunction (fun n => (χ n).re)

@[simp] theorem realCharacterArithmetic_apply_pos {D : ℕ} (χ : DirichletCharacter ℂ D)
    {n : ℕ} (hn : 0 < n) : realCharacterArithmetic χ n = (χ n).re := by
  simp [realCharacterArithmetic, toArithmeticFunction, hn.ne']

/-- The generic convolution is the actual `zetaMul` real part. -/
theorem realCharacterArithmetic_mul_zeta {D : ℕ} (χ : DirichletCharacter ℂ D) (n : ℕ) :
    (realCharacterArithmetic χ * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) : ArithmeticFunction ℝ) n = nu χ n := by
  rw [ArithmeticFunction.coe_mul_zeta_apply, nu_eq_sum_divisors]
  apply sum_congr rfl
  intro d hd
  exact realCharacterArithmetic_apply_pos χ (Nat.pos_of_mem_divisors hd)

private theorem character_positiveSum {D : ℕ} (χ : DirichletCharacter ℂ D) (T : ℝ) :
    positiveSum (realCharacterArithmetic χ) T = ∑ n ∈ Icc 1 ⌊T⌋₊, (χ n).re := by
  have hI : Ioc 0 ⌊T⌋₊ = Icc 1 ⌊T⌋₊ := by ext n; simp only [mem_Ioc, mem_Icc]; omega
  unfold positiveSum
  rw [hI]
  exact sum_congr rfl fun n hn => realCharacterArithmetic_apply_pos χ (mem_Icc.mp hn).1

private theorem character_harmonic_positiveSum {D : ℕ} (χ : DirichletCharacter ℂ D) (T : ℝ) :
    positiveSum (fun n => realCharacterArithmetic χ n / n) T =
      ∑ n ∈ Icc 1 ⌊T⌋₊, (χ n).re / (n : ℝ) := by
  have hI : Ioc 0 ⌊T⌋₊ = Icc 1 ⌊T⌋₊ := by ext n; simp only [mem_Ioc, mem_Icc]; omega
  unfold positiveSum
  rw [hI]
  apply sum_congr rfl
  intro n hn
  dsimp only
  rw [realCharacterArithmetic_apply_pos χ (mem_Icc.mp hn).1]

/-- Section 2 for the actual character convolution and actual L-function. -/
theorem nu_summatory_error_six_sqrt {D : ℕ} [NeZero D]
    (χ : DirichletCharacter ℂ D) (hne : χ ≠ 1) {x : ℝ} (hx : (D : ℝ) ≤ x) :
    |positiveSum (nu χ) x - LOne χ * x| ≤ 6 * Real.sqrt ((D : ℝ) * x) := by
  have hD : (1 : ℝ) ≤ D := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne D)
  have h := summatory_error_six_sqrt (realCharacterArithmetic χ) (a := LOne χ) hD hx
  have hf : ∀ n : ℕ, 0 < n → |realCharacterArithmetic χ n| ≤ 1 := by
    intro n hn
    rw [realCharacterArithmetic_apply_pos χ hn]
    exact (Complex.abs_re_le_norm _).trans (χ.norm_le_one _)
  have hp : ∀ T : ℝ, 0 ≤ T → |positiveSum (realCharacterArithmetic χ) T| ≤ (D : ℝ) := by
    intro T hT
    rw [character_positiveSum]
    exact character_sum_Icc_abs_le χ hne _
  have ht : ∀ T : ℝ, 0 < T →
      |positiveSum (fun n => realCharacterArithmetic χ n / n) T - LOne χ| ≤ 2 * (D : ℝ) / T := by
    intro T hT
    rw [character_harmonic_positiveSum]
    exact abs_characterHarmonicSum_re_sub_LFunction_one_le χ hne
      (character_sum_Icc_norm_le χ hne) hT
  simpa only [positiveSum, realCharacterArithmetic_mul_zeta] using h hf hp ht

/-- Section 3 for the actual character convolution and actual L-function. -/
theorem nu_harmonic_tail_eighteen_sqrt {D : ℕ} [NeZero D]
    (χ : DirichletCharacter ℂ D) (hne : χ ≠ 1) {T X : ℝ}
    (hDT : (D : ℝ) ≤ T) (hTX : T ≤ X) :
    (∑ n ∈ Ioc ⌊T⌋₊ ⌊X⌋₊, nu χ n / (n : ℝ)) ≤
      LOne χ * Real.log (X / T) + 18 * Real.sqrt ((D : ℝ) / T) := by
  have hD : (0 : ℝ) < D := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne D))
  apply harmonic_tail_eighteen_sqrt (nu χ) (by simp [nu]) hD.le
    (hD.trans_le hDT) hTX
  intro u hu
  exact nu_summatory_error_six_sqrt χ hne (hDT.trans hu.1)

end Splice

#print axioms Splice.finite_hyperbola
#print axioms Splice.summatory_error_six_sqrt
#print axioms Splice.harmonic_tail_eighteen_sqrt
#print axioms Splice.nu_summatory_error_six_sqrt
#print axioms Splice.nu_harmonic_tail_eighteen_sqrt
