import ZhangLS.Spec.BSourceRegressions
import ZhangLS.Spec.RoughCollisionSmoothSplit

/-! Exact finite support bridges for the genuine Lemma 15.1 coefficients. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical

/-- The actual product cutoff is bounded by P for every modulus. -/
theorem actual151_b_product_cutoff_le_P (D : ℕ) :
    bProductCutoff D ≤ lemma23PaperP D := by
  rw [b_product_cutoff_exact]
  apply max_le
  · simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (b_paperP_one_le D)
        (by norm_num : (0.998 : ℝ) ≤ 1)
  · have ht : lemma56PaperT D^(-10 : ℤ) ≤ 1 := by
      rw [zpow_neg,zpow_ofNat]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (b_paperT_one_le D))
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left ht (le_trans zero_le_one (b_paperP_one_le D))

theorem actual151_b_first_cutoff_le_P (D : ℕ) :
    bFirstCutoff D ≤ lemma23PaperP D := by
  have hh : (lemma23PaperP D)^(1/2 : ℝ) ≤ lemma23PaperP D := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (b_paperP_one_le D)
        (by norm_num : (1/2 : ℝ) ≤ 1)
  exact max_le hh ((b_P2_le_half_power D).trans hh)

theorem actual151_b_second_cutoff_le_P (D : ℕ) :
    bSecondCutoff D ≤ lemma23PaperP D := by
  apply max_le
  · exact (by
      simpa only [lemma151P3,Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le (b_paperP_one_le D)
          (by norm_num : (0.498 : ℝ) ≤ 1))
  · exact (b_P2_le_half_power D).trans (by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le (b_paperP_one_le D)
          (by norm_num : (1/2 : ℝ) ≤ 1))

/-- Divisor-pair coordinates retain the exact positive n1 range. -/
theorem actual151_divisor_coordinates {n₁ : ℕ} {dd : ℕ×ℕ}
    (hdd : dd ∈ n₁.divisorsAntidiagonal) :
    0<dd.1 ∧ 0<dd.2 ∧ dd.1≤n₁ ∧ dd.2≤n₁ := by
  have he := (Nat.mem_divisorsAntidiagonal.mp hdd).1
  have hn := Nat.pos_of_ne_zero (Nat.mem_divisorsAntidiagonal.mp hdd).2
  have hp : 0<dd.1*dd.2 := he.symm ▸ hn
  have h1 := Nat.pos_of_mul_pos_right hp
  have h2 := Nat.pos_of_mul_pos_left hp
  refine ⟨h1,h2,?_,?_⟩
  · rw [←he]
    exact Nat.le_mul_of_pos_right _ h2
  · rw [←he]
    exact Nat.le_mul_of_pos_left _ h1

/-- Positive strict support converts genuine infinite notation to the exact
floor rectangle endpoint, with any predicate and arithmetic weight. -/
theorem actual151_weight_tsum_finite {X P : ℝ} {w : ℕ→ℂ}
    (hw : BStrictSupport X w) (n₁ : ℕ) (hn₁ : 0<n₁) (hXP : X≤P)
    (f : ℕ→ℂ) (q : ℕ→Prop) [DecidablePred q] :
    (∑' n : ℕ,if q n then w (n₁*n)*f n/n else 0)=
      ∑ n∈(Icc 1 ⌊P⌋₊).filter q,w (n₁*n)*f n/n := by
  have he : (∑' n : ℕ,if q n then w (n₁*n)*f n/n else 0)=
      ∑ n∈(Icc 1 ⌊P⌋₊).filter q,
        if q n then w (n₁*n)*f n/n else 0 := by
    apply tsum_eq_sum
    intro n hn
    by_cases hq : q n
    · rw [if_pos hq]
      by_cases hn0 : n=0
      · simp [hn0]
      have hz : w (n₁*n)=0 := by
        by_contra hne
        have hs := hw (n₁*n) hne
        have hmul : (n : ℝ)≤((n₁*n : ℕ) : ℝ) := by
          exact_mod_cast Nat.le_mul_of_pos_left n hn₁
        have hnp : (n : ℝ)≤P := (hmul.trans hs.2.le).trans hXP
        exact hn (mem_filter.mpr
          ⟨mem_Icc.mpr ⟨Nat.pos_of_ne_zero hn0,Nat.le_floor hnp⟩,hq⟩)
      simp [hz]
    · simp [hq]
  rw [he]
  exact sum_congr rfl (fun n hn => if_pos (mem_filter.mp hn).2)

/-- Exact finite-support form of the actual psi-basis arithmetic sum. -/
theorem actual151_psi_arithmetic_sum_finite {D : ℕ}
    (χ : RealPrimitiveCharacter D) (hD : 1<D) (c : ℝ) (j : Fin 3)
    (n₁ : ℕ) (hn₁ : 0<n₁) :
    lemma151ArithmeticSum χ c j (lemma151BPsi χ) n₁ =
      χ.evalNat n₁ * ∑ n∈roughCollisionDomain D ⌊lemma23PaperP D⌋₊,
        lemma151BChiPsi D (n₁*n)*lemma151RhoStar χ (lemma83PaperBeta D c j) n/n := by
  rw [b_repaired_rough_sum χ hD c j n₁,
    actual151_weight_tsum_finite (b_canonical_strict_support D) n₁ hn₁
      (actual151_b_product_cutoff_le_P D)]
  rfl

/-- A nonzero pair of the original U,V kernels forces its rough product below
P. This is the support justification for removing the product condition. -/
theorem actual151_kernel_pair_product_le_floor {D l₁ l₂ a b : ℕ}
    (hl₁ : 0<l₁) (hl₂ : 0<l₂)
    (hne : lemma151First D (l₁*a)*lemma151Second D (l₂*b)≠0) :
    a*b≤⌊lemma23PaperP D⌋₊ := by
  have hs₁ := b_first_strict_support D (l₁*a) (left_ne_zero_of_mul hne)
  have hs₂ := b_second_strict_support D (l₂*b) (right_ne_zero_of_mul hne)
  have ha : (a : ℝ)≤((l₁*a : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_mul_of_pos_left a hl₁
  have hb : (b : ℝ)≤((l₂*b : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_mul_of_pos_left b hl₂
  have hp : ((a*b : ℕ) : ℝ)<bProductCutoff D := by
    calc
      _ = (a : ℝ)*(b : ℝ) := Nat.cast_mul _ _
      _ ≤ ((l₁*a : ℕ) : ℝ)*((l₂*b : ℕ) : ℝ) :=
        mul_le_mul ha hb (Nat.cast_nonneg b) (Nat.cast_nonneg (l₁*a))
      _ < bFirstCutoff D*bSecondCutoff D :=
        mul_lt_mul hs₁.2 hs₂.2.le (Nat.cast_pos.mpr hs₂.1)
          ((Nat.cast_pos.mpr hs₁.1).trans hs₁.2).le
      _ = _ := rfl
  exact Nat.le_floor (hp.le.trans (actual151_b_product_cutoff_le_P D))

end ZhangLS.Spec
