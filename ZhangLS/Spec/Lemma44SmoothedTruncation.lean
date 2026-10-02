import ZhangLS.Spec.Lemma44ProductMellin

/-!
# Removing Gaussian smoothing from the short polynomial

The scale `B=P^(9/5)` is far above `D^4`. Gaussian symmetry and an explicit
tail bound therefore make the short smoothing error at most `L^-180`.
The same scalar tail estimate will also control the infinite smoothed tail.
-/

namespace ZhangLS.Spec

open Complex MeasureTheory

set_option maxHeartbeats 1000000

theorem lemma44_gaussian_weight_inv (D : ℕ) (x : ℝ) :
    zhangGaussianWeight D x⁻¹ = 1 - zhangGaussianWeight D x := by
  have hend : zhangGaussianEndpoint D x⁻¹ = -zhangGaussianEndpoint D x := by
    simp [zhangGaussianEndpoint, Real.log_inv, mul_neg]
  have hi := intervalIntegral.integral_comp_neg
    (f := fun t : ℝ => Real.exp (-(t ^ 2)))
    (a := (0 : ℝ)) (b := zhangGaussianEndpoint D x)
  simp only [neg_zero, neg_sq] at hi
  unfold zhangGaussianWeight
  rw [hend]
  rw [show (∫ t : ℝ in (0 : ℝ)..(-zhangGaussianEndpoint D x),
      Real.exp (-(t ^ 2))) =
      -(∫ t : ℝ in (0 : ℝ)..zhangGaussianEndpoint D x,
        Real.exp (-(t ^ 2))) by
      rw [intervalIntegral.integral_symm]
      exact congrArg Neg.neg hi.symm]
  ring

/-- A positive logarithmic displacement of at least one gives a simple
exponential majorant for the Gaussian tail. -/
theorem lemma44_gaussian_weight_le_exp_endpoint {D : ℕ} {x : ℝ}
    (hy : 1 ≤ -zhangGaussianEndpoint D x) :
    zhangGaussianWeight D x ≤ Real.exp (zhangGaussianEndpoint D x) := by
  rw [zhangGaussianWeight_eq_tail_of_endpoint_nonpos (by linarith)]
  have ht := zhangGaussianTail_le_exp_linear (K := 1) zero_lt_one hy
  simp only [neg_mul, one_mul, neg_neg, div_one] at ht
  have hs : (Real.sqrt Real.pi)⁻¹ ≤ 1 := by
    have hp : 1 ≤ Real.sqrt Real.pi := by
      simpa using Real.sqrt_le_sqrt (by linarith [Real.one_le_pi_div_two] : 1 ≤ Real.pi)
    exact inv_le_one_of_one_le₀ hp
  calc
    _ ≤ (Real.sqrt Real.pi)⁻¹ * Real.exp (zhangGaussianEndpoint D x) :=
      mul_le_mul_of_nonneg_left ht (inv_nonneg.mpr (Real.sqrt_nonneg _))
    _ ≤ _ := by simpa using mul_le_mul_of_nonneg_right hs (Real.exp_pos _).le

theorem lemma44_short_log_displacement {D : ℕ} (hL : 3 ≤ lemma23PaperL D)
    {n : ℕ} (hn : n ∈ Finset.Icc 1 (D ^ 4)) :
    lemma23PaperL D ^ 9 ≤
      Real.log (lemma44PaperGaussianScale D / (n : ℝ)) := by
  let L := lemma23PaperL D
  have hL1 : 1 ≤ L := by dsimp [L]; linarith
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hnp : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hDp : (0 : ℝ) < D := by
    have hDn : 0 < D ^ 4 := lt_of_lt_of_le
      (lt_of_lt_of_le (by norm_num) (Finset.mem_Icc.mp hn).1) (Finset.mem_Icc.mp hn).2
    exact_mod_cast Nat.pos_of_ne_zero (by intro h; simp [h] at hDn)
  have hlogn : Real.log (n : ℝ) ≤ 4 * L := by
    calc
      _ ≤ Real.log ((D : ℝ) ^ 4) :=
        Real.log_le_log hnp (by exact_mod_cast (Finset.mem_Icc.mp hn).2)
      _ = 4 * L := by rw [Real.log_pow]; rfl
  have hB : 0 < lemma44PaperGaussianScale D :=
    Real.rpow_pos_of_pos (Real.exp_pos _) _
  have hlogB : Real.log (lemma44PaperGaussianScale D) = (9 / 5 : ℝ) * L ^ 9 := by
    rw [lemma44PaperGaussianScale, lemma23PaperP,
      Real.log_rpow (Real.exp_pos _), Real.log_exp]
  have hL8 : (3 : ℝ) ^ 8 ≤ L ^ 8 := pow_le_pow_left₀ (by norm_num) hL 8
  have hgrowth : 5 * L ≤ L ^ 9 := by
    calc
      5 * L ≤ L ^ 8 * L := by nlinarith only [hL8, hL0]
      _ = L ^ 9 := by ring
  rw [Real.log_div hB.ne' hnp.ne', hlogB]
  nlinarith only [hgrowth, hlogn]

theorem lemma44_L24_dominates_linear {L : ℝ} (hL : 3 ≤ L) :
    2000 * L ≤ L ^ 24 := by
  have hL1 : 1 ≤ L := by linarith
  have hL7 : (3 : ℝ) ^ 7 ≤ L ^ 7 := pow_le_pow_left₀ (by norm_num) hL 7
  calc
    2000 * L ≤ L ^ 7 * L := by nlinarith only [hL7, hL]
    _ = L ^ 8 := by ring
    _ ≤ L ^ 24 := pow_le_pow_right₀ hL1 (by norm_num)

theorem lemma44_short_gaussian_weight_error {D : ℕ}
    (hD : 1 < D) (hL : 3 ≤ lemma23PaperL D)
    {n : ℕ} (hn : n ∈ Finset.Icc 1 (D ^ 4)) :
    |zhangGaussianWeight D (lemma44PaperGaussianScale D / n) - 1| ≤
      Real.exp (-(lemma23PaperL D ^ 24)) := by
  let x := lemma44PaperGaussianScale D / (n : ℝ)
  have hx : 0 < x := by
    exact div_pos (Real.rpow_pos_of_pos (Real.exp_pos _) _)
      (by exact_mod_cast (Finset.mem_Icc.mp hn).1)
  have he : lemma23PaperL D ^ 24 ≤ zhangGaussianEndpoint D x := by
    have h := mul_le_mul_of_nonneg_left (lemma44_short_log_displacement hL hn)
      (show 0 ≤ lemma23PaperL D ^ 15 by positivity)
    simpa [x, zhangGaussianEndpoint, lemma23PaperL, ← pow_add] using h
  have h24 : 1 ≤ lemma23PaperL D ^ 24 := one_le_pow₀ (by linarith)
  have hinv : -zhangGaussianEndpoint D x⁻¹ = zhangGaussianEndpoint D x := by
    simp [zhangGaussianEndpoint, Real.log_inv, mul_neg]
  have ht := lemma44_gaussian_weight_le_exp_endpoint (x := x⁻¹)
    (by rw [hinv]; exact h24.trans he)
  have hsym := lemma44_gaussian_weight_inv D x
  have hg : 0 ≤ zhangGaussianWeight D x⁻¹ := zhangGaussianWeight_nonneg hD (inv_pos.mpr hx)
  rw [hsym] at hg ht
  rw [abs_of_nonpos (by linarith : zhangGaussianWeight D x - 1 ≤ 0)]
  calc
    _ ≤ Real.exp (zhangGaussianEndpoint D x⁻¹) := by linarith only [ht]
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [hinv, he])

/-- The smoothed short polynomial at the actual paper scale. -/
noncomputable def lemma44GaussianShortDirichletSum {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 (D ^ 4),
    lemma23NuArithmeticFunction χ n * ψ (n : ZMod N) *
      exp (-s * (Real.log (n : ℝ) : ℂ)) *
        (zhangGaussianWeight D (lemma44PaperGaussianScale D / n) : ℂ)

/-- Removing the Gaussian from the actual short polynomial costs at most
`L^-180`, uniformly on the nonnegative real half-plane. -/
theorem lemma44_short_smoothing_error {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N)
    (hD : 1 < D) (hL : 3 ≤ lemma23PaperL D) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖lemma44GaussianShortDirichletSum χ ψ s -
      lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod N)) s‖ ≤
        lemma23PaperL D ^ (-180 : ℤ) := by
  let L := lemma23PaperL D
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hDp : (0 : ℝ) < D := by exact_mod_cast Nat.zero_lt_of_lt hD
  have hmajor : ∀ n ∈ Finset.Icc 1 (D ^ 4),
      ‖lemma23NuArithmeticFunction χ n * ψ (n : ZMod N) *
        exp (-s * (Real.log (n : ℝ) : ℂ))‖ ≤ (D : ℝ) ^ 4 := by
    intro n hn
    have hnp : 1 ≤ (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hnu : ‖lemma23NuArithmeticFunction χ n‖ ≤ (n : ℝ) :=
      (lemma23NuArithmeticFunction_norm_le_card_divisors χ n).trans
        (by exact_mod_cast Nat.card_divisors_le_self n)
    have hpsi := ψ.norm_le_one (n : ZMod N)
    have hexp : ‖exp (-s * (Real.log (n : ℝ) : ℂ))‖ ≤ 1 := by
      rw [norm_exp]
      apply Real.exp_le_one_iff.mpr
      simp only [mul_re, neg_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) (Real.log_nonneg hnp)
    rw [norm_mul, norm_mul]
    calc
      _ ≤ (n : ℝ) * 1 * 1 := by gcongr
      _ ≤ (D : ℝ) ^ 4 := by simpa using (show (n : ℝ) ≤ (D : ℝ) ^ 4 by
        exact_mod_cast (Finset.mem_Icc.mp hn).2)
  have hdiff : ‖lemma44GaussianShortDirichletSum χ ψ s -
      lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod N)) s‖ ≤
      (D : ℝ) ^ 8 * Real.exp (-(L ^ 24)) := by
    unfold lemma44GaussianShortDirichletSum lemma23ActualSectionFourF
      lemma23SectionFourF lemma23FiniteDirichletPolynomial
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ n ∈ Finset.Icc 1 (D ^ 4), ‖lemma23NuArithmeticFunction χ n * ψ (n : ZMod N) *
          exp (-s * (Real.log (n : ℝ) : ℂ)) *
            ((zhangGaussianWeight D (lemma44PaperGaussianScale D / n) : ℂ) - 1)‖ := by
        convert norm_sum_le (Finset.Icc 1 (D ^ 4)) _ using 1
        congr 1
        funext n
        congr 1
        ring
      _ ≤ ∑ _n ∈ Finset.Icc 1 (D ^ 4), (D : ℝ) ^ 4 * Real.exp (-(L ^ 24)) := by
        apply Finset.sum_le_sum
        intro n hn
        rw [norm_mul, ← ofReal_one, ← ofReal_sub, norm_real, Real.norm_eq_abs]
        exact mul_le_mul (hmajor n hn) (lemma44_short_gaussian_weight_error hD hL hn)
          (abs_nonneg _) (by positivity)
      _ = (D : ℝ) ^ 8 * Real.exp (-(L ^ 24)) := by
        simp [Finset.sum_const, Nat.card_Icc]
        ring
  calc
    _ ≤ (D : ℝ) ^ 8 * Real.exp (-(L ^ 24)) := hdiff
    _ = Real.exp (8 * L - L ^ 24) := by
      have heD : Real.exp L = (D : ℝ) := Real.exp_log hDp
      rw [← heD, ← Real.exp_nat_mul, ← Real.exp_add]
      norm_num
      congr 1
    _ ≤ Real.exp (-180 * Real.log L) := by
      apply Real.exp_le_exp.mpr
      have hlog := Real.log_le_sub_one_of_pos hL0
      have hpow := lemma44_L24_dominates_linear hL
      nlinarith only [hlog, hpow, hL0]
    _ = L ^ (-180 : ℤ) := by
      rw [← Real.rpow_intCast, Real.rpow_def_of_pos hL0]
      congr 1
      norm_num
      ring

end ZhangLS.Spec
