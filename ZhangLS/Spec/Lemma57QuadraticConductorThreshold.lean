import ZhangLS.Spec.Lemma57GaussianQuadraticMoment
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

/-!
# Eventual budget under conductor-linear quadratic growth

This module proves that a quadratic bound with coefficient no larger than
the conductor `D` is quantitatively strong enough for the shifted integral
when `D` is sufficiently large. The bound on the actual zeta/L factor is
still an explicit hypothesis, not a proved analytic fact.
-/

namespace ZhangLS.Spec

open Complex Filter
open scoped Real Topology

/-- Every fixed power of `log D` is negligible compared with `D`. -/
theorem tendsto_log_pow_div_modulus_zero (n : ℕ) :
    Tendsto (fun D : ℕ => Real.log (D : ℝ) ^ n / (D : ℝ))
      atTop (nhds 0) := by
  simpa using
    (Real.tendsto_pow_log_div_mul_add_atTop 1 0 n one_ne_zero).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))

/-- A convenient polynomial-log majorant for the quadratic Gaussian moment. -/
noncomputable def lemma57QuadraticConductorMajorant (D : ℕ) : ℝ :=
  ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ * Real.exp 1 *
    (8 * Real.pi) *
    ((Real.log (D : ℝ) ^ 30 + 8 * Real.log (D : ℝ) ^ 60) / (D : ℝ))

/-- A closed, computable modulus threshold for the quadratic-conductor error
estimate.  The expression is deliberately kept factored instead of expanded
to its enormous decimal numeral. -/
def lemma57ExplicitModulusThreshold : ℕ := 3 ^ 10_000_000

/-- At the explicit threshold, `log D` is at least ten million. -/
theorem lemma57_log_ge_ten_million {D : ℕ}
    (hD : lemma57ExplicitModulusThreshold ≤ D) :
    10_000_000 ≤ Real.log (D : ℝ) := by
  have hpow_nat : 3 ^ 10_000_000 ≤ D := hD
  have hpow_real : (3 : ℝ) ^ 10_000_000 ≤ (D : ℝ) := by
    exact_mod_cast hpow_nat
  have hlogthree : (1 : ℝ) ≤ Real.log 3 :=
    (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 3)).2
      (le_of_lt Real.exp_one_lt_three)
  have hlogmono := Real.log_le_log
    (by positivity : (0 : ℝ) < (3 : ℝ) ^ 10_000_000) hpow_real
  rw [Real.log_pow] at hlogmono
  have hlogmul : (10_000_000 : ℝ) ≤
      (10_000_000 : ℝ) * Real.log 3 :=
    by
      simpa using mul_le_mul_of_nonneg_left hlogthree
        (by norm_num : (0 : ℝ) ≤ 10_000_000)
  norm_num at hlogmono
  linarith [hlogmono, hlogmul]

/-- The closed threshold also guarantees that the modulus is nontrivial. -/
theorem lemma57_one_lt_of_explicit_threshold {D : ℕ}
    (hD : lemma57ExplicitModulusThreshold ≤ D) : 1 < D := by
  change 3 ^ 10_000_000 ≤ D at hD
  have hpow : 3 ≤ 3 ^ 10_000_000 :=
    Nat.le_self_pow (by omega : 10_000_000 ≠ 0) 3
  exact lt_of_lt_of_le (by norm_num : 1 < 3) (hpow.trans hD)

/-- The polynomial-log majorant, including the proved factor `288`, is below
the remaining `1/32` error budget for every modulus above the closed threshold.
This replaces the non-effective eventuality witness at the final application. -/
theorem lemma57_scaled_majorant_le_one_thirtysecond_of_explicit_threshold
    {D : ℕ} (hD : lemma57ExplicitModulusThreshold ≤ D) :
    288 * lemma57QuadraticConductorMajorant D ≤ (1 : ℝ) / 32 := by
  have hDgt : 1 < D := lemma57_one_lt_of_explicit_threshold hD
  have hDr : (0 : ℝ) < D := by exact_mod_cast (Nat.zero_lt_of_lt hDgt)
  let x : ℝ := Real.log (D : ℝ)
  have hxlarge : (10_000_000 : ℝ) ≤ x := by
    simpa [x] using lemma57_log_ge_ten_million hD
  clear hD
  have hxpos : 0 < x := by linarith
  have hxone : 1 ≤ x := by linarith

  have hexp_two_lt_nine : Real.exp 2 < 9 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_one_lt_three, Real.exp_pos (1 : ℝ),
      mul_pos (Real.exp_pos (1 : ℝ))
        (sub_pos.mpr Real.exp_one_lt_three)]
  have hexp_two_le_x : Real.exp 2 ≤ x := by
    have h : Real.exp 2 ≤ (10_000_000 : ℝ) := by
      linarith [hexp_two_lt_nine]
    exact h.trans hxlarge
  have hratio := Real.log_div_sqrt_antitoneOn
    (by simp : Real.exp 2 ∈ Set.Ici (Real.exp 2))
    (show x ∈ Set.Ici (Real.exp 2) from hexp_two_le_x) hexp_two_le_x
  have hsqrt_exp_two : Real.sqrt (Real.exp 2) = Real.exp 1 := by
    rw [← Real.exp_half (2 : ℝ)]
    norm_num
  have hratio_le_one : Real.log x / Real.sqrt x ≤ 1 := by
    calc
      Real.log x / Real.sqrt x ≤ 2 / Real.exp 1 := by
        simpa [Real.log_exp, hsqrt_exp_two] using hratio
      _ ≤ 1 := (div_le_iff₀ (Real.exp_pos (1 : ℝ))).2
        (by nlinarith [Real.exp_one_gt_two])
  have hlog_sqrt : Real.log x ≤ Real.sqrt x :=
    by simpa using (div_le_iff₀ (Real.sqrt_pos.2 hxpos)).1 hratio_le_one
  have hsqrt_small : Real.sqrt x ≤ x / 1000 := by
    apply (Real.sqrt_le_left (by positivity : (0 : ℝ) ≤ x / 1000)).2
    have hmul := mul_nonneg (sub_nonneg.mpr hxlarge) hxpos.le
    nlinarith
  have hlog_small : 60 * Real.log x ≤ x / 2 := by
    calc
      60 * Real.log x ≤ 60 * Real.sqrt x :=
        mul_le_mul_of_nonneg_left hlog_sqrt (by norm_num)
      _ ≤ 60 * (x / 1000) :=
        mul_le_mul_of_nonneg_left hsqrt_small (by norm_num)
      _ ≤ x / 2 := by nlinarith [hxpos]
  have hpow_exp : x ^ 60 ≤ Real.exp (x / 2) := by
    rw [← Real.exp_log (pow_pos hxpos 60)]
    apply Real.exp_le_exp.mpr
    rw [Real.log_pow]
    nlinarith [hlog_small]
  have hexp_half_ge_x : x ≤ Real.exp (x / 2) := by
    calc
      x = 2 * (x / 2) := by ring
      _ ≤ Real.exp (x / 2) := Real.two_mul_le_exp

  have hpower : x ^ 30 ≤ x ^ 60 :=
    pow_le_pow_right₀ hxone (by norm_num)
  have hpoly : x ^ 30 + 8 * x ^ 60 ≤ 9 * x ^ 60 := by
    nlinarith [hpower, pow_nonneg hxpos.le 60]
  have hpower_div : x ^ 60 / Real.exp x ≤ 1 / x := by
    calc
      x ^ 60 / Real.exp x ≤ Real.exp (x / 2) / Real.exp x :=
        div_le_div_of_nonneg_right hpow_exp (Real.exp_pos x).le
      _ = 1 / Real.exp (x / 2) := by
        have hexpeq : Real.exp x = Real.exp (x / 2) * Real.exp (x / 2) := by
          rw [← Real.exp_add]
          congr 1 <;> ring
        rw [hexpeq]
        field_simp
      _ ≤ 1 / x := one_div_le_one_div_of_le hxpos hexp_half_ge_x
  have hpoly_div :
      (x ^ 30 + 8 * x ^ 60) / Real.exp x ≤ 9 / x := by
    calc
      (x ^ 30 + 8 * x ^ 60) / Real.exp x ≤
          (9 * x ^ 60) / Real.exp x :=
        div_le_div_of_nonneg_right hpoly (Real.exp_pos x).le
      _ = 9 * (x ^ 60 / Real.exp x) := by ring
      _ ≤ 9 * (1 / x) :=
        mul_le_mul_of_nonneg_left hpower_div (by norm_num)
      _ = 9 / x := by ring
  have hnorm : ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ ≤ 1 := by
    have hden : (1 : ℝ) ≤ ‖2 * (Real.pi : ℂ) * I‖ := by
      rw [norm_mul, Complex.norm_I, mul_one, norm_mul,
        Complex.norm_of_nonneg Real.pi_pos.le]
      norm_num
      nlinarith [Real.one_le_pi_div_two]
    rw [norm_inv]
    exact (inv_le_one₀ (lt_of_lt_of_le (by norm_num) hden)).2 hden
  have hcoeff :
      ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ * Real.exp 1 * (8 * Real.pi) ≤ 96 := by
    calc
      ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ * Real.exp 1 * (8 * Real.pi) ≤
          1 * 3 * 32 := by
        gcongr
        · exact Real.exp_one_lt_three.le
        · nlinarith [Real.pi_le_four]
      _ = 96 := by norm_num
  have hmajor : lemma57QuadraticConductorMajorant D ≤ 864 / x := by
    change ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ * Real.exp 1 * (8 * Real.pi) *
      ((Real.log (D : ℝ) ^ 30 + 8 * Real.log (D : ℝ) ^ 60) / (D : ℝ)) ≤
        864 / x
    rw [show Real.log (D : ℝ) = x by rfl]
    rw [show (D : ℝ) = Real.exp x by
      dsimp [x]
      exact (Real.exp_log hDr).symm]
    calc
      ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ * Real.exp 1 * (8 * Real.pi) *
          ((x ^ 30 + 8 * x ^ 60) / Real.exp x) ≤
          96 * ((x ^ 30 + 8 * x ^ 60) / Real.exp x) := by
        exact mul_le_mul_of_nonneg_right hcoeff (by positivity)
      _ ≤ 96 * (9 / x) :=
        mul_le_mul_of_nonneg_left hpoly_div (by norm_num)
      _ = 864 / x := by ring
  calc
    288 * lemma57QuadraticConductorMajorant D ≤ 288 * (864 / x) :=
      mul_le_mul_of_nonneg_left hmajor (by norm_num)
    _ = 248832 / x := by ring
    _ ≤ (1 : ℝ) / 32 := by
      apply (div_le_iff₀ hxpos).2
      nlinarith [hxlarge]

/-- The majorant tends to zero along natural moduli. -/
theorem tendsto_lemma57QuadraticConductorMajorant_zero :
    Tendsto lemma57QuadraticConductorMajorant atTop (nhds 0) := by
  have h30 := tendsto_log_pow_div_modulus_zero 30
  have h60 := tendsto_log_pow_div_modulus_zero 60
  have hsum : Tendsto
      (fun D : ℕ => Real.log (D : ℝ) ^ 30 / (D : ℝ) +
        8 * (Real.log (D : ℝ) ^ 60 / (D : ℝ)))
      atTop (nhds 0) := by
    convert h30.add (h60.const_mul 8) using 1; norm_num
  have hmajor : Tendsto
      (fun D : ℕ =>
        ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ * Real.exp 1 * (8 * Real.pi) *
          (Real.log (D : ℝ) ^ 30 / (D : ℝ) +
            8 * (Real.log (D : ℝ) ^ 60 / (D : ℝ))))
      atTop (nhds 0) := by
    convert (hsum.const_mul
      (‖(2 * (Real.pi : ℂ) * I)⁻¹‖ * Real.exp 1 * (8 * Real.pi))) using 1
    norm_num
  apply hmajor.congr'
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with D hD
  dsimp [lemma57QuadraticConductorMajorant]
  rw [add_div]
  ring

/-- For `log D ≥ 2`, the explicit quadratic integral estimate with
coefficient `D` is bounded by the polynomial-log majorant above. -/
theorem lemma57QuadraticConductorExpression_le_majorant
    {D : ℕ} (hD : 1 < D) (hlog : 2 ≤ Real.log (D : ℝ)) :
    ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
        (Real.exp (-2 * Real.log (D : ℝ) +
          1 / (16 * Real.log (D : ℝ) ^ 30)) *
          ((D : ℝ) * (1 + 8 * Real.log (D : ℝ) ^ 30) *
            Real.sqrt (8 * Real.pi * Real.log (D : ℝ) ^ 30))) ≤
      lemma57QuadraticConductorMajorant D := by
  let L : ℝ := Real.log (D : ℝ)
  let δ : ℝ := 1 / (16 * L ^ 30)
  let q : ℝ := 8 * Real.pi * L ^ 30
  have hDr : (0 : ℝ) < D := by exact_mod_cast (Nat.zero_lt_of_lt hD)
  have hL : 0 < L := by dsimp [L]; linarith
  have hLone : 1 ≤ L := by dsimp [L]; linarith
  have hLpow : 1 ≤ L ^ 30 := one_le_pow₀ hLone
  have hδ : δ ≤ 1 := by
    dsimp [δ]
    apply (div_le_iff₀ (by positivity : 0 < 16 * L ^ 30)).2
    nlinarith
  have hExpLog : Real.exp L = (D : ℝ) := by
    exact Real.exp_log hDr
  have hE :
      Real.exp (-2 * L + δ) * (D : ℝ) ≤ Real.exp 1 / (D : ℝ) := by
    have heq : Real.exp (-2 * L + δ) * (D : ℝ) =
        Real.exp δ / (D : ℝ) := by
      rw [Real.exp_add]
      have htwice : -2 * L = -(L + L) := by ring
      rw [htwice, Real.exp_neg, Real.exp_add, hExpLog]
      field_simp
    rw [heq]
    gcongr
  have hpi : 1 ≤ Real.pi := by linarith [Real.one_le_pi_div_two]
  have hq : 1 ≤ q := by
    have hp : (1 : ℝ) * 1 ≤ Real.pi * L ^ 30 :=
      mul_le_mul hpi hLpow (by norm_num) (by positivity)
    dsimp [q]
    nlinarith
  have hS : Real.sqrt q ≤ q := by
    exact (Real.sqrt_le_left (by positivity : 0 ≤ q)).2 (by nlinarith [hq])
  have hP : 0 ≤ 1 + 8 * L ^ 30 := by positivity
  have hden : (D : ℝ) ≠ 0 := hDr.ne'
  have hinner :
      (Real.exp (-2 * L + δ) * (D : ℝ)) *
          ((1 + 8 * L ^ 30) * Real.sqrt q) ≤
        (Real.exp 1 / (D : ℝ)) * ((1 + 8 * L ^ 30) * q) := by
    gcongr
  calc
    ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
        (Real.exp (-2 * Real.log (D : ℝ) +
          1 / (16 * Real.log (D : ℝ) ^ 30)) *
          ((D : ℝ) * (1 + 8 * Real.log (D : ℝ) ^ 30) *
            Real.sqrt (8 * Real.pi * Real.log (D : ℝ) ^ 30))) =
      ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
        ((Real.exp (-2 * L + δ) * (D : ℝ)) *
          ((1 + 8 * L ^ 30) * Real.sqrt q)) := by
      dsimp [L, δ, q]
      ring
    _ ≤ ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
          ((Real.exp 1 / (D : ℝ)) * ((1 + 8 * L ^ 30) * q)) :=
      mul_le_mul_of_nonneg_left hinner (norm_nonneg _)
    _ = lemma57QuadraticConductorMajorant D := by
      dsimp [lemma57QuadraticConductorMajorant, q, L]
      field_simp

/-- If the actual undamped factor admits a quadratic bound with coefficient
`D`, then for every sufficiently large modulus it satisfies the full
analytic-error target under Assumption (A). This theorem does *not* assert
that the required zeta/L growth bound holds. -/
theorem exists_modulus_threshold_for_conductor_quadratic_error :
    ∃ D₀ : ℕ, ∀ {D : ℕ} (χ : RealPrimitiveCharacter D),
      D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
      Lemma57LeftQuadraticGrowth χ (D : ℝ) →
      Lemma57GaussianAnalyticErrorBound χ := by
  obtain ⟨Dlog, hlog⟩ := exists_modulus_threshold_log_ge_two
  have hsmall : ∀ᶠ D : ℕ in atTop,
      lemma57QuadraticConductorMajorant D ≤ (1 : ℝ) / 32 := by
    have h := tendsto_lemma57QuadraticConductorMajorant_zero.eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 32))
    exact h.mono (fun _ hx => hx.le)
  obtain ⟨Dmajor, hmajor⟩ := Filter.eventually_atTop.1 hsmall
  refine ⟨max Dlog Dmajor, ?_⟩
  intro D χ hDN hD hA hgrowth
  have hlogD : 2 ≤ Real.log (D : ℝ) :=
    hlog D ((le_max_left _ _).trans hDN)
  have hmajorD : lemma57QuadraticConductorMajorant D ≤ (1 : ℝ) / 32 :=
    hmajor D ((le_max_right _ _).trans hDN)
  have hC : (0 : ℝ) ≤ D := by exact_mod_cast Nat.zero_le D
  have hleft := lemma57LeftVerticalIntegral_norm_le_of_quadratic
    χ hD hC hgrowth
  have hExpr := lemma57QuadraticConductorExpression_le_majorant hD hlogD
  have hscale := lemma57Scale_ge_one hD
  have hbudget : lemma57QuadraticConductorMajorant D ≤
      (1 : ℝ) / 32 * lemma57Scale D := by linarith
  apply lemma57GaussianAnalyticErrorBound_of_shifted_norm χ hD hlogD hA
  exact (hleft.trans hExpr).trans hbudget

/-- A smaller quadratic coefficient can be enlarged to the conductor. -/
theorem lemma57LeftQuadraticGrowth_of_coefficient_le_conductor
    {D : ℕ} (χ : RealPrimitiveCharacter D) {C : ℝ}
    (hC : C ≤ (D : ℝ)) (hgrowth : Lemma57LeftQuadraticGrowth χ C) :
    Lemma57LeftQuadraticGrowth χ (D : ℝ) := by
  intro t
  exact (hgrowth t).trans
    (mul_le_mul_of_nonneg_right hC (by positivity : 0 ≤ 1 + t ^ 2))

/-- Any quadratic growth coefficient at most linear in the conductor is
enough for the large-modulus analytic-error conclusion. -/
theorem exists_modulus_threshold_for_quadratic_coefficient_error :
    ∃ D₀ : ℕ, ∀ {D : ℕ} (χ : RealPrimitiveCharacter D) {C : ℝ},
      D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
      C ≤ (D : ℝ) → Lemma57LeftQuadraticGrowth χ C →
      Lemma57GaussianAnalyticErrorBound χ := by
  obtain ⟨D₀, hD₀⟩ := exists_modulus_threshold_for_conductor_quadratic_error
  refine ⟨D₀, ?_⟩
  intro D χ C hDN hD hA hC hgrowth
  exact hD₀ χ hDN hD hA
    (lemma57LeftQuadraticGrowth_of_coefficient_le_conductor χ hC hgrowth)

end ZhangLS.Spec
