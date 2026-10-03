import ZhangLS.Spec.LogMomentQuantitative

/-! Uniform thresholds fixed before both conductor and character. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Filter
open scoped Topology

lemma lemma171_left_majorant_nonneg (D : ℕ) : 0 ≤ lemma171LeftMajorant D := by
  have hK := lemma32_regular_product_bound_pos (3/4)
  unfold lemma171LeftMajorant
  positivity

lemma lemma171_scaled_left_majorant_tendsto (k : ℕ) :
    Tendsto (fun D : ℕ => lemma23PaperL D ^ k * lemma171LeftMajorant D) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [lemma171_log_tendsto_atTop.eventually (eventually_ge_atTop 1)] with D hL
    have h0 : 0 ≤ lemma23PaperL D ^ k * lemma171LeftMajorant D :=
      mul_nonneg (pow_nonneg (by linarith) _) (lemma171_left_majorant_nonneg D)
    exact ha.trans_le h0
  · intro b hb
    obtain ⟨D₀, _, hsmall⟩ := lemma171_subexponential_absorption
      lemma171LeftErrorConstant (1/4) lemma171_left_error_constant_pos.le
      (by norm_num) 4 (75+k) b hb
    filter_upwards [eventually_ge_atTop D₀,
      lemma171_log_tendsto_atTop.eventually (eventually_ge_atTop 1)] with D hD hL
    calc
      _ ≤ lemma23PaperL D ^ k * (lemma171LeftErrorConstant * (D : ℝ)^4 *
          lemma23PaperL D ^ 75 * Real.exp (-(1/4 : ℝ) * lemma23PaperL D^(11/10 : ℝ))) :=
        mul_le_mul_of_nonneg_left (lemma171_left_majorant_polynomial_bound hL)
          (pow_nonneg (by linarith) _)
      _ = lemma171LeftErrorConstant * (D : ℝ)^4 * lemma23PaperL D ^ (75+k) *
          Real.exp (-(1/4 : ℝ) * lemma23PaperL D^(11/10 : ℝ)) := by rw [pow_add]; ring
      _ < b := hsmall D hD

lemma lemma171_log_power_endpoint_tendsto (k : ℕ) :
    Tendsto (fun D : ℕ => lemma23PaperL D ^ k * (D : ℝ)^(-4 : ℤ)) atTop (𝓝 0) := by
  have hh := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k : ℝ) 4 (by norm_num)).comp
    lemma171_log_tendsto_atTop
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with D hD
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  simp only [Function.comp_apply, Real.rpow_natCast]
  congr 1
  rw [show -(4 : ℝ) * lemma23PaperL D = -(4 * lemma23PaperL D) by ring,
    Real.exp_neg]
  have hfour : Real.exp (4 * lemma23PaperL D) = (D : ℝ)^4 := by
    simpa [lemma23PaperL, Real.exp_log hD0] using Real.exp_nat_mul (lemma23PaperL D) 4
  rw [hfour]
  simp [zpow_neg, zpow_ofNat]

lemma lemma171_first_log_moment_budget_expansion {D : ℕ} (hL : 0 < lemma23PaperL D) :
    lemma171FirstLogMomentBudget D =
      (1 + lemma44InverseSquareMass) *
        (lemma23PaperL D ^ (-180 : ℤ) + lemma23PaperL D ^ (-171 : ℤ)) +
      3780 * lemma23PaperL D ^ (-2002 : ℤ) +
      lemma171LogResidueErrorConstant * lemma23PaperL D ^ (-2016 : ℤ) +
      lemma171ResidueErrorConstant * lemma23PaperL D ^ (-2009 : ℤ) +
      2 * (lemma23PaperL D ^ 9 * (D : ℝ) ^ (-4 : ℤ)) +
      4 * lemma171LeftMajorant D + lemma23PaperL D ^ 9 * lemma171LeftMajorant D := by
  have h180 : lemma23PaperL D ^ 9 * lemma23PaperL D ^ (-180 : ℤ) =
      lemma23PaperL D ^ (-171 : ℤ) := by
    simpa only [Int.reduceAdd, zpow_ofNat] using (zpow_add₀ hL.ne' (9 : ℤ) (-180)).symm
  have h2011 : lemma23PaperL D ^ 9 * lemma23PaperL D ^ (-2011 : ℤ) =
      lemma23PaperL D ^ (-2002 : ℤ) := by
    simpa only [Int.reduceAdd, zpow_ofNat] using (zpow_add₀ hL.ne' (9 : ℤ) (-2011)).symm
  have h2018 : lemma23PaperL D ^ 9 * lemma23PaperL D ^ (-2018 : ℤ) =
      lemma23PaperL D ^ (-2009 : ℤ) := by
    simpa only [Int.reduceAdd, zpow_ofNat] using (zpow_add₀ hL.ne' (9 : ℤ) (-2018)).symm
  unfold lemma171FirstLogMomentBudget lemma171HarmonicErrorBudget
  rw [mul_add, mul_add, mul_add, mul_add]
  linear_combination (1 + lemma44InverseSquareMass) * h180 + 1260 * h2011 +
    lemma171ResidueErrorConstant * h2018

lemma lemma171_first_log_moment_budget_tendsto :
    Tendsto lemma171FirstLogMomentBudget atTop (𝓝 0) := by
  have hp (n : ℤ) (hn : n < 0) :
      Tendsto (fun D : ℕ => lemma23PaperL D ^ n) atTop (𝓝 0) :=
    (tendsto_zpow_atTop_zero hn).comp lemma171_log_tendsto_atTop
  have hl : Tendsto lemma171LeftMajorant atTop (𝓝 0) := by
    simpa using lemma171_scaled_left_majorant_tendsto 0
  have hshort := ((hp (-180) (by norm_num)).add (hp (-171) (by norm_num))).const_mul
    (1 + lemma44InverseSquareMass)
  have hmiddle := hshort.add ((hp (-2002) (by norm_num)).const_mul 3780)
  have hresidue := (hmiddle.add
    ((hp (-2016) (by norm_num)).const_mul lemma171LogResidueErrorConstant)).add
    ((hp (-2009) (by norm_num)).const_mul lemma171ResidueErrorConstant)
  have hb := ((hresidue.add ((lemma171_log_power_endpoint_tendsto 9).const_mul 2)).add
    (hl.const_mul 4)).add (lemma171_scaled_left_majorant_tendsto 9)
  simp only [mul_zero, add_zero] at hb
  apply hb.congr'
  filter_upwards [lemma171_log_tendsto_atTop.eventually (eventually_gt_atTop 0)] with D hL
  exact (lemma171_first_log_moment_budget_expansion hL).symm

/-- Actual first logarithmic moment expansion under original (A), with a
threshold chosen before D and χ. No desired-error or chosen-jet premise occurs. -/
theorem lemma171_actual_first_log_moment_uniform (ε : ℝ) (hε : 0 < ε) :
    ∃ D₀ : ℕ, 2 ≤ D₀ ∧ ∀ D : ℕ, D₀ ≤ D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ → |lemma171FirstLogMomentError χ| < ε := by
  obtain ⟨D₁, hsmall⟩ := eventually_atTop.mp
    (lemma171_first_log_moment_budget_tendsto.eventually (eventually_lt_nhds hε))
  obtain ⟨D₂, hD₂, hscale⟩ := lemma171_smoothing_scale_threshold
  obtain ⟨D₃, habs⟩ := lemma31_exponential_absorption_threshold
  obtain ⟨D₄, _, hmain⟩ := lemma171_actual_main_gt_half
  refine ⟨max D₂ (max D₁ (max D₃ D₄)), hD₂.trans (le_max_left _ _), ?_⟩
  intro D hD χ hA
  have h2 : D₂ ≤ D := (le_max_left _ _).trans hD
  have hr := (le_max_right _ _).trans hD
  have h1 : D₁ ≤ D := (le_max_left _ _).trans hr
  have hr' := (le_max_right _ _).trans hr
  have h3 : D₃ ≤ D := (le_max_left _ _).trans hr'
  have h4 : D₄ ≤ D := (le_max_right _ _).trans hr'
  have hd : realLDerivAtOne χ ≠ 0 := by
    intro hz
    have hzero : lemma171MainTerm χ = 0 := by simp [lemma171MainTerm, hz]
    have hpos := hmain D h4 χ hA
    linarith
  exact (lemma171_actual_first_log_moment_error_quantitative χ (habs D h3).1
    (hscale D h2).1 (hscale D h2).2 hA (habs D h3).2.2 hd).trans_lt (hsmall D h1)

/-- The error is also uniformly o(a), since the actual a is eventually >1/2. -/
theorem lemma171_actual_first_log_moment_relative_uniform (ε : ℝ) (hε : 0 < ε) :
    ∃ D₀ : ℕ, 2 ≤ D₀ ∧ ∀ D : ℕ, D₀ ≤ D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ → |lemma171FirstLogMomentError χ / lemma171MainTerm χ| < ε := by
  obtain ⟨D₁, hD₁, hmain⟩ := lemma171_actual_main_gt_half
  obtain ⟨D₂, _, herr⟩ := lemma171_actual_first_log_moment_uniform (ε/2) (by positivity)
  refine ⟨max D₁ D₂, hD₁.trans (le_max_left _ _), ?_⟩
  intro D hD χ hA
  have hp := hmain D ((le_max_left _ _).trans hD) χ hA
  have he := herr D ((le_max_right _ _).trans hD) χ hA
  rw [abs_div, abs_of_pos (by linarith : 0 < lemma171MainTerm χ)]
  apply (div_lt_iff₀ (by linarith : 0 < lemma171MainTerm χ)).mpr
  nlinarith

end ZhangLS.Spec
