import ZhangLS.Spec.Lemma31TotalWeight
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Finset Filter
open scoped Topology

/-- The integer endpoint retains exactly the strict real cutoff. -/
lemma squareNuTailLinear_strict_floor (D n : ℕ) :
    ⌊(D : ℝ) ^ (21 / 20 : ℝ)⌋₊ < n ↔ (D : ℝ) ^ (21 / 20 : ℝ) < n :=
  Nat.floor_lt (Real.rpow_nonneg (Nat.cast_nonneg D) _)

lemma squareNuTailLinear_D_le_floor {D : ℕ} (hD : 1 < D) :
    D ≤ ⌊(D : ℝ) ^ (21 / 20 : ℝ)⌋₊ := by
  apply Nat.le_floor
  have hd : (1 : ℝ) ≤ D := by exact_mod_cast hD.le
  simpa using Real.rpow_le_rpow_of_exponent_le hd (by norm_num : (1 : ℝ) ≤ 21 / 20)

lemma squareNuTailLinear_sqrt_ratio {D : ℕ} (hD : 1 < D) :
    Real.sqrt (D : ℝ) * (Real.sqrt ((⌊(D : ℝ) ^ (21 / 20 : ℝ)⌋₊ : ℕ) : ℝ))⁻¹ ≤
      2 * (D : ℝ) ^ (-1 / 40 : ℝ) := by
  let A : ℝ := (D : ℝ) ^ (21 / 20 : ℝ)
  let M : ℕ := ⌊A⌋₊
  have hd : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hmD : D ≤ M := squareNuTailLinear_D_le_floor hD
  have hm : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hm1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have ha : 0 < A := Real.rpow_pos_of_pos hd _
  have hfloor : A < (M : ℝ) + 1 := Nat.lt_floor_add_one A
  have hA4 : A ≤ 4 * (M : ℝ) := by linarith
  have hs : Real.sqrt A ≤ 2 * Real.sqrt (M : ℝ) := by
    have hsA := Real.sq_sqrt ha.le
    have hsM := Real.sq_sqrt hm.le
    have hnA := Real.sqrt_nonneg A
    have hnM := Real.sqrt_nonneg (M : ℝ)
    nlinarith
  have hi : (Real.sqrt (M : ℝ))⁻¹ ≤ 2 * (Real.sqrt A)⁻¹ := by
    rw [← one_div (Real.sqrt (M : ℝ)), ← div_eq_mul_inv]
    apply (div_le_div_iff₀ (Real.sqrt_pos.mpr hm) (Real.sqrt_pos.mpr ha)).mpr
    simpa using hs
  have he : Real.sqrt (D : ℝ) * (Real.sqrt A)⁻¹ = (D : ℝ) ^ (-1 / 40 : ℝ) := by
    dsimp [A]
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hd.le,
      ← div_eq_mul_inv, ← Real.rpow_sub hd]
    norm_num
  calc
    _ ≤ Real.sqrt (D : ℝ) * (2 * (Real.sqrt A)⁻¹) :=
      mul_le_mul_of_nonneg_left hi (Real.sqrt_nonneg _)
    _ = 2 * (Real.sqrt (D : ℝ) * (Real.sqrt A)⁻¹) := by ring
    _ = _ := by rw [he]

lemma squareNuTailLinear_log_factor {D N : ℕ} (hL : 1 ≤ lemma23PaperL D)
    (hN : 0 < N) (hNP : (N : ℝ) ≤ lemma23PaperP D ^ 4) :
    1 + Real.log (N : ℝ) ≤ 5 * lemma23PaperL D ^ 9 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hh := Real.log_le_log hn hNP
  have hp : 1 ≤ lemma23PaperL D ^ 9 := one_le_pow₀ hL
  simp only [Real.log_pow, lemma23PaperP, Real.log_exp] at hh
  norm_num at hh
  linarith

lemma squareNuTailLinear_main_le {D N : ℕ} (χ : RealPrimitiveCharacter D)
    (hL : 1 ≤ lemma23PaperL D) (hA : NormalizedAssumptionA χ)
    (hN : 0 < N) (hNP : (N : ℝ) ≤ lemma23PaperP D ^ 4) :
    realLAtOne χ * (1 + Real.log (N : ℝ)) ≤ 5 * lemma23PaperL D ^ (-2013 : ℤ) := by
  have hl : 0 < lemma23PaperL D := by linarith
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hfac : 0 ≤ 1 + Real.log (N : ℝ) := by have := Real.log_nonneg hn; linarith
  have ha : realLAtOne χ ≤ lemma23PaperL D ^ (-2022 : ℤ) := by
    have hh : realLAtOne χ < lemma23PaperL D ^ (-2022 : ℤ) := by
      simpa only [NormalizedAssumptionA, AssumptionAWithConstant, one_mul, lemma23PaperL] using hA
    exact hh.le
  calc
    _ ≤ lemma23PaperL D ^ (-2022 : ℤ) * (5 * lemma23PaperL D ^ 9) :=
      mul_le_mul ha (squareNuTailLinear_log_factor hL hN hNP) hfac (zpow_pos hl _).le
    _ = 5 * (lemma23PaperL D ^ (-2022 : ℤ) * lemma23PaperL D ^ 9) := by ring
    _ = _ := by rw [lemma31_small_value_scale_identity _ hl]

/-- Actual character tail; no assumption about ν's tail is introduced. -/
lemma squareNuTailLinear_actual_le {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 1 ≤ lemma23PaperL D) (hA : NormalizedAssumptionA χ)
    (N : ℕ) (hNP : (N : ℝ) ≤ lemma23PaperP D ^ 4) :
    (∑ n ∈ Finset.Ioc ⌊(D : ℝ) ^ (21 / 20 : ℝ)⌋₊ N,
      lemma31NuReal χ n * (n : ℝ)⁻¹) ≤
      5 * lemma23PaperL D ^ (-2013 : ℤ) + 36 * (D : ℝ) ^ (-1 / 40 : ℝ) := by
  let M : ℕ := ⌊(D : ℝ) ^ (21 / 20 : ℝ)⌋₊
  by_cases hMN : M ≤ N
  · have hDM : D ≤ M := squareNuTailLinear_D_le_floor hD
    have hn : 0 < N := by omega
    have he := lemma31_nu_weighted_linear_tail_le χ hD M N hDM hMN
    have hs := squareNuTailLinear_sqrt_ratio hD
    have hm := squareNuTailLinear_main_le χ hL hA hn hNP
    calc
      _ ≤ realLAtOne χ * (1 + Real.log (N : ℝ)) +
          18 * Real.sqrt (D : ℝ) * (Real.sqrt (M : ℝ))⁻¹ := he
      _ ≤ _ := by dsimp [M] at *; nlinarith
  · have hempty : Finset.Ioc M N = ∅ := Finset.Ioc_eq_empty_of_le (by omega)
    change (∑ n ∈ Finset.Ioc M N, _) ≤ _
    rw [hempty, Finset.sum_empty]
    positivity

/-- Uniform total harmonic ν mass up to P^4. -/
lemma squareNuTailLinear_mass_le {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 1 ≤ lemma23PaperL D) (hA : NormalizedAssumptionA χ)
    (N : ℕ) (hNP : (N : ℝ) ≤ lemma23PaperP D ^ 4) :
    (∑ n ∈ Finset.Icc 1 N, lemma31NuReal χ n * (n : ℝ)⁻¹) ≤
      32 * lemma23PaperL D ^ 2 := by
  have hl2 : 0 ≤ lemma23PaperL D ^ 2 := sq_nonneg _
  by_cases hND : N ≤ D ^ 2
  · calc
      _ ≤ ∑ n ∈ Finset.Icc 1 (D ^ 2), lemma31NuReal χ n * (n : ℝ)⁻¹ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.Icc_subset_Icc_right hND
        · intro n hn hnot
          exact mul_nonneg (lemma31_nu_real_nonneg χ n) (by positivity)
      _ ≤ 9 * lemma23PaperL D ^ 2 := lemma31_nu_small_weighted_sum_le χ hL
      _ ≤ _ := by nlinarith
  · have hDN : D ^ 2 ≤ N := by omega
    have hn : 0 < N := lt_of_lt_of_le (pow_pos (show 0 < D by omega) _) hDN
    have he := lemma31_nu_weighted_D_square_tail_le χ hD N hDN
    have hm := squareNuTailLinear_main_le χ hL hA hn hNP
    have hd : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
    have hd1 : (1 : ℝ) ≤ D := by exact_mod_cast hD.le
    have hs : 1 ≤ Real.sqrt (D : ℝ) := by
      have hh := Real.sq_sqrt hd.le
      have hh0 := Real.sqrt_nonneg (D : ℝ)
      nlinarith
    have hi : (Real.sqrt (D : ℝ))⁻¹ ≤ 1 := by
      simpa using (inv_le_inv₀ (Real.sqrt_pos.mpr hd)
        (by norm_num : (0 : ℝ) < 1)).mpr hs
    have hz : lemma23PaperL D ^ (-2013 : ℤ) ≤ 1 :=
      zpow_le_one_of_nonpos₀ hL (by norm_num)
    have hl21 : 1 ≤ lemma23PaperL D ^ 2 := one_le_pow₀ hL
    have hsplit : (∑ n ∈ Finset.Icc 1 N, lemma31NuReal χ n * (n : ℝ)⁻¹) =
        (∑ n ∈ Finset.Icc 1 (D ^ 2), lemma31NuReal χ n * (n : ℝ)⁻¹) +
        (∑ n ∈ Finset.Ioc (D ^ 2) N, lemma31NuReal χ n * (n : ℝ)⁻¹) := by
      have hsetN : Finset.Icc 1 N = Finset.Ioc 0 N :=
        Finset.Icc_add_one_left_eq_Ioc (0 : ℕ) N
      have hsetM : Finset.Icc 1 (D ^ 2) = Finset.Ioc 0 (D ^ 2) :=
        Finset.Icc_add_one_left_eq_Ioc (0 : ℕ) (D ^ 2)
      rw [hsetN, hsetM]
      exact (Finset.sum_Ioc_consecutive (fun n => lemma31NuReal χ n * (n : ℝ)⁻¹)
        (Nat.zero_le _) hDN).symm
    rw [hsplit]
    have hh := lemma31_nu_small_weighted_sum_le χ hL
    nlinarith

lemma squareNuTailLinear_exponential_absorption_threshold :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
      1 < D ∧ 1 ≤ lemma23PaperL D ∧
        (D : ℝ) ^ (-1 / 40 : ℝ) ≤ lemma23PaperL D ^ (-2013 : ℤ) := by
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hf : Tendsto (fun D : ℕ => lemma23PaperL D ^ 2013 *
      Real.exp (-(1 / 40 : ℝ) * lemma23PaperL D)) atTop (𝓝 0) := by
    simpa only [Real.rpow_ofNat, Function.comp_apply] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2013 : ℝ) (1 / 40)
        (by norm_num)).comp ht
  have he : ∀ᶠ D : ℕ in atTop, 1 < D ∧ 1 ≤ lemma23PaperL D ∧
      (D : ℝ) ^ (-1 / 40 : ℝ) ≤ lemma23PaperL D ^ (-2013 : ℤ) := by
    filter_upwards [hf.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
      ht.eventually (eventually_ge_atTop 1), eventually_ge_atTop (2 : ℕ)]
      with D hsmall hL hD
    refine ⟨by omega, hL, ?_⟩
    have hl : 0 < lemma23PaperL D := by linarith
    have hd : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
    have hexp : (D : ℝ) ^ (-1 / 40 : ℝ) =
        Real.exp (-(1 / 40 : ℝ) * lemma23PaperL D) := by
      rw [Real.rpow_def_of_pos hd]
      congr 1
      unfold lemma23PaperL
      ring
    rw [hexp]
    simp only [zpow_neg, zpow_ofNat]
    rw [← one_mul ((lemma23PaperL D ^ 2013)⁻¹)]
    apply (le_mul_inv_iff₀ (pow_pos hl 2013)).mpr
    simpa only [mul_comm] using hsmall.le
  exact eventually_atTop.mp he

/-- Constants and modulus threshold precede the actual character and endpoint. -/
lemma squareNuTailLinear_uniform_inputs :
    ∃ D₀ : ℕ, 2 ≤ D₀ ∧ ∀ D : ℕ, D₀ ≤ D →
      1 ≤ lemma23PaperL D ∧ ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ → ∀ N : ℕ, (N : ℝ) ≤ lemma23PaperP D ^ 4 →
        (∑ n ∈ Finset.Ioc ⌊(D : ℝ) ^ (21 / 20 : ℝ)⌋₊ N,
          lemma31NuReal χ n * (n : ℝ)⁻¹) ≤ 41 * lemma23PaperL D ^ (-2013 : ℤ) ∧
        (∑ n ∈ Finset.Icc 1 N, lemma31NuReal χ n * (n : ℝ)⁻¹) ≤
          32 * lemma23PaperL D ^ 2 := by
  obtain ⟨D₀, hD₀⟩ := squareNuTailLinear_exponential_absorption_threshold
  refine ⟨max D₀ 2, le_max_right _ _, ?_⟩
  intro D hD
  obtain ⟨hd, hl, ha⟩ := hD₀ D ((le_max_left _ _).trans hD)
  refine ⟨hl, ?_⟩
  intro χ hA N hNP
  refine ⟨?_, squareNuTailLinear_mass_le χ hd hl hA N hNP⟩
  have hh := squareNuTailLinear_actual_le χ hd hl hA N hNP
  nlinarith

end ZhangLS.Spec
