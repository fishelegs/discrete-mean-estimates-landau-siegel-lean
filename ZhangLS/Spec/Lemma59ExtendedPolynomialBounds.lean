import ZhangLS.Spec.Lemma59Parameters

/-! # Auxiliary inputs for Lemma 5.9

The actual original closed strip, actual coefficients and actual L-function
are retained. The full `Lemma59Target` quotient is proved in `Lemma59.lean`.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Set Metric MeasureTheory Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

theorem lemma59_extended_center_displacement_le_three {D : ℕ} {s : ℂ}
    (hL : 100 ≤ lemma23PaperL D) (hs : Lemma59InExtendedOmega1 D s) :
    ‖lemma23PaperCenter D - s‖ ≤ 3 * lemma23PaperL D ^ 405 := by
  let L := lemma23PaperL D
  have hLpos : 0 < L := by dsimp [L]; linarith
  have hL1 : 1 ≤ L := by dsimp [L]; linarith
  have hdelta0 : 0 ≤ Real.log L / (100 * L) :=
    div_nonneg (Real.log_nonneg hL1) (by positivity)
  have hdelta1 : Real.log L / (100 * L) ≤ 1 / 100 := by
    apply (div_le_iff₀ (by positivity : 0 < 100 * L)).mpr
    nlinarith [Real.log_le_self hLpos.le]
  have hre : |(lemma23PaperCenter D - s).re| ≤ 1 := by
    rw [Complex.sub_re]
    change |1 / 2 - s.re| ≤ 1
    apply abs_le.mpr
    change 1 / 2 - Real.log L / (100 * L) < s.re ∧
      s.re < 1 + Real.log L / (100 * L) ∧ _ at hs
    constructor <;> linarith [hs.1, hs.2.1]
  have him : |(lemma23PaperCenter D - s).im| ≤ L ^ 405 + 20 := by
    rw [Complex.sub_im, abs_sub_comm]
    exact hs.2.2.le
  have hLp : 100 ≤ L ^ 405 := by
    have hp : L ≤ L ^ 405 := by
      simpa using pow_le_pow_right₀ hL1 (show 1 ≤ 405 by norm_num)
    exact hL.trans hp
  calc
    ‖lemma23PaperCenter D - s‖ ≤
        |(lemma23PaperCenter D - s).re| + |(lemma23PaperCenter D - s).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ ≤ L ^ 405 + 21 := by linarith
    _ ≤ 3 * L ^ 405 := by linarith

theorem lemma59_extended_center_displacement_le {D : ℕ} {s : ℂ}
    (hL : 100 ≤ lemma23PaperL D) (hs : Lemma59InExtendedOmega1 D s) :
    ‖lemma23PaperCenter D - s‖ ≤ lemma23PaperL D ^ 406 := by
  calc
    ‖lemma23PaperCenter D - s‖ ≤ 3 * lemma23PaperL D ^ 405 :=
      lemma59_extended_center_displacement_le_three hL hs
    _ ≤ lemma23PaperL D * lemma23PaperL D ^ 405 :=
      mul_le_mul_of_nonneg_right (by linarith only [hL] : 3 ≤ lemma23PaperL D) (by positivity)
    _ = lemma23PaperL D ^ 406 := by rw [pow_succ]; ring

theorem lemma59_extended_power_kernel_le {D : ℕ} {s : ℂ} {t : ℝ}
    (hL : 100 ≤ lemma23PaperL D) (hs : Lemma59InExtendedOmega1 D s)
    (ht : 1 ≤ t) (htD : t ≤ (D : ℝ) ^ 80) :
    ‖lemma23AbelPowerWeight (lemma23PaperCenter D - s) t‖ ≤ lemma23PaperL D := by
  have hlogt : Real.log t ≤ 80 * lemma23PaperL D := by
    calc
      Real.log t ≤ Real.log ((D : ℝ) ^ 80) := Real.log_le_log (by linarith) htD
      _ = 80 * lemma23PaperL D := by rw [Real.log_pow]; rfl
  apply lemma23AbelPowerWeight_norm_le_of_strip_exponent (by linarith) ht hlogt
  rw [Complex.sub_re]
  change 1 / 2 - s.re ≤ Real.log (lemma23PaperL D) / (100 * lemma23PaperL D)
  linarith [hs.1]

theorem lemma59_extended_FG_bound {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N) (s : ℂ)
    (hL : 100 ≤ lemma23PaperL D) (hgood : Lemma23GoodPartialSums χ ψ)
    (hs : Lemma59InExtendedOmega1 D s) :
    ‖lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod N)) s‖ +
      ‖lemma23ActualSectionFourG χ (fun n => ψ (n : ZMod N)) s‖ ≤
      2 * lemma23PaperL D ^ 79 := by
  have hL3 : 3 ≤ lemma23PaperL D := by linarith only [hL]
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast χ.modulus_pos
  have hEndpoint := lemma59_extended_power_kernel_le hL hs
    (one_le_pow₀ hD1) (le_refl ((D : ℝ) ^ 80))
  rw [← Nat.cast_pow] at hEndpoint
  have hKernel : ∀ t ∈ Set.Ioc (1 : ℝ) ((D ^ 80 : ℕ) : ℝ),
      ‖lemma23AbelPowerWeight (lemma23PaperCenter D - s) t‖ ≤ lemma23PaperL D := by
    intro t ht
    apply lemma59_extended_power_kernel_le hL hs ht.1.le
    simpa only [Nat.cast_pow] using ht.2
  have hbounds := hgood.x1_x2_bounds
  have hF := lemma23ActualSectionFourF_norm_le_of_X1_data χ ψ
    (lemma23PaperCenter D) s (lemma23PaperL D) hL3 hbounds.1.1 hbounds.1.2
    (lemma59_extended_center_displacement_le hL hs) hEndpoint hKernel
  have hG := lemma23ActualSectionFourG_norm_le_of_X2_data χ ψ
    (lemma23PaperCenter D) s (lemma23PaperL D) hL3 hbounds.2.1 hbounds.2.2
    (lemma59_extended_center_displacement_le hL hs) hEndpoint hKernel
  linarith

theorem lemma59_extended_product_bound {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N) (s : ℂ)
    (hL : 100 ≤ lemma23PaperL D) (hgood : Lemma23GoodPartialSums χ ψ)
    (hs : Lemma59InExtendedOmega1 D s) :
    ‖lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod N)) s *
        lemma23ActualSectionFourG χ (fun n => ψ (n : ZMod N)) s - 1‖ ≤
      4 * lemma23PaperL D ^ (-227 : ℤ) := by
  let L := lemma23PaperL D
  let c := lemma23ActualX4CenteredCoefficient χ ψ
  have hL1 : 1 ≤ L := by dsimp [L]; linarith
  have hLne : L ≠ 0 := by dsimp [L]; linarith
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast χ.modulus_pos
  have hD8 : (D : ℝ) ^ 8 ≤ (D : ℝ) ^ 80 := pow_le_pow_right₀ hD1 (by norm_num)
  have hEndpoint :
      ‖lemma23AbelPowerWeight (lemma23PaperCenter D - s) ((D ^ 8 : ℕ) : ℝ)‖ ≤ L := by
    rw [Nat.cast_pow]
    exact lemma59_extended_power_kernel_le hL hs (one_le_pow₀ hD1) hD8
  have hbounds := hgood.x4_bounds
  have hCoefEndpoint : ‖∑ n ∈ Finset.Icc 0 (D ^ 8), c n‖ ≤ L ^ (-633 : ℤ) := by
    have hx := lemma23ActualX4_eq_centered_partial_sum χ ψ ((D : ℝ) ^ 8)
    rw [← Nat.cast_pow, Nat.floor_natCast] at hx
    change ‖∑ n ∈ Finset.Icc 0 (D ^ 8), lemma23ActualX4CenteredCoefficient χ ψ n‖ ≤
      lemma23PaperL D ^ (-633 : ℤ)
    rw [← hx, Nat.cast_pow]
    exact hbounds.1
  have hIntegral : (∫ t in Set.Ioc (1 : ℝ) ((D ^ 8 : ℕ) : ℝ),
      ‖∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n‖ / t) ≤ L ^ (-633 : ℤ) := by
    dsimp [c, L]
    simpa only [Nat.cast_pow, ← lemma23ActualX4_eq_centered_partial_sum] using hbounds.2
  have hWeight : ∀ t ∈ Set.Ioc (1 : ℝ) ((D ^ 8 : ℕ) : ℝ),
      ‖lemma23PaperCenter D - s‖ *
          ‖lemma23AbelPowerWeight (lemma23PaperCenter D - s) t‖ ≤ 3 * L ^ 406 := by
    intro t ht
    have ht8 : t ≤ (D : ℝ) ^ 8 := by simpa only [Nat.cast_pow] using ht.2
    have htD : t ≤ (D : ℝ) ^ 80 := ht8.trans hD8
    calc
      _ ≤ (3 * L ^ 405) * L :=
        mul_le_mul (lemma59_extended_center_displacement_le_three hL hs)
          (lemma59_extended_power_kernel_le hL hs ht.1.le htD) (norm_nonneg _) (by positivity)
      _ = 3 * L ^ 406 := by rw [pow_succ]; ring
  have hAbel := lemma23_abel_power_weight_norm_bound (by simp [c]) hEndpoint
    hCoefEndpoint (by positivity : 0 ≤ 3 * L ^ 406) hWeight hIntegral
  have hpower : L ^ 406 * L ^ (-633 : ℤ) = L ^ (-227 : ℤ) := by
    rw [← zpow_natCast, ← zpow_add₀ hLne]
    norm_num
  have hfirst : L * L ^ (-633 : ℤ) ≤ L ^ (-227 : ℤ) := by
    rw [← hpower]
    apply mul_le_mul_of_nonneg_right
    · simpa using pow_le_pow_right₀ hL1 (show 1 ≤ 406 by norm_num)
    · positivity
  rw [lemma23ActualSectionFourFG_sub_one_eq_centered_abel_sum]
  calc
    _ ≤ L * L ^ (-633 : ℤ) + (3 * L ^ 406) * L ^ (-633 : ℤ) := hAbel
    _ = L * L ^ (-633 : ℤ) + 3 * L ^ (-227 : ℤ) := by rw [mul_assoc, hpower]
    _ ≤ 4 * L ^ (-227 : ℤ) := by linarith

lemma lemma59_extended_L227_error_lt_half {L : ℝ} (hL : 3 ≤ L) :
    4 * L ^ (-227 : ℤ) < 1 / 2 := by
  have hL1 : 1 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  have hp2 : 9 ≤ L ^ 2 := by nlinarith
  have hp227 : 9 ≤ L ^ 227 := hp2.trans (pow_le_pow_right₀ hL1 (by norm_num))
  have hp227pos : 0 < L ^ 227 := pow_pos hLpos _
  have hinv : (L ^ 227)⁻¹ ≤ (9 : ℝ)⁻¹ :=
    (inv_le_inv₀ hp227pos (by norm_num : 0 < (9 : ℝ))).mpr hp227
  have hpow : L ^ (-227 : ℤ) = (L ^ 227)⁻¹ := by
    rw [zpow_neg, zpow_ofNat]
  rw [hpow]
  norm_num at hinv
  linarith

end ZhangLS.Spec
