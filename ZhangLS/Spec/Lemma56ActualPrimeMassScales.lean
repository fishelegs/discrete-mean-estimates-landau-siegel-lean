import ZhangLS.Spec.Lemma56PrincipalMassSharpPrime
import ZhangLS.Spec.Lemma56PrimeMassNormalization

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Metric Finset Filter
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

lemma lemma56_principal_mass_window_width {L : ℝ} (hL : 10000000 ≤ L) :
    4 ≤ Real.exp (L ^ 9) * L ^ (-68 : ℤ) := by
  have hLp : 0 < L := by linarith only [hL]
  have hL1 : 1 ≤ L := by linarith only [hL]
  have hp := (lemma56_principal_mass_smoothing_polynomial hL).2
  have h132 : 4 ≤ L ^ 132 := by
    have hh : L ≤ L ^ 132 := by simpa only [pow_one] using pow_le_pow_right₀ hL1 (by norm_num : (1 : ℕ) ≤ 132)
    linarith only [hh, hL]
  have hz : L ^ 200 * L ^ (-68 : ℤ) = L ^ 132 := by
    change L ^ (200 : ℤ) * L ^ (-68 : ℤ) = L ^ (132 : ℤ)
    rw [← zpow_add₀ hLp.ne']
    norm_num
  rw [← hz] at h132
  exact h132.trans (mul_le_mul_of_nonneg_right hp (zpow_nonneg hLp.le _))

lemma lemma56_principal_mass_prefix_error_budget {L C : ℝ} (hL : 10000000 ≤ L)
    (hC : 0 ≤ C) (hCL : C ≤ L) :
    2 * C * Real.exp (L ^ 9) * L ^ (-191 : ℤ) ≤
      Real.exp (L ^ 9) * L ^ (-68 : ℤ) / 4 := by
  have hLp : 0 < L := by linarith only [hL]
  have hL1 : 1 ≤ L := by linarith only [hL]
  have h122 : 8 ≤ L ^ 122 := by
    have hh : L ≤ L ^ 122 := by simpa only [pow_one] using pow_le_pow_right₀ hL1 (by norm_num : (1 : ℕ) ≤ 122)
    linarith only [hh, hL]
  have hz1 : L * L ^ (-191 : ℤ) = L ^ (-190 : ℤ) := by
    calc
      _ = L ^ (1 : ℤ) * L ^ (-191 : ℤ) := by rw [zpow_one]
      _ = _ := by rw [← zpow_add₀ hLp.ne']; norm_num
  have hz2 : L ^ (-190 : ℤ) * L ^ 122 = L ^ (-68 : ℤ) := by
    change L ^ (-190 : ℤ) * L ^ (122 : ℤ) = L ^ (-68 : ℤ)
    rw [← zpow_add₀ hLp.ne']
    norm_num
  have hb := mul_le_mul_of_nonneg_left h122 (zpow_nonneg hLp.le (-190 : ℤ))
  rw [hz2] at hb
  have hbP := mul_le_mul_of_nonneg_left hb (Real.exp_nonneg (L ^ 9))
  calc
    _ ≤ 2 * L * Real.exp (L ^ 9) * L ^ (-191 : ℤ) := by gcongr
    _ = 2 * Real.exp (L ^ 9) * L ^ (-190 : ℤ) := by
      calc
        _ = 2 * Real.exp (L ^ 9) * (L * L ^ (-191 : ℤ)) := by ring
        _ = _ := by rw [hz1]
    _ ≤ _ := by nlinarith only [hbP]

noncomputable def lemma56PaperPrimeLowerCut (D : ℕ) : ℝ :=
  ((⌊lemma23PaperP D⌋₊ + 1 : ℕ) : ℝ)

lemma lemma56_paper_prime_mass_cut_parameters {D : ℕ} (hL : 10000000 ≤ lemma23PaperL D) :
    1 ≤ lemma56PaperPrimeLowerCut D ∧ lemma56PaperPrimeLowerCut D ≤ 2 * lemma23PaperP D ∧
      1 ≤ lemma56PrimeUpper D ∧ lemma56PrimeUpper D ≤ 2 * lemma23PaperP D ∧
        lemma56PaperPrimeLowerCut D ≤ lemma56PrimeUpper D ∧
          (3 / 4 : ℝ) * lemma23PaperP D * lemma23PaperL D ^ (-68 : ℤ) ≤
            lemma56PrimeUpper D - lemma56PaperPrimeLowerCut D := by
  have hP : 0 < lemma23PaperP D := Real.exp_pos _
  have hp := lemma56_paper_prime_weight_parameters (by linarith only [hL] : 2000 ≤ lemma23PaperL D)
  have hw := lemma56_principal_mass_window_width hL
  change 4 ≤ lemma23PaperP D * lemma23PaperL D ^ (-68 : ℤ) at hw
  have hm1 : 1 ≤ lemma56PaperPrimeLowerCut D := by
    unfold lemma56PaperPrimeLowerCut
    exact_mod_cast (show 1 ≤ ⌊lemma23PaperP D⌋₊ + 1 by omega)
  have hmP : lemma56PaperPrimeLowerCut D ≤ lemma23PaperP D + 1 := by
    have hh := Nat.floor_le hP.le
    unfold lemma56PaperPrimeLowerCut
    rw [Nat.cast_add, Nat.cast_one]
    linarith only [hh]
  have hgap : (3 / 4 : ℝ) * lemma23PaperP D * lemma23PaperL D ^ (-68 : ℤ) ≤
      lemma56PrimeUpper D - lemma56PaperPrimeLowerCut D := by
    unfold lemma56PrimeUpper
    nlinarith only [hw, hmP]
  have hwidth0 : 0 ≤ lemma23PaperP D * lemma23PaperL D ^ (-68 : ℤ) := by linarith only [hw]
  exact ⟨hm1, by linarith only [hmP, hp.2.1], by linarith only [hp.2.1, hp.2.2.1],
    by linarith only [hp.2.2.2.1], by linarith only [hgap, hwidth0], hgap⟩

end ZhangLS.Spec
