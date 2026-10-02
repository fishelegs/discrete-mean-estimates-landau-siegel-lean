import ZhangLS.Spec.Lemma59ActualLocalZeros

/-! # Actual local zeros for Lemma 5.9

Actual L-function zeros, divisors and analytic multiplicities are retained.
The full original quotient estimate is proved in `Lemma59.lean`.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Metric Set MeromorphicOn Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

lemma lemma59_large_height_bound {D : ℕ} {t : ℝ}
    (hL : 100 ≤ lemma23PaperL D)
    (ht : |t - (lemma23PaperCenter D).im| ≤ lemma23PaperL D ^ 405 + 20) :
    |t| ≤ 10 * lemma23PaperL D ^ 519 := by
  let L := lemma23PaperL D
  have hLp : 0 < L := by dsimp [L]; linarith only [hL]
  have hL1 : 1 ≤ L := by dsimp [L]; linarith only [hL]
  have hp : L ^ 405 ≤ L ^ 519 := pow_le_pow_right₀ hL1 (by norm_num)
  have hp1 : L ≤ L ^ 519 := by simpa only [pow_one] using pow_le_pow_right₀ hL1 (by norm_num : (1 : ℕ) ≤ 519)
  have hh : 20 ≤ L ^ 519 := by dsimp [L] at hp1; linarith only [hp1,hL]
  have hc : |(lemma23PaperCenter D).im| ≤ 8 * L ^ 519 := by
    change |2 * Real.pi * L ^ 519| ≤ 8 * L ^ 519
    rw [abs_of_nonneg (by positivity)]
    nlinarith only [Real.pi_le_four, pow_nonneg hLp.le 519]
  have he : t = (t - (lemma23PaperCenter D).im) + (lemma23PaperCenter D).im := by ring
  rw [he]
  have hx := abs_add_le (t - (lemma23PaperCenter D).im) (lemma23PaperCenter D).im
  change |t - (lemma23PaperCenter D).im| ≤ L ^ 405 + 20 at ht
  change _ ≤ 10 * L ^ 519
  linarith only [ht, hx, hc, hp, hh]

lemma lemma59_family_modulus_le_two_P {D p : ℕ} (ψ : DirichletCharacter ℂ p)
    (hL : 100 ≤ lemma23PaperL D) (hψ : Lemma23InPsi (D := D) ψ) :
    (p : ℝ) ≤ 2 * lemma23PaperP D := by
  have hLp : 0 < lemma23PaperL D := by linarith only [hL]
  have hL1 : 1 ≤ lemma23PaperL D := by linarith only [hL]
  have hpow : 1 ≤ lemma23PaperL D ^ 68 := one_le_pow₀ hL1
  have hinv : lemma23PaperL D ^ (-68 : ℤ) ≤ 1 := by
    rw [zpow_neg, zpow_ofNat]
    exact inv_le_one_of_one_le₀ hpow
  have hP : 0 < lemma23PaperP D := Real.exp_pos _
  nlinarith only [hψ.2.2.2.le, mul_le_mul_of_nonneg_left hinv hP.le]

lemma lemma59_family_large_disk_log_budget {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hL : 100 ≤ lemma23PaperL D)
    (hψ : Lemma23InPsi (D := D) ψ) {t : ℝ}
    (ht : |t - (lemma23PaperCenter D).im| ≤ lemma23PaperL D ^ 405 + 20) :
    Real.log (32 * (p : ℝ) * (4 + |t|)) ≤ 2 * lemma23PaperL D ^ 9 := by
  let L := lemma23PaperL D
  have hLp : 0 < L := by dsimp [L]; linarith only [hL]
  have hL1 : 1 ≤ L := by dsimp [L]; linarith only [hL]
  have hp1 : L ≤ L ^ 519 := by simpa only [pow_one] using pow_le_pow_right₀ hL1 (by norm_num : (1 : ℕ) ≤ 519)
  have hp4 : 4 ≤ L ^ 519 := by dsimp [L] at hp1; linarith only [hp1,hL]
  have ht' := lemma59_large_height_bound hL ht
  have hmod := lemma59_family_modulus_le_two_P ψ hL hψ
  have hPpos : 0 < lemma23PaperP D := Real.exp_pos _
  have hbound : 32 * (p : ℝ) * (4 + |t|) ≤ 704 * lemma23PaperP D * L ^ 519 := by
    calc
      _ ≤ (32 * (2 * lemma23PaperP D)) * (11 * L ^ 519) := by
        have hh : 4 + |t| ≤ 11 * L ^ 519 := by dsimp [L]; linarith only [ht', hp4]
        gcongr <;> positivity
      _ = _ := by ring
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hlog := Real.log_le_log (by positivity : 0 < 32 * (p : ℝ) * (4 + |t|)) hbound
  have he : Real.log (704 * lemma23PaperP D * L ^ 519) =
      Real.log 704 + L ^ 9 + 519 * Real.log L := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) hPpos.ne',
      Real.log_pow, lemma23PaperP, Real.log_exp]
    norm_num [L]
  rw [he] at hlog
  have hconst : Real.log (704 : ℝ) ≤ 704 := Real.log_le_self (by norm_num)
  have hlogL : Real.log L ≤ L := Real.log_le_self hLp.le
  have hL2 : 100 ≤ L ^ 2 := by dsimp [L]; nlinarith only [hL]
  have hL3 : 10000 * L ≤ L ^ 3 := by
    have hh : (100 : ℝ) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (by norm_num) (by dsimp [L]; exact hL) 2
    nlinarith only [mul_le_mul_of_nonneg_right hh hLp.le]
  have hL9 : L ^ 3 ≤ L ^ 9 := pow_le_pow_right₀ hL1 (by norm_num)
  change _ ≤ 2 * L ^ 9
  change Real.log (32 * (p : ℝ) * (4 + |t|)) ≤ Real.log 704 + L ^ 9 + 519 * Real.log L at hlog
  have hlarge : 100 ≤ L := hL
  linarith only [hlog, hconst, hlogL, hL3, hL9, hlarge]

lemma lemma59_family_character_nonprincipal {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : Lemma23InPsi (D := D) ψ) : ψ ≠ 1 := by
  intro he
  have hh := hψ.2.1
  rw [he, DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_one] at hh
  exact hψ.1.ne_one hh.symm

lemma lemma59_uniform_actual_local_zero_bound :
    ∃ D₀ : ℕ, ∀ {D p : ℕ} [NeZero p] (χ : RealPrimitiveCharacter D)
      (ψ : DirichletCharacter ℂ p), D₀ ≤ D → Lemma23InPsi1 χ ψ →
      ∀ {t : ℝ}, |t - (lemma23PaperCenter D).im| ≤ lemma23PaperL D ^ 405 + 20 →
        (lemma59JensenMultiplicityCount ψ t : ℝ) ≤ 30 * lemma23PaperL D ^ 9 ∧
        ((lemma59LocalZeroFinset ψ t).card : ℝ) ≤ 30 * lemma23PaperL D ^ 9 := by
  refine ⟨lemma23SectionFourModulusThreshold, ?_⟩
  intro D p _ χ ψ hD hψ t ht
  have hparam := lemma23_sectionFour_parameters_at_explicit_threshold hD
  have hL : 100 ≤ lemma23PaperL D := by
    have hh := Real.log_le_self (by linarith only [hparam.1] : 0 ≤ lemma23PaperL D)
    linarith only [hh,hparam.2]
  have hne := lemma59_family_character_nonprincipal ψ hψ.1
  have hlog := lemma59_family_large_disk_log_budget ψ hL hψ.1 ht
  have hJ := lemma59_actual_large_disk_multiplicity_bound ψ hne t
  have hc := lemma59_actual_local_zero_card_bound ψ hne t
  constructor <;> nlinarith only [hJ, hc, hlog]

end ZhangLS.Spec
