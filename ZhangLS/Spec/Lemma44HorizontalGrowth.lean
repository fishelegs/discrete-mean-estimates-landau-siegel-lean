import ZhangLS.Spec.Lemma44ComplexCharacterAbel
import ZhangLS.Spec.Lemma44InitialLeftEstimates

/-!
# Growth of the actual product on the finite contour

The nontriviality and conductor bounds come from the genuine family. Abel
summation controls the right half-plane; the functional equation controls
the remaining part of the local rectangle. No growth assumption is added.
-/

namespace ZhangLS.Spec

open Complex

set_option maxHeartbeats 1000000

theorem lemma44_log_large_at_threshold {D : ℕ}
    (hD : lemma23SectionFourModulusThreshold ≤ D) : 1000 ≤ lemma23PaperL D := by
  have hp : (3 : ℝ) ^ (3 ^ 200 : ℕ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hlog3 : (1 : ℝ) ≤ Real.log 3 :=
    (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 3)).mpr
      (le_of_lt Real.exp_one_lt_three)
  have hm := Real.log_le_log (by positivity : 0 < (3 : ℝ) ^ (3 ^ 200 : ℕ)) hp
  rw [Real.log_pow] at hm
  have hb : (1000 : ℝ) ≤ ((3 ^ 200 : ℕ) : ℝ) := by norm_num
  have hmul := mul_le_mul_of_nonneg_left hlog3
    (by positivity : (0 : ℝ) ≤ ((3 ^ 200 : ℕ) : ℝ))
  change 1000 ≤ Real.log (D : ℝ)
  linarith

theorem lemma44_horizontal_decay_budget {L : ℝ} (hL : 1000 ≤ L) :
    L ^ 2000 * Real.exp (30 * L ^ 9 + 100 * L - L ^ 10 / 4) ≤ L ^ (-180 : ℤ) := by
  have hL0 : 0 < L := by linarith
  have h9 : 6561 * L ≤ L ^ 9 := by
    have h8 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3)
      (by linarith : 3 ≤ L) 8
    calc
      _ ≤ L ^ 8 * L := by norm_num at h8; nlinarith only [h8, hL0]
      _ = _ := by ring
  have h10 : 1000 * L ^ 9 ≤ L ^ 10 := by
    have h := mul_le_mul_of_nonneg_right hL (pow_nonneg hL0.le 9)
    nlinarith only [h]
  have hlog := Real.log_le_sub_one_of_pos hL0
  have hp : L ^ 2000 = Real.exp (2000 * Real.log L) := by
    simpa [Real.exp_log hL0] using (Real.exp_nat_mul (Real.log L) 2000).symm
  rw [hp, ← Real.exp_add]
  calc
    _ ≤ Real.exp (-180 * Real.log L) :=
      Real.exp_le_exp.mpr (by nlinarith only [h9, h10, hlog, hL0])
    _ = _ := by
      rw [← Real.rpow_intCast, Real.rpow_def_of_pos hL0]
      congr 1
      norm_num
      ring

theorem lemma44_family_characters_nontrivial {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hL : 3 ≤ lemma23PaperL D) (hψ : Lemma23InPsi (D := D) ψ) :
    ψ ≠ 1 ∧ lemma44CharacterTwist χ ψ ≠ 1 := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  constructor
  · intro he
    have hc : ψ.conductor = p := hψ.2.1
    rw [he, DirichletCharacter.conductor_one] at hc
    exact hψ.1.ne_one hc.symm
  · have htw := lemma44CharacterTwist_isPrimitive χ ψ hψ.2.1
      (lemma44_family_coprime χ ψ hL hψ)
    intro he
    have hc : (lemma44CharacterTwist χ ψ).conductor = D * p := htw
    rw [he, DirichletCharacter.conductor_one] at hc
    exact hψ.1.ne_one (Nat.dvd_one.mp (hc.symm ▸ Nat.dvd_mul_left p D))

theorem lemma44_extended_region_norm_bounds {D : ℕ} {z : ℂ}
    (hL : 3 ≤ lemma23PaperL D) (hz : Lemma44InExtendedGammaRegion D z) :
    ‖z‖ ≤ 128 * lemma23PaperL D ^ 519 ∧
      ‖1 - z‖ ≤ 128 * lemma23PaperL D ^ 519 := by
  let L := lemma23PaperL D
  have hL1 : 1 ≤ L := by linarith
  have hpow : L ^ 405 ≤ L ^ 519 := pow_le_pow_right₀ hL1 (by norm_num)
  have hpow1 : 1 ≤ L ^ 519 := one_le_pow₀ hL1
  have hpow3 : 3 ≤ L ^ 519 := hL.trans (le_self_pow₀ hL1 (by norm_num))
  have him : |z.im - 2 * Real.pi * L ^ 519| ≤ 2 * L ^ 405 + 3 := hz.2
  have himhi : z.im ≤ 11 * L ^ 519 := by
    nlinarith [Real.pi_le_four, (abs_le.mp him).2]
  have himpos := (lemma44_extended_gamma_region_height hL hz).2.2.1
  have hre : |z.re| ≤ 101 := by
    have ht := abs_add_le (z.re - 1 / 2) (1 / 2 : ℝ)
    norm_num at ht
    linarith [hz.1]
  have hn : ‖z‖ ≤ 112 * L ^ 519 := by
    have ht := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_pos himpos] at ht
    nlinarith only [hre, himhi, hpow1, ht]
  constructor
  · exact hn.trans (by nlinarith only [hpow1])
  · have ht := norm_sub_le (1 : ℂ) z
    norm_num at ht
    nlinarith only [hn, hpow1, ht]

theorem lemma44_product_halfplane_growth {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hL : 3 ≤ lemma23PaperL D) (hψ : Lemma23InPsi (D := D) ψ)
    (η : DirichletCharacter ℂ p) (hη : η ≠ 1)
    (hηtw : lemma44CharacterTwist χ η ≠ 1)
    {z : ℂ} (hz : 1 / 2 ≤ z.re) (hn : ‖z‖ ≤ 128 * lemma23PaperL D ^ 519) :
    letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    ‖DirichletCharacter.LFunction η z *
      DirichletCharacter.LFunction (lemma44CharacterTwist χ η) z‖ ≤
      262144 * Real.exp (lemma23PaperL D + 2 * lemma23PaperL D ^ 9) *
        lemma23PaperL D ^ 1038 := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  have hz0 : 0 < z.re := by linarith
  have hfirst := lemma44_dirichletLFunction_norm_le_of_pos_re η hη hz0
  have hsecond := lemma44_dirichletLFunction_norm_le_of_pos_re
    (lemma44CharacterTwist χ η) hηtw hz0
  have hdiv1 : (p : ℝ) / z.re ≤ 2 * p := by
    apply (div_le_iff₀ hz0).mpr
    nlinarith [show (0 : ℝ) ≤ p by positivity]
  have hdiv2 : ((D * p : ℕ) : ℝ) / z.re ≤ 2 * (D * p) := by
    push_cast
    apply (div_le_iff₀ hz0).mpr
    nlinarith [show (0 : ℝ) ≤ (D : ℝ) * p by positivity]
  have hf : ‖DirichletCharacter.LFunction η z‖ ≤ 2 * p * ‖z‖ := by
    exact hfirst.trans (by nlinarith [mul_le_mul_of_nonneg_left hdiv1 (norm_nonneg z)])
  have hg : ‖DirichletCharacter.LFunction (lemma44CharacterTwist χ η) z‖ ≤
      2 * (D * p) * ‖z‖ := by
    exact hsecond.trans (by nlinarith [mul_le_mul_of_nonneg_left hdiv2 (norm_nonneg z)])
  have hp : (p : ℝ) ≤ 2 * Real.exp (lemma23PaperL D ^ 9) := by
    have hsmall : lemma23PaperL D ^ (-68 : ℤ) ≤ 1 :=
      zpow_le_one_of_nonpos₀ (by linarith : 1 ≤ lemma23PaperL D) (by norm_num)
    have hu := hψ.2.2.2.le
    change (p : ℝ) ≤ Real.exp (lemma23PaperL D ^ 9) *
      (1 + lemma23PaperL D ^ (-68 : ℤ)) at hu
    change (p : ℝ) ≤ 2 * lemma23PaperP D
    unfold lemma23PaperP
    nlinarith [Real.exp_pos (lemma23PaperL D ^ 9)]
  have hDexp : (D : ℝ) = Real.exp (lemma23PaperL D) := by
    exact (Real.exp_log (by exact_mod_cast χ.modulus_pos)).symm
  rw [norm_mul]
  calc
    _ ≤ (2 * p * ‖z‖) * (2 * (D * p) * ‖z‖) :=
      mul_le_mul hf hg (norm_nonneg _) (by positivity)
    _ ≤ (2 * (2 * Real.exp (lemma23PaperL D ^ 9)) * (128 * lemma23PaperL D ^ 519)) *
        (2 * (Real.exp (lemma23PaperL D) * (2 * Real.exp (lemma23PaperL D ^ 9))) *
          (128 * lemma23PaperL D ^ 519)) := by
      push_cast
      rw [hDexp]
      gcongr
    _ = _ := by
      rw [show lemma23PaperL D ^ 1038 = lemma23PaperL D ^ 519 * lemma23PaperL D ^ 519
        by rw [← pow_add]]
      have he : Real.exp (2 * lemma23PaperL D ^ 9) = Real.exp (lemma23PaperL D ^ 9) ^ 2 := by
        simpa using Real.exp_nat_mul (lemma23PaperL D ^ 9) 2
      rw [Real.exp_add, he]
      ring

theorem lemma44_actual_product_local_growth {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi (D := D) ψ)
    {z : ℂ} (hz : Lemma44InExtendedGammaRegion D z) (hre : -1 / 2 ≤ z.re) :
    letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    ‖DirichletCharacter.LFunction ψ z *
      DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) z‖ ≤
      262144 * Real.exp (4 * lemma23PaperL D + 4 * lemma23PaperL D ^ 9) *
        lemma23PaperL D ^ 1038 := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have hn := lemma44_extended_region_norm_bounds hL hz
  have hne := lemma44_family_characters_nontrivial χ ψ hL hψ
  by_cases hr : 1 / 2 ≤ z.re
  · have hb := lemma44_product_halfplane_growth χ ψ hL hψ ψ hne.1 hne.2 hr hn.1
    apply hb.trans
    have hL0 : 0 ≤ lemma23PaperL D := by linarith
    have hp : 0 ≤ lemma23PaperL D ^ 9 := by positivity
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hL0 1038)
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 262144)
    exact Real.exp_le_exp.mpr (by nlinarith only [hL0, hp])
  · have hmir : 1 / 2 ≤ (1 - z).re := by simp; linarith
    have hinv : ψ⁻¹ ≠ 1 := by simpa using hne.1
    have htw : lemma44CharacterTwist χ ψ⁻¹ ≠ 1 := by
      rw [← lemma44CharacterTwist_inv]
      simpa using hne.2
    have hb := lemma44_product_halfplane_growth χ ψ hL hψ ψ⁻¹ hinv htw hmir hn.2
    have hzbound := lemma44ActualZtilde_norm_le_left χ ψ hD hψ hz (le_of_not_ge hr)
    have hz' : ‖lemma44ActualZtilde χ ψ z‖ ≤
        Real.exp (2 * lemma23PaperL D ^ 9 + 3 * lemma23PaperL D) := by
      apply hzbound.trans
      simp only [lemma23PaperP, Real.log_exp]
      apply Real.exp_le_exp.mpr
      have hL0 : 0 ≤ lemma23PaperL D := by linarith
      have hp : 0 ≤ lemma23PaperL D ^ 9 := by positivity
      nlinarith only [hre, hL0, hp]
    rw [lemma44_equation44 χ ψ hL hψ
      (lemma44_extended_gamma_region_height hL hz).2.2.1,
      mul_assoc, lemma44CharacterTwist_inv, norm_mul]
    calc
      _ ≤ Real.exp (2 * lemma23PaperL D ^ 9 + 3 * lemma23PaperL D) *
          (262144 * Real.exp (lemma23PaperL D + 2 * lemma23PaperL D ^ 9) *
            lemma23PaperL D ^ 1038) :=
        mul_le_mul hz' hb (norm_nonneg _) (Real.exp_nonneg _)
      _ = _ := by
        have he : Real.exp (4 * lemma23PaperL D + 4 * lemma23PaperL D ^ 9) =
            Real.exp (2 * lemma23PaperL D ^ 9 + 3 * lemma23PaperL D) *
              Real.exp (lemma23PaperL D + 2 * lemma23PaperL D ^ 9) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [he]
        ring

end ZhangLS.Spec
