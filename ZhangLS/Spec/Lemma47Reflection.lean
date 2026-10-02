import ZhangLS.Spec.Lemma46ZeroAnalysis

/-! # Reflection identities for the expanded disk in Lemma 4.7

The expanded circle crosses the left edge of `Ω₃`. The genuine functional
equation transports the normalized error from the reflected right half.
-/

namespace ZhangLS.Spec

open Complex ComplexConjugate Metric Set

set_option maxHeartbeats 2000000

theorem lemma47_dirichletZ_reflection {N : ℕ} [NeZero N]
    (ψ : DirichletCharacter ℂ N) (hψ : ψ.IsPrimitive) (hN : N ≠ 1)
    {s : ℂ} (hs : s.im ≠ 0) :
    lemma23DirichletZ ψ s * conj (lemma23DirichletZ ψ (1 - conj s)) = 1 := by
  have hγ := lemma23_gammaFactor_ne_zero_of_im_ne_zero ψ hs
  have hγi := lemma23_gammaFactor_ne_zero_of_im_ne_zero ψ⁻¹
    (by simpa using neg_ne_zero.mpr hs : (1 - s).im ≠ 0)
  have hγ₁ : conj (DirichletCharacter.gammaFactor ψ⁻¹
      (1 - (1 - conj s))) = DirichletCharacter.gammaFactor ψ s := by
    rw [show 1 - (1 - conj s) = conj s by ring, lemma23_gammaFactor_inv_conj]
    simp
  have hγ₂ : conj (DirichletCharacter.gammaFactor ψ (1 - conj s)) =
      DirichletCharacter.gammaFactor ψ⁻¹ (1 - s) := by
    rw [show 1 - conj s = conj (1 - s) by simp,
      ← inv_inv ψ, lemma23_gammaFactor_inv_conj]
    simp
  have harg : (N : ℂ).arg ≠ Real.pi := by
    change ((N : ℝ) : ℂ).arg ≠ Real.pi
    rw [arg_ofReal_of_nonneg (Nat.cast_nonneg N)]
    exact Real.pi_ne_zero.symm
  have hpow : conj ((N : ℂ) ^ ((1 / 2 : ℂ) - (1 - conj s))) =
      (N : ℂ) ^ (s - 1 / 2) := by
    have hh := cpow_conj (N : ℂ) ((1 / 2 : ℂ) - (1 - conj s)) harg
    simp only [map_natCast] at hh
    rw [← hh]
    congr 1
    simp only [map_sub, map_div₀, map_one, map_ofNat, conj_conj]
    ring
  have hn : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hp : (N : ℂ) ^ ((1 / 2 : ℂ) - s) * (N : ℂ) ^ (s - 1 / 2) = 1 := by
    rw [← cpow_add _ _ hn, show (1 / 2 : ℂ) - s + (s - 1 / 2) = 0 by ring,
      cpow_zero]
  have hr : DirichletCharacter.rootNumber ψ * conj (DirichletCharacter.rootNumber ψ) = 1 := by
    rw [mul_conj, normSq_eq_norm_sq, lemma23_rootNumber_norm_eq_one ψ hψ hN]
    norm_num
  unfold lemma23DirichletZ
  rw [map_mul, map_mul, map_div₀, hpow, hγ₁, hγ₂]
  calc
    _ = ((N : ℂ) ^ ((1 / 2 : ℂ) - s) * (N : ℂ) ^ (s - 1 / 2)) *
        (DirichletCharacter.rootNumber ψ * conj (DirichletCharacter.rootNumber ψ)) *
        ((DirichletCharacter.gammaFactor ψ⁻¹ (1 - s) / DirichletCharacter.gammaFactor ψ s) *
          (DirichletCharacter.gammaFactor ψ s / DirichletCharacter.gammaFactor ψ⁻¹ (1 - s))) := by ring
    _ = 1 := by rw [hp, hr]; field_simp

theorem lemma47_actual_Z_reflection {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hL : 3 ≤ lemma23PaperL D) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hs : s.im ≠ 0) :
    lemma44ActualZtilde χ ψ s * conj (lemma44ActualZtilde χ ψ (1 - conj s)) = 1 := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  have hpne := hψ.1.ne_one
  have hDpne : D * p ≠ 1 := by
    intro h
    exact hpne (Nat.dvd_one.mp (h ▸ Nat.dvd_mul_left p D))
  have htwist := lemma44CharacterTwist_isPrimitive χ ψ hψ.2.1
    (lemma44_family_coprime χ ψ hL hψ)
  have h₁ := lemma47_dirichletZ_reflection ψ hψ.2.1 hpne hs
  have h₂ := lemma47_dirichletZ_reflection (lemma44CharacterTwist χ ψ) htwist hDpne hs
  simp only [lemma44ActualZtilde, lemma44ProductZ, map_mul]
  calc
    _ = (lemma23DirichletZ ψ s * conj (lemma23DirichletZ ψ (1 - conj s))) *
        (lemma23DirichletZ (lemma44CharacterTwist χ ψ) s *
          conj (lemma23DirichletZ (lemma44CharacterTwist χ ψ) (1 - conj s))) := by ring
    _ = 1 := by rw [h₁, h₂, mul_one]

theorem lemma47_actual_normalized_reflection {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    {s : ℂ} (hs : Lemma46InLocalStrip D s) :
    lemma45ActualA χ ψ s = lemma45ActualB χ ψ s *
      conj (lemma45ActualA χ ψ (1 - conj s)) ∧
    lemma45ActualB χ ψ s * conj (lemma45ActualB χ ψ (1 - conj s)) = 1 := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  have hp := lemma23_sectionFour_parameters_at_explicit_threshold hD
  have hr := lemma46_local_strip_regions hD hs
  have hR : 0 < lemma23LogDerivativeRadius D := by
    unfold lemma23LogDerivativeRadius
    exact div_pos (by linarith only [hp.2]) (by linarith only [hp.1])
  have hF := lemma23_omega1_F_ne_zero χ ψ s hp.1 hψ.2
    (lemma23_omega2_disk_subset_omega1 hp.1 hp.2 hr.1 (mem_ball_self hR))
  have hFr := lemma23_omega1_F_ne_zero χ ψ (conj (1 - s)) hp.1 hψ.2
    (lemma23_omega2_disk_subset_omega1 hp.1 hp.2 hr.2.1 (mem_ball_self hR))
  have hFir : lemma23ActualSectionFourF χ (fun n => ψ⁻¹ (n : ZMod p)) (1 - s) ≠ 0 := by
    rw [lemma45_short_sum_inv_eq_conj]
    exact (map_ne_zero conj).2 hFr
  have hψne : ψ ≠ 1 := by
    intro he
    have hh := hψ.1.2.1
    rw [he, DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_one] at hh
    exact hψ.1.1.ne_one hh.symm
  have htwist := lemma44CharacterTwist_isPrimitive χ ψ hψ.1.2.1
    (lemma44_family_coprime χ ψ hp.1 hψ.1)
  have htwne : lemma44CharacterTwist χ ψ ≠ 1 := by
    intro he
    rw [he, DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_one] at htwist
    exact hψ.1.1.ne_one (Nat.dvd_one.mp (htwist ▸ Nat.dvd_mul_left p D))
  have hfe := lemma44_equation44 χ ψ hp.1 hψ.1 hr.2.2.2
  rw [dirichletLFunction_inv_eq_conj_at_conj ψ hψne,
    dirichletLFunction_inv_eq_conj_at_conj (lemma44CharacterTwist χ ψ) htwne] at hfe
  have hZ := lemma47_actual_Z_reflection χ ψ hp.1 hψ.1 hr.2.2.2.ne'
  have hconj : conj (1 - s) = 1 - conj s := by simp
  have hFc : conj (lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p))
      (1 - conj s)) = lemma23ActualSectionFourF χ (fun n => ψ⁻¹ (n : ZMod p)) (1 - s) := by
    rw [lemma45_short_sum_inv_eq_conj, hconj]
  have hFc₂ : conj (lemma23ActualSectionFourF χ (fun n => ψ⁻¹ (n : ZMod p))
      (conj s)) = lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p)) s := by
    rw [lemma45_short_sum_inv_eq_conj]
    simp
  constructor
  · unfold lemma45ActualA lemma45ActualB
    simp only [map_div₀, map_mul, hFc]
    rw [hfe, hconj]
    field_simp
  · unfold lemma45ActualB
    simp only [map_div₀, map_mul, sub_sub_cancel, hFc, hFc₂]
    calc
      _ = lemma44ActualZtilde χ ψ s *
          conj (lemma44ActualZtilde χ ψ (1 - conj s)) := by field_simp
      _ = 1 := hZ

end ZhangLS.Spec
