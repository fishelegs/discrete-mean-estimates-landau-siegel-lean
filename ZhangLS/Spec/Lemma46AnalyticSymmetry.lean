import ZhangLS.Spec.Lemma46LocalGeometry
import ZhangLS.Spec.Lemma23DirichletConjugation

/-! # Analyticity and reflected zeros of the genuine normalized product -/

namespace ZhangLS.Spec

open Complex ComplexConjugate Metric Set

set_option maxHeartbeats 1000000

theorem lemma46_LFunction_analyticAt {N : ℕ} [NeZero N]
    (ψ : DirichletCharacter ℂ N) {s : ℂ} (hs : s ≠ 1) :
    AnalyticAt ℂ (DirichletCharacter.LFunction ψ) s := by
  have hd : DifferentiableOn ℂ (DirichletCharacter.LFunction ψ) {1}ᶜ := by
    intro z hz
    exact (DirichletCharacter.differentiableAt_LFunction ψ z
      (Or.inl (by simpa using hz))).differentiableWithinAt
  exact hd.analyticAt (isOpen_compl_singleton.mem_nhds (by simpa using hs))

theorem lemma46_actual_A_analyticAt {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    {s : ℂ} (hs : s ≠ 1)
    (hF : lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p)) s ≠ 0) :
    AnalyticAt ℂ (lemma45ActualA χ ψ) s := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  have hf : AnalyticAt ℂ (lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p))) s :=
    (lemma44_short_polynomial_differentiable χ ψ).analyticAt s
  exact ((lemma46_LFunction_analyticAt ψ hs).mul
    (lemma46_LFunction_analyticAt (lemma44CharacterTwist χ ψ) hs)).div hf hF

theorem lemma46_actual_A_analyticOn_inner_disk {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    {c : ℂ} (hc : c.re = 1 / 2)
    (hci : |c.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 2)
    {R : ℝ} (hR : R < lemma44PaperAlpha D) :
    AnalyticOnNhd ℂ (fun w => lemma45ActualA χ ψ (c + w)) (closedBall 0 R) := by
  intro w hw
  have hnorm : ‖w‖ < lemma44PaperAlpha D :=
    lt_of_le_of_lt (by simpa [mem_closedBall, dist_zero_right] using hw) hR
  have hs : ‖c + w - c‖ < lemma44PaperAlpha D := by simpa using hnorm
  have hr := lemma46_inner_disk_regions hD hc hci hs
  have hL := (lemma23_sectionFour_parameters_at_explicit_threshold hD).1
  have hF := lemma23_omega1_F_ne_zero χ ψ (c + w) hL hψ.2 hr.2
  have hstrip := lemma46_disk_subset_local_strip hD hc hci
    (by linarith [ (lemma46_alpha_parameters hD).1] : ‖c + w - c‖ < 2 * lemma44PaperAlpha D)
  have him := (lemma46_local_strip_regions hD hstrip).2.2.2
  have hne : c + w ≠ 1 := by
    intro he
    rw [he] at him
    norm_num at him
  exact (lemma46_actual_A_analyticAt χ ψ hne hF).comp (by fun_prop)

theorem lemma46_actual_A_reflected_zero {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    {s : ℂ} (hs : Lemma46InLocalStrip D s)
    (hzero : lemma45ActualA χ ψ s = 0) :
    lemma45ActualA χ ψ (1 - conj s) = 0 := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  have hp := lemma23_sectionFour_parameters_at_explicit_threshold hD
  have hr := lemma46_local_strip_regions hD hs
  have hR : 0 < lemma23LogDerivativeRadius D := by
    unfold lemma23LogDerivativeRadius
    exact div_pos (by linarith only [hp.2]) (by linarith only [hp.1])
  have hF := lemma23_omega1_F_ne_zero χ ψ s hp.1 hψ.2
    (lemma23_omega2_disk_subset_omega1 hp.1 hp.2 hr.1 (mem_ball_self hR))
  have hprod : DirichletCharacter.LFunction ψ s *
      DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) s = 0 := by
    change _ / lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p)) s = 0 at hzero
    exact (div_eq_zero_iff).mp hzero |>.resolve_right hF
  have hfe := lemma44_equation44 χ ψ hp.1 hψ.1 hr.2.2.2
  rw [hprod] at hfe
  have hZ := lemma44ActualZtilde_ne_zero χ ψ hp.1 hψ.1 hr.2.2.2
  have hbar := (mul_eq_zero.mp hfe.symm).resolve_left hZ
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
    have hdvp : p ∣ 1 := htwist ▸ Nat.dvd_mul_left p D
    exact hψ.1.1.ne_one (Nat.dvd_one.mp hdvp)
  rw [dirichletLFunction_inv_eq_conj_at_conj ψ hψne,
    dirichletLFunction_inv_eq_conj_at_conj (lemma44CharacterTwist χ ψ) htwne,
    ← map_mul, map_sub, map_one] at hbar
  have hz : DirichletCharacter.LFunction ψ (1 - conj s) *
      DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) (1 - conj s) = 0 :=
    (map_eq_zero conj).mp hbar
  simp only [lemma45ActualA, hz, zero_div]

end ZhangLS.Spec
