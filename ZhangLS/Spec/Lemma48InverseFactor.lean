import ZhangLS.Spec.Lemma48ZeroRegion

/-! # Lemma 4.8: the inverse functional-equation factor at actual zeros

Multiplying the genuine approximate functional equation by `Z̃⁻¹ G`
produces the desired error. The additional `FG - 1` term is controlled by
Lemma 4.2. All region and inverse-factor bounds follow from the original
Ω and actual product-zero hypotheses.
-/

namespace ZhangLS.Spec

open Complex

set_option maxHeartbeats 1000000

noncomputable def lemma48ErrorConstant : ℝ :=
  Real.exp 3 * (4 + 2 * lemma44ErrorConstant)

theorem lemma48_error_constant_pos : 0 < lemma48ErrorConstant := by
  unfold lemma48ErrorConstant
  exact mul_pos (Real.exp_pos _) (by linarith [lemma44_error_constant_pos])

/-- A closed numerical bound for the absolute error constant. -/
theorem lemma48_error_constant_le : lemma48ErrorConstant ≤ (3 : ℝ) ^ 65 := by
  have he : Real.exp 3 ≤ (3 : ℝ) ^ 3 := by
    calc
      Real.exp 3 = (Real.exp 1) ^ 3 := by
        simpa only [Nat.cast_ofNat, mul_one] using Real.exp_nat_mul 1 3
      _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 3
  have hc := lemma45_error_constant_le
  unfold lemma48ErrorConstant
  have hm := mul_le_mul he (show 4 + 2 * lemma44ErrorConstant ≤ 4 + 2 * (3 : ℝ) ^ 60 by
    linarith) (by linarith [lemma44_error_constant_pos]) (by positivity)
  exact hm.trans (by norm_num)

/-- Lemma 4.8 with an explicit absolute error constant and the existing
computable threshold `3^(3^200)`. No critical-line, region-containment,
inverse-factor or approximation conclusion is assumed. -/
theorem lemma48_actual_inverse_factor_approximation {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    {ρ : ℂ} (hρ : Lemma48InOmega D ρ) (hzero : lemma48ActualProduct χ ψ ρ = 0) :
    ‖(lemma44ActualZtilde χ ψ ρ)⁻¹ +
      lemma23ActualSectionFourG χ (fun n => ψ (n : ZMod p)) ρ *
        lemma23ActualSectionFourF χ (fun n => ψ⁻¹ (n : ZMod p)) (1 - ρ)‖ ≤
      lemma48ErrorConstant * lemma23PaperL D ^ (-100 : ℤ) := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  let L := lemma23PaperL D
  let F := lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p)) ρ
  let G := lemma23ActualSectionFourG χ (fun n => ψ (n : ZMod p)) ρ
  let Fr := lemma23ActualSectionFourF χ (fun n => ψ⁻¹ (n : ZMod p)) (1 - ρ)
  let Z := lemma44ActualZtilde χ ψ ρ
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have hLp : 0 < L := by dsimp [L]; linarith
  have hL1 : 1 ≤ L := by dsimp [L]; linarith
  have hr := lemma48_thin_slab_regions hD hρ
    (lemma48_actual_zero_in_thin_slab χ ψ hD hψ hρ hzero)
  have hZne : Z ≠ 0 := lemma44ActualZtilde_ne_zero χ ψ hL hψ.1
    (lemma48_omega_height_pos hL hρ)
  have hZi := lemma48_actual_Z_inv_bound χ ψ hD hψ hρ hzero
  change ‖Z⁻¹‖ ≤ Real.exp 3 at hZi
  have h41 := lemma23_lemma41 χ ψ ρ hL hψ hr.2.1
  have hG : ‖G‖ ≤ 2 * L ^ 79 := by
    change ‖F‖ + ‖G‖ ≤ 2 * L ^ 79 at h41
    linarith [norm_nonneg F]
  have h42 := lemma23_lemma42 χ ψ ρ hL hψ hr.2.1
  have hFG : ‖1 - F * G‖ ≤ 4 * L ^ (-227 : ℤ) := by
    rw [norm_sub_rev]
    exact h42
  have h44 := lemma44_actual_approximate_functional_equation χ ψ hD hψ hr.1
  change ‖lemma48ActualProduct χ ψ ρ - (F + Z * Fr)‖ ≤
    lemma44ErrorConstant * L ^ (-179 : ℤ) at h44
  rw [hzero, zero_sub, norm_neg] at h44
  have hid : Z⁻¹ + G * Fr =
      Z⁻¹ * (1 - F * G) + Z⁻¹ * G * (F + Z * Fr) := by
    field_simp
    ring
  have hfirst : ‖Z⁻¹ * (1 - F * G)‖ ≤
      Real.exp 3 * (4 * L ^ (-227 : ℤ)) := by
    rw [norm_mul]
    exact mul_le_mul hZi hFG (norm_nonneg _) (Real.exp_nonneg _)
  have hsecond : ‖Z⁻¹ * G * (F + Z * Fr)‖ ≤
      Real.exp 3 * (2 * L ^ 79) * (lemma44ErrorConstant * L ^ (-179 : ℤ)) := by
    simp only [norm_mul]
    apply mul_le_mul
      (mul_le_mul hZi hG (norm_nonneg _) (Real.exp_nonneg _)) h44
      (norm_nonneg _) (by positivity)
  have hpow : L ^ 79 * L ^ (-179 : ℤ) = L ^ (-100 : ℤ) := by
    rw [← zpow_natCast, ← zpow_add₀ hLp.ne']
    norm_num
  have hpowle : L ^ (-227 : ℤ) ≤ L ^ (-100 : ℤ) :=
    zpow_le_zpow_right₀ hL1 (by norm_num)
  change ‖Z⁻¹ + G * Fr‖ ≤ _
  rw [hid]
  calc
    _ ≤ ‖Z⁻¹ * (1 - F * G)‖ + ‖Z⁻¹ * G * (F + Z * Fr)‖ := norm_add_le _ _
    _ ≤ Real.exp 3 * (4 * L ^ (-227 : ℤ)) +
        Real.exp 3 * (2 * L ^ 79) * (lemma44ErrorConstant * L ^ (-179 : ℤ)) :=
      add_le_add hfirst hsecond
    _ ≤ Real.exp 3 * (4 * L ^ (-100 : ℤ)) +
        Real.exp 3 * (2 * L ^ 79) * (lemma44ErrorConstant * L ^ (-179 : ℤ)) := by
      gcongr
    _ = lemma48ErrorConstant * L ^ (-100 : ℤ) := by
      dsimp only [lemma48ErrorConstant]
      calc
        _ = Real.exp 3 * 4 * L ^ (-100 : ℤ) +
            Real.exp 3 * 2 * lemma44ErrorConstant * (L ^ 79 * L ^ (-179 : ℤ)) := by ring
        _ = _ := by rw [hpow]; ring

/-- The original conclusion at closed explicit constant and threshold. -/
theorem lemma48_at_explicit_constant {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    {ρ : ℂ} (hρ : Lemma48InOmega D ρ) (hzero : lemma48ActualProduct χ ψ ρ = 0) :
    ‖(lemma44ActualZtilde χ ψ ρ)⁻¹ +
      lemma23ActualSectionFourG χ (fun n => ψ (n : ZMod p)) ρ *
        lemma23ActualSectionFourF χ (fun n => ψ⁻¹ (n : ZMod p)) (1 - ρ)‖ ≤
      (3 : ℝ) ^ 65 * lemma23PaperL D ^ (-100 : ℤ) := by
  exact (lemma48_actual_inverse_factor_approximation χ ψ hD hψ hρ hzero).trans
    (mul_le_mul_of_nonneg_right lemma48_error_constant_le (by positivity))

/-- The original Lemma 4.8: one absolute constant and one modulus threshold
are selected before all characters and all actual product zeros in Ω. -/
def Lemma48Target : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℕ, ∀ {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p),
    D₀ ≤ D → Lemma23InPsi1 χ ψ → ∀ ρ : ℂ,
    Lemma48InOmega D ρ → lemma48ActualProduct χ ψ ρ = 0 →
    ‖(lemma44ActualZtilde χ ψ ρ)⁻¹ +
      lemma23ActualSectionFourG χ (fun n => ψ (n : ZMod p)) ρ *
        lemma23ActualSectionFourF χ (fun n => ψ⁻¹ (n : ZMod p)) (1 - ρ)‖ ≤
      C * lemma23PaperL D ^ (-100 : ℤ)

theorem lemma48_proved : Lemma48Target := by
  refine ⟨(3 : ℝ) ^ 65, by positivity,
    lemma23SectionFourModulusThreshold, ?_⟩
  intro D p hp χ ψ hD hψ ρ hρ hzero
  exact lemma48_at_explicit_constant χ ψ hD hψ hρ hzero

end ZhangLS.Spec
