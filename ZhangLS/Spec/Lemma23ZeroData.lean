import ZhangLS.Spec.Lemma23ZeroIntervals

/-! # Uniform actual zero data for Lemma 2.3

One constant is selected before the character family. It satisfies the
strict Proposition 2.2 gap bound and defines all three paper offsets.
The derivative and interval hypotheses needed by the sign theorem are
derived from actual smaller-window L-function zeros.
-/

namespace ZhangLS.Spec

open Complex Set

set_option maxHeartbeats 1000000

noncomputable def lemma23PaperOffsetOne (D : ℕ) (c : ℝ) : ℝ :=
  lemma44PaperAlpha D * (1 - 5 * c * lemma44PaperAlpha D * lemma23PaperL D)

noncomputable def lemma23PaperOffsetTwo (D : ℕ) (c : ℝ) : ℝ :=
  2 * lemma44PaperAlpha D * (1 + c * lemma44PaperAlpha D * lemma23PaperL D)

noncomputable def lemma23PaperOffsetThree (D : ℕ) (c : ℝ) : ℝ :=
  3 * lemma44PaperAlpha D * (1 - c * lemma44PaperAlpha D * lemma23PaperL D)

/-- All sign-theorem inputs are conclusions about the actual L-function. -/
structure Lemma23ZeroDataAt {p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (D : ℕ) (c : ℝ) (ρ : ℂ) : Prop where
  critical : ρ.re = 1 / 2
  positive_height : 0 < ρ.im
  simple : deriv (DirichletCharacter.LFunction ψ) ρ ≠ 0
  offset_order : 0 < lemma23PaperOffsetOne D c ∧
    lemma23PaperOffsetOne D c ≤ lemma23PaperOffsetTwo D c ∧
    lemma23PaperOffsetTwo D c ≤ lemma23PaperOffsetThree D c
  first_interval : ∀ ⦃x : ℝ⦄, 0 < x → x ≤ lemma23PaperOffsetOne D c →
    DirichletCharacter.LFunction ψ (criticalLinePoint ρ x) ≠ 0
  third_interval : ∀ x ∈ Icc (lemma23PaperOffsetTwo D c) (lemma23PaperOffsetThree D c),
    DirichletCharacter.LFunction ψ (criticalLinePoint ρ x) ≠ 0

theorem lemma23_exists_uniform_actual_zero_data :
    ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℕ, ∀ {D p : ℕ} [NeZero p]
      (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p),
      D₀ ≤ D → Lemma23InPsi1 χ ψ →
      (∀ ρ ρ' : ℂ, Proposition22ConsecutiveZeros χ ψ ρ ρ' →
        |ρ'.im - ρ.im - lemma44PaperAlpha D| <
          C * lemma44PaperAlpha D ^ 2 * lemma23PaperL D) ∧
      (∀ ρ : ℂ, Lemma23InZeroWindow D ρ → DirichletCharacter.LFunction ψ ρ = 0 →
        Lemma23ZeroDataAt ψ D C ρ) := by
  obtain ⟨m, hm, hmodel⟩ := lemma46_model_uniform_inner_boundary
  let c := (lemma46ModelErrorConstant + 1) / m
  have hc : 0 < c := div_pos (by linarith [lemma46_model_error_constant_pos]) hm
  have hcmp : lemma46ModelErrorConstant < m * c := by
    dsimp [c]
    rw [mul_div_cancel₀ _ hm.ne']
    linarith
  obtain ⟨n, hn, hnmodel⟩ := proposition22_model_uniform_near_zero
  let k := (lemma47ModelErrorConstant + 1) / n
  have hk : 0 < k := div_pos (by linarith [lemma47_model_error_constant_pos]) hn
  have hkcmp : lemma47ModelErrorConstant < n * k := by
    dsimp [k]
    rw [mul_div_cancel₀ _ hn.ne']
    linarith
  let C := c + k + 1
  have hC : 0 < C := by dsimp [C]; linarith
  obtain ⟨D₀, hD₀, hsmall⟩ := lemma46_exists_contraction_threshold
    (c := 16 * C) (by positivity)
  refine ⟨C, hC, D₀, ?_⟩
  intro D p hp χ ψ hD hψ
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  have hsection := hD₀.trans hD
  have ha := (lemma46_alpha_parameters hsection).1
  have hL : 0 < lemma23PaperL D := by
    linarith [(lemma45_parameters_at_threshold hsection).1]
  have hCsmall : C * lemma44PaperAlpha D * lemma23PaperL D ≤ 1 / 32 := by
    nlinarith only [hsmall D hD]
  have hcC : c ≤ C := by dsimp [C]; linarith
  have hkC : k ≤ C := by dsimp [C]; linarith
  have hsmallc : c * lemma44PaperAlpha D * lemma23PaperL D ≤ 1 / 4 := by
    have hh := mul_le_mul_of_nonneg_right hcC (mul_nonneg ha.le hL.le)
    nlinarith only [hh, hCsmall]
  have hsmallk : k * lemma44PaperAlpha D * lemma23PaperL D ≤ 1 / 4 := by
    have hh := mul_le_mul_of_nonneg_right hkC (mul_nonneg ha.le hL.le)
    nlinarith only [hh, hCsmall]
  have hlocal := fun ρ hρ hz => proposition22_actual_zero_analysis hm hc hcmp hmodel
    χ ψ hsection hψ (by linarith : c * lemma44PaperAlpha D * lemma23PaperL D ≤ 1 / 2)
    (ρ := ρ) hρ hz
  have hgap : ∀ ρ ρ' : ℂ, Proposition22ConsecutiveZeros χ ψ ρ ρ' →
      |ρ'.im - ρ.im - lemma44PaperAlpha D| <
        C * lemma44PaperAlpha D ^ 2 * lemma23PaperL D := by
    intro ρ ρ' hcon
    have hb := proposition22_consecutive_gap_bounds hk hkcmp hnmodel χ ψ hsection hψ
      (by linarith : k * lemma44PaperAlpha D * lemma23PaperL D ≤ 1 / 2) hlocal hcon
    have hweight : 0 < lemma44PaperAlpha D ^ 2 * lemma23PaperL D := by positivity
    unfold lemma46InnerRadius at hb
    apply abs_lt.mpr
    dsimp [C]
    constructor <;> nlinarith only [hb.1, hb.2, hweight,
      mul_pos hc hweight, mul_pos hk hweight]
  refine ⟨hgap, ?_⟩
  intro ρ hρ hzero
  have hρΩ := lemma23_zero_window_subset_omega hρ
  have hz : lemma48ActualProduct χ ψ ρ = 0 := by
    change DirichletCharacter.LFunction ψ ρ * _ = 0
    rw [hzero, zero_mul]
  have hl := hlocal ρ hρΩ hz
  have hρne : ρ ≠ 1 := by intro he; rw [he] at hl; norm_num at hl
  have hsimple : deriv (DirichletCharacter.LFunction ψ) ρ ≠ 0 := by
    have hdψ := (lemma46_LFunction_analyticAt ψ hρne).differentiableAt
    have hdχψ := (lemma46_LFunction_analyticAt (lemma44CharacterTwist χ ψ) hρne).differentiableAt
    have hpderiv : deriv (lemma48ActualProduct χ ψ) ρ =
        deriv (DirichletCharacter.LFunction ψ) ρ *
          DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) ρ +
        DirichletCharacter.LFunction ψ ρ *
          deriv (DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ)) ρ :=
      deriv_mul hdψ hdχψ
    intro hd
    apply hl.2.1
    rw [hpderiv, hd, hzero]
    simp
  have hsuccessor := fun ζ hre him hζzero => lemma23_actual_successor hk hkcmp hnmodel
    χ ψ hsection hψ hsmallc hsmallk hlocal (ρ := ζ) hre him hζzero
  obtain ⟨ρ₁, ρ₂, ρ₃, h₁, h₂, h₃⟩ := lemma23_actual_three_successors χ ψ
    (lemma46_alpha_parameters hsection).2.1 hsuccessor
    (fun ζ hΩ hζzero => (hlocal ζ hΩ hζzero).1) hρ hl.1 hz
  let δ := C * lemma44PaperAlpha D * lemma23PaperL D
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hδlt : δ < 1 / 5 := by dsimp [δ]; linarith
  have hg₁ : |ρ₁.im - ρ.im - lemma44PaperAlpha D| < lemma44PaperAlpha D * δ := by
    have hh := hgap ρ ρ₁ h₁
    dsimp [δ]
    nlinarith only [hh]
  have hg₂ : |ρ₂.im - ρ₁.im - lemma44PaperAlpha D| < lemma44PaperAlpha D * δ := by
    have hh := hgap ρ₁ ρ₂ h₂
    dsimp [δ]
    nlinarith only [hh]
  have hg₃ : |ρ₃.im - ρ₂.im - lemma44PaperAlpha D| < lemma44PaperAlpha D * δ := by
    have hh := hgap ρ₂ ρ₃ h₃
    dsimp [δ]
    nlinarith only [hh]
  have hb₁ := abs_lt.mp hg₁
  have hb₂ := abs_lt.mp hg₂
  have hb₃ := abs_lt.mp hg₃
  have hi := lemma23_paper_offset_gap_interleaving
    (g₁ := ρ₁.im - ρ.im) (g₂ := ρ₂.im - ρ₁.im) (g₃ := ρ₃.im - ρ₂.im) ha hδ hδlt
    (by nlinarith only [hb₁.1]) (by nlinarith only [hb₁.2])
    (by nlinarith only [hb₂.1]) (by nlinarith only [hb₂.2])
    (by nlinarith only [hb₃.1])
  have hnz := lemma23_actual_offset_nonzero_of_successors χ ψ hl.1 h₁ h₂ h₃
    ha hδ hδlt hg₁ hg₂ hg₃
  have hb₁eq : lemma23PaperOffsetOne D C = lemma44PaperAlpha D * (1 - 5 * δ) := by
    dsimp [lemma23PaperOffsetOne, δ]
    ring
  have hb₂eq : lemma23PaperOffsetTwo D C = 2 * lemma44PaperAlpha D * (1 + δ) := rfl
  have hb₃eq : lemma23PaperOffsetThree D C = 3 * lemma44PaperAlpha D * (1 - δ) := rfl
  refine ⟨hl.1, lemma48_omega_height_pos
    (lemma44_parameters_at_explicit_threshold hsection).1 hρΩ, hsimple, ?_, ?_, ?_⟩
  · rw [hb₁eq, hb₂eq, hb₃eq]
    exact ⟨hi.1, hi.2.1.le, hi.2.2.2.2.1.le⟩
  · rw [hb₁eq]
    exact hnz.1
  · rw [hb₂eq, hb₃eq]
    exact hnz.2

end ZhangLS.Spec
