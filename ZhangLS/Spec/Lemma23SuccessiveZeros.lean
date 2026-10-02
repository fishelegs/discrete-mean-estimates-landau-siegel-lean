import ZhangLS.Spec.Proposition22

/-! # Actual consecutive successors in the smaller zero region

The original Lemma 2.3 window has a height margin of two inside Ω.
Rouché supplies upper neighbors; the local exclusion disks rule out
intermediate zeros. Three iterations remain in the original Ω.
-/

namespace ZhangLS.Spec

open Complex Metric Set

set_option maxHeartbeats 1000000

/-- The original smaller window defining the zeros in Lemma 2.3. -/
def Lemma23InZeroWindow (D : ℕ) (ρ : ℂ) : Prop :=
  |ρ.re - 1 / 2| < 1 / 2 ∧
    |ρ.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405

theorem lemma23_zero_window_subset_omega {D : ℕ} {ρ : ℂ}
    (hρ : Lemma23InZeroWindow D ρ) : Lemma48InOmega D ρ :=
  ⟨hρ.1, by linarith [hρ.2]⟩

theorem lemma23_consecutive_of_local_exclusion
    {D p : ℕ} [NeZero p] (χ : RealPrimitiveCharacter D)
    (ψ : DirichletCharacter ℂ p) {r : ℝ}
    (hlocal : ∀ ρ : ℂ, Lemma48InOmega D ρ → lemma48ActualProduct χ ψ ρ = 0 →
      ρ.re = 1 / 2 ∧ ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < r →
        lemma48ActualProduct χ ψ (ρ + w) ≠ 0)
    {ρ ρ' : ℂ} (hρ : Lemma48InOmega D ρ) (hρ' : Lemma48InOmega D ρ')
    (hz : lemma48ActualProduct χ ψ ρ = 0) (hz' : lemma48ActualProduct χ ψ ρ' = 0)
    (hinc : ρ.im < ρ'.im) (hgap : ρ'.im - ρ.im < 2 * r) :
    Proposition22ConsecutiveZeros χ ψ ρ ρ' := by
  refine ⟨hρ, hρ', hz, hz', hinc, ?_⟩
  intro ζ hζ hlo hhi hzero
  have hl := hlocal ρ hρ hz
  have hr := hlocal ρ' hρ' hz'
  have hm := hlocal ζ hζ hzero
  have hn₁ : ‖ζ - ρ‖ = ζ.im - ρ.im := by
    have he : ζ - ρ = I * ((ζ.im - ρ.im : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hl.1, hm.1]
    rw [he, norm_mul, norm_I, norm_real, Real.norm_of_nonneg (by linarith), one_mul]
  have hn₂ : ‖ζ - ρ'‖ = ρ'.im - ζ.im := by
    have he : ζ - ρ' = I * ((ζ.im - ρ'.im : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hr.1, hm.1]
    rw [he, norm_mul, norm_I, norm_real, Real.norm_of_nonpos (by linarith), one_mul]
    ring
  by_cases hnear : ζ.im - ρ.im < r
  · have hh := hl.2 (ζ - ρ) (by rw [hn₁]; linarith) (by rw [hn₁]; exact hnear)
    rw [add_sub_cancel] at hh
    exact hh hzero
  · have hh := hr.2 (ζ - ρ') (by rw [hn₂]; linarith)
      (by rw [hn₂]; linarith)
    rw [add_sub_cancel] at hh
    exact hh hzero

theorem lemma23_actual_successor {m k c : ℝ}
    (hk : 0 < k) (hcmp : lemma47ModelErrorConstant < m * k)
    (hmodel : ∀ z : ℂ, ‖z‖ ≤ 1 / 2 →
      m * ‖z‖ ≤ ‖lemma23ExponentialGapModel Real.pi z‖)
    {D p : ℕ} [NeZero p] (χ : RealPrimitiveCharacter D)
    (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    (hsmallc : c * lemma44PaperAlpha D * lemma23PaperL D ≤ 1 / 4)
    (hsmallk : k * lemma44PaperAlpha D * lemma23PaperL D ≤ 1 / 4)
    (hlocal : ∀ ρ : ℂ, Lemma48InOmega D ρ → lemma48ActualProduct χ ψ ρ = 0 →
      ρ.re = 1 / 2 ∧ deriv (lemma48ActualProduct χ ψ) ρ ≠ 0 ∧
        ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < lemma46InnerRadius D c →
          lemma48ActualProduct χ ψ (ρ + w) ≠ 0)
    {ρ : ℂ} (hre : ρ.re = 1 / 2)
    (him : |ρ.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 1)
    (hz : lemma48ActualProduct χ ψ ρ = 0) :
    ∃ ρ' : ℂ, Proposition22ConsecutiveZeros χ ψ ρ ρ' ∧
      ρ'.im - ρ.im ≤ (3 / 2) * lemma44PaperAlpha D := by
  let a := lemma44PaperAlpha D
  let L := lemma23PaperL D
  let R := k * a ^ 2 * L
  have ha : 0 < a := (lemma46_alpha_parameters hD).1
  have hasmall : a < 1 / 4 := (lemma46_alpha_parameters hD).2.1
  have hRhi : R ≤ a / 4 := by
    have hh := mul_le_mul_of_nonneg_left hsmallk ha.le
    change a * (k * a * L) ≤ a * (1 / 4) at hh
    dsimp [R]
    nlinarith only [hh]
  have hrlo : (3 / 4) * a ≤ lemma46InnerRadius D c := by
    have hh := mul_le_mul_of_nonneg_left hsmallc ha.le
    unfold lemma46InnerRadius
    nlinarith only [hh]
  have hρΩ : Lemma48InOmega D ρ := ⟨by rw [hre]; norm_num, by linarith⟩
  have hA : lemma45ActualA χ ψ ρ = 0 := by
    change lemma48ActualProduct χ ψ ρ / _ = 0
    rw [hz, zero_div]
  obtain ⟨v, hv, hvzero⟩ := proposition22_actual_upper_neighbor hk hcmp hmodel χ ψ hD hψ
    (by linarith) hre hρΩ.2 hA
  change ‖v‖ ≤ R at hv
  let ζ := ρ + I * (a : ℂ) + v
  have himζ : ζ.im = ρ.im + a + v.im := by simp [ζ]
  have hvim : -R ≤ v.im ∧ v.im ≤ R := by
    exact ⟨by linarith [(abs_le.mp (abs_im_le_norm v)).1],
      (le_abs_self v.im).trans ((abs_im_le_norm v).trans hv)⟩
  have hinc : ρ.im < ζ.im := by rw [himζ]; linarith
  have hgap : ζ.im - ρ.im ≤ (3 / 2) * a := by rw [himζ]; linarith
  have hζΩ : Lemma48InOmega D ζ := by
    constructor
    · have he : ζ.re - 1 / 2 = v.re := by simp [ζ, hre]
      rw [he]
      exact (abs_re_le_norm v).trans_lt (by linarith)
    · apply abs_lt.mpr
      have hh := abs_lt.mp him
      rw [himζ]
      constructor <;> linarith
  have hw : ‖ζ - ρ‖ < 2 * a := by
    have he : ζ - ρ = I * (a : ℂ) + v := by dsimp [ζ]; ring
    rw [he]
    have hh := norm_add_le (I * (a : ℂ)) v
    rw [norm_mul, norm_I, norm_real, Real.norm_of_nonneg ha.le, one_mul] at hh
    linarith
  have hF := lemma23_omega1_F_ne_zero χ ψ ζ
    (lemma44_parameters_at_explicit_threshold hD).1 hψ.2
    (lemma47_outer_disk_omega1 hD hre hρΩ.2 hw)
  have hζzero : lemma48ActualProduct χ ψ ζ = 0 := by
    change lemma48ActualProduct χ ψ ζ / _ = 0 at hvzero
    exact (div_eq_zero_iff.mp hvzero).resolve_right hF
  refine ⟨ζ, lemma23_consecutive_of_local_exclusion χ ψ
    (fun z hΩ hzero => ⟨(hlocal z hΩ hzero).1, (hlocal z hΩ hzero).2.2⟩)
    hρΩ hζΩ hz hζzero hinc ?_, hgap⟩
  have hgap' : ζ.im - ρ.im ≤ a + R := by rw [himζ]; linarith
  linarith

theorem lemma23_actual_three_successors
    {D p : ℕ} [NeZero p] (χ : RealPrimitiveCharacter D)
    (ψ : DirichletCharacter ℂ p) (ha : lemma44PaperAlpha D < 1 / 4)
    (hsuccessor : ∀ ρ : ℂ, ρ.re = 1 / 2 →
      |ρ.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 1 →
      lemma48ActualProduct χ ψ ρ = 0 →
      ∃ ρ' : ℂ, Proposition22ConsecutiveZeros χ ψ ρ ρ' ∧
        ρ'.im - ρ.im ≤ (3 / 2) * lemma44PaperAlpha D)
    (hcritical : ∀ ρ : ℂ, Lemma48InOmega D ρ → lemma48ActualProduct χ ψ ρ = 0 →
      ρ.re = 1 / 2)
    {ρ : ℂ} (hρ : Lemma23InZeroWindow D ρ) (hre : ρ.re = 1 / 2)
    (hz : lemma48ActualProduct χ ψ ρ = 0) :
    ∃ ρ₁ ρ₂ ρ₃ : ℂ,
      Proposition22ConsecutiveZeros χ ψ ρ ρ₁ ∧
      Proposition22ConsecutiveZeros χ ψ ρ₁ ρ₂ ∧
      Proposition22ConsecutiveZeros χ ψ ρ₂ ρ₃ := by
  obtain ⟨ρ₁, h₁, hg₁⟩ := hsuccessor ρ hre (by linarith [hρ.2]) hz
  have hh := abs_lt.mp hρ.2
  have ht₁ : |ρ₁.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 1 := by
    apply abs_lt.mpr
    constructor <;> linarith [h₁.increasing]
  obtain ⟨ρ₂, h₂, hg₂⟩ := hsuccessor ρ₁
    (hcritical ρ₁ h₁.right_mem h₁.right_zero) ht₁ h₁.right_zero
  have ht₂ : |ρ₂.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 1 := by
    apply abs_lt.mpr
    constructor <;> linarith [h₁.increasing, h₂.increasing]
  obtain ⟨ρ₃, h₃, _⟩ := hsuccessor ρ₂
    (hcritical ρ₂ h₂.right_mem h₂.right_zero) ht₂ h₂.right_zero
  exact ⟨ρ₁, ρ₂, ρ₃, h₁, h₂, h₃⟩

end ZhangLS.Spec
