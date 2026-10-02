import ZhangLS.Spec.Proposition22Zeros
import ZhangLS.Spec.Proposition22Neighbor

/-! # Proposition 2.2 for the actual Dirichlet L-product

The original Ω, actual good-set membership and actual product zeros are
retained. Consecutive means that no product zero in Ω has an intermediate
ordinate. One absolute error constant and one modulus threshold are uniform
over the whole character family.
-/

namespace ZhangLS.Spec

open Complex Metric Set

set_option maxHeartbeats 1000000

/-- Consecutive zeros in precisely the original region, without assuming
critical-line location, simplicity, existence of other zeros or gap bounds. -/
structure Proposition22ConsecutiveZeros {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (ρ ρ' : ℂ) : Prop where
  left_mem : Lemma48InOmega D ρ
  right_mem : Lemma48InOmega D ρ'
  left_zero : lemma48ActualProduct χ ψ ρ = 0
  right_zero : lemma48ActualProduct χ ψ ρ' = 0
  increasing : ρ.im < ρ'.im
  between_nonzero : ∀ ζ : ℂ, Lemma48InOmega D ζ →
    ρ.im < ζ.im → ζ.im < ρ'.im → lemma48ActualProduct χ ψ ζ ≠ 0

theorem proposition22_consecutive_gap_bounds {m k c : ℝ}
    (hk : 0 < k) (hcmp : lemma47ModelErrorConstant < m * k)
    (hmodel : ∀ z : ℂ, ‖z‖ ≤ 1 / 2 →
      m * ‖z‖ ≤ ‖lemma23ExponentialGapModel Real.pi z‖)
    {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    (hsmall : k * lemma44PaperAlpha D * lemma23PaperL D ≤ 1 / 2)
    (hlocal : ∀ ρ : ℂ, Lemma48InOmega D ρ → lemma48ActualProduct χ ψ ρ = 0 →
      ρ.re = 1 / 2 ∧ deriv (lemma48ActualProduct χ ψ) ρ ≠ 0 ∧
        ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < lemma46InnerRadius D c →
          lemma48ActualProduct χ ψ (ρ + w) ≠ 0)
    {ρ ρ' : ℂ} (hcon : Proposition22ConsecutiveZeros χ ψ ρ ρ') :
    lemma46InnerRadius D c ≤ ρ'.im - ρ.im ∧
      ρ'.im - ρ.im ≤ lemma44PaperAlpha D + k * lemma44PaperAlpha D ^ 2 * lemma23PaperL D := by
  let a := lemma44PaperAlpha D
  let L := lemma23PaperL D
  let g := ρ'.im - ρ.im
  let R := k * a ^ 2 * L
  have ha : 0 < a := (lemma46_alpha_parameters hD).1
  have hasmall : a < 1 / 4 := (lemma46_alpha_parameters hD).2.1
  have hL : 0 < L := by linarith [(lemma45_parameters_at_threshold hD).1]
  have hgp : 0 < g := sub_pos.mpr hcon.increasing
  have hz := hlocal ρ hcon.left_mem hcon.left_zero
  have hz' := hlocal ρ' hcon.right_mem hcon.right_zero
  have hdiff : ρ' - ρ = I * (g : ℂ) := by
    apply Complex.ext <;> simp [g, hz.1, hz'.1]
  have hnorm : ‖ρ' - ρ‖ = g := by
    rw [hdiff, norm_mul, norm_I, norm_real, Real.norm_of_nonneg hgp.le, one_mul]
  constructor
  · by_contra h
    have hlt : ‖ρ' - ρ‖ < lemma46InnerRadius D c := by rw [hnorm]; exact lt_of_not_ge h
    have hne := hz.2.2 (ρ' - ρ) (by rw [hnorm]; exact hgp) hlt
    rw [add_sub_cancel] at hne
    exact hne hcon.right_zero
  · change g ≤ a + R
    by_contra h
    have hgR : a + R < g := lt_of_not_ge h
    have hA : lemma45ActualA χ ψ ρ = 0 := by
      change lemma48ActualProduct χ ψ ρ / _ = 0
      rw [hcon.left_zero, zero_div]
    obtain ⟨v, hv, hvzero⟩ := proposition22_actual_upper_neighbor hk hcmp hmodel χ ψ hD hψ
      hsmall hz.1 hcon.left_mem.2 hA
    change ‖v‖ ≤ R at hv
    have hRhi : R ≤ a / 2 := by
      have hh := mul_le_mul_of_nonneg_left hsmall ha.le
      change a * (k * a * L) ≤ a * (1 / 2) at hh
      dsimp [R]
      nlinarith only [hh]
    let ζ := ρ + I * (a : ℂ) + v
    have hζim : ζ.im = ρ.im + a + v.im := by simp [ζ]
    have hiv : -R ≤ v.im ∧ v.im ≤ R := by
      exact ⟨by linarith [(abs_le.mp (abs_im_le_norm v)).1],
        (le_abs_self v.im).trans ((abs_im_le_norm v).trans hv)⟩
    have hζlo : ρ.im < ζ.im := by rw [hζim]; linarith
    have hζhi : ζ.im < ρ'.im := by rw [hζim]; dsimp [g] at hgR; linarith
    have hζΩ : Lemma48InOmega D ζ := by
      constructor
      · have he : ζ.re - 1 / 2 = v.re := by simp [ζ, hz.1]
        rw [he]
        exact (abs_re_le_norm v).trans_lt (by linarith)
      · apply abs_lt.mpr
        have hl := abs_lt.mp hcon.left_mem.2
        have hr := abs_lt.mp hcon.right_mem.2
        exact ⟨by linarith [hl.1], by linarith [hr.2]⟩
    have hw : ‖ζ - ρ‖ < 2 * a := by
      have he : ζ - ρ = I * (a : ℂ) + v := by dsimp [ζ]; ring
      rw [he]
      have ht := norm_add_le (I * (a : ℂ)) v
      rw [norm_mul, norm_I, norm_real, Real.norm_of_nonneg ha.le, one_mul] at ht
      linarith
    have hζω := lemma47_outer_disk_omega1 hD hz.1 hcon.left_mem.2 hw
    have hF := lemma23_omega1_F_ne_zero χ ψ ζ
      (lemma44_parameters_at_explicit_threshold hD).1 hψ.2 hζω
    have hζzero : lemma48ActualProduct χ ψ ζ = 0 := by
      change lemma48ActualProduct χ ψ ζ / _ = 0 at hvzero
      exact (div_eq_zero_iff.mp hvzero).resolve_right hF
    exact hcon.between_nonzero ζ hζΩ hζlo hζhi hζzero

/-- The three original conclusions of Proposition 2.2. The hypotheses
contain no critical-line, simplicity or gap conclusions. -/
def Proposition22Target : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℕ, ∀ {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p),
    D₀ ≤ D → Lemma23InPsi1 χ ψ →
    (∀ ρ : ℂ, Lemma48InOmega D ρ → lemma48ActualProduct χ ψ ρ = 0 →
      ρ.re = 1 / 2 ∧ deriv (lemma48ActualProduct χ ψ) ρ ≠ 0) ∧
    (∀ ρ ρ' : ℂ, Proposition22ConsecutiveZeros χ ψ ρ ρ' →
      |ρ'.im - ρ.im - lemma44PaperAlpha D| ≤
        C * lemma44PaperAlpha D ^ 2 * lemma23PaperL D)

theorem proposition22_proved : Proposition22Target := by
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
  let C := c + k
  have hC : 0 < C := add_pos hc hk
  obtain ⟨D₀, hD₀, hsmall⟩ := lemma46_exists_contraction_threshold hC
  refine ⟨C, hC, D₀, ?_⟩
  intro D p hp χ ψ hD hψ
  have hsection := hD₀.trans hD
  have ha := (lemma46_alpha_parameters hsection).1
  have hL : 0 < lemma23PaperL D := by linarith [(lemma45_parameters_at_threshold hsection).1]
  have hsmallc : c * lemma44PaperAlpha D * lemma23PaperL D ≤ 1 / 2 := by
    have hh := hsmall D hD
    dsimp [C] at hh
    nlinarith only [hh, mul_pos (mul_pos hk ha) hL]
  have hsmallk : k * lemma44PaperAlpha D * lemma23PaperL D ≤ 1 / 2 := by
    have hh := hsmall D hD
    dsimp [C] at hh
    nlinarith only [hh, mul_pos (mul_pos hc ha) hL]
  have hlocal := fun ρ hρ hz => proposition22_actual_zero_analysis hm hc hcmp hmodel
    χ ψ hsection hψ hsmallc (ρ := ρ) hρ hz
  constructor
  · intro ρ hρ hz
    exact ⟨(hlocal ρ hρ hz).1, (hlocal ρ hρ hz).2.1⟩
  · intro ρ ρ' hcon
    have hb := proposition22_consecutive_gap_bounds hk hkcmp hnmodel χ ψ hsection hψ
      hsmallk hlocal hcon
    have hweight : 0 ≤ lemma44PaperAlpha D ^ 2 * lemma23PaperL D := by positivity
    have hcC : c * lemma44PaperAlpha D ^ 2 * lemma23PaperL D ≤
        C * lemma44PaperAlpha D ^ 2 * lemma23PaperL D := by
      have hh := mul_le_mul_of_nonneg_right (show c ≤ C by dsimp [C]; linarith) hweight
      nlinarith only [hh]
    have hkC : k * lemma44PaperAlpha D ^ 2 * lemma23PaperL D ≤
        C * lemma44PaperAlpha D ^ 2 * lemma23PaperL D := by
      have hh := mul_le_mul_of_nonneg_right (show k ≤ C by dsimp [C]; linarith) hweight
      nlinarith only [hh]
    unfold lemma46InnerRadius at hb
    exact abs_le.mpr ⟨by nlinarith only [hb.1, hcC], by linarith only [hb.2, hkC]⟩

end ZhangLS.Spec
