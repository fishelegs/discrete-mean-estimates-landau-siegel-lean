import ZhangLS.Spec.ChiReciprocalStrip

namespace ZhangLS.Spec
open Complex Metric Set
open scoped Real
set_option maxHeartbeats 1200000

/-- The left side and horizontal connections required by the original Perron contour.
The right endpoint is allowed up to 1+1/log D. -/
def ChiReciprocalContour (D : ℕ) (s : ℂ) : Prop :=
  (s.re = 1-1/Real.log (D:ℝ) ∧ |s.im| ≤ D) ∨
  (|s.im| = D ∧ 1-1/Real.log (D:ℝ) ≤ s.re ∧ s.re ≤ 1+1/Real.log (D:ℝ))

lemma chi_reciprocal_contour_geometry {D : ℕ} (hD : 1 < D)
    (hL : 8 ≤ Real.log (D:ℝ)) {ρ : ℝ}
    (hclose : 1-ρ ≤ 1/(4*Real.log (D:ℝ))) {s : ℂ}
    (hs : ChiReciprocalContour D s) :
    1-1/Real.log (D:ℝ) ≤ s.re ∧ s.re ≤ 1+1/Real.log (D:ℝ) ∧
      |s.im| ≤ D ∧ 1/(2*Real.log (D:ℝ)) ≤ ‖s-(ρ:ℂ)‖ := by
  have hLp : 0 < Real.log (D:ℝ) := by linarith
  have hi : 0 < 1/Real.log (D:ℝ) := by positivity
  have he4 : 1/(4*Real.log (D:ℝ))=(1/Real.log (D:ℝ))/4 := by ring
  have he2 : 1/(2*Real.log (D:ℝ))=(1/Real.log (D:ℝ))/2 := by ring
  rcases hs with ⟨hre,ht⟩ | ⟨ht,hlo,hhi⟩
  · refine ⟨hre.ge,by linarith,ht,?_⟩
    have hr : 1/(2*Real.log (D:ℝ)) ≤ ρ-s.re := by
      rw [he4] at hclose
      rw [he2,hre]
      linarith
    have hn := Complex.abs_re_le_norm (s-(ρ:ℂ))
    simp only [sub_re,ofReal_re] at hn
    exact hr.trans ((by linarith [neg_le_abs (s.re-ρ)] : ρ-s.re ≤ |s.re-ρ|).trans hn)
  · refine ⟨hlo,hhi,ht.le,?_⟩
    have hn := Complex.abs_im_le_norm (s-(ρ:ℂ))
    simp only [sub_im,ofReal_im,sub_zero,ht] at hn
    have hD1 : (1:ℝ) ≤ D := by exact_mod_cast hD.le
    have hi1 : 1/(2*Real.log (D:ℝ)) ≤ 1 :=
      (div_le_one (by positivity : 0 < 2*Real.log (D:ℝ))).mpr (by linarith)
    exact hi1.trans (hD1.trans hn)

/-- Separation by 1/(2log D) absorbs precisely one further logarithmic power. -/
lemma chi_reciprocal_distance_absorption {L M q : ℝ}
    (hL : 1 ≤ L) (hM : 0 ≤ M) (hq : 1/(2*L) ≤ q) :
    M*L^25*(1+q⁻¹) ≤ 3*M*L^26 := by
  have hLp : 0 < L := by linarith
  have hqp : 0 < q := (by positivity : 0 < 1/(2*L)).trans_le hq
  have hinv := one_div_le_one_div_of_le (by positivity : 0 < 1/(2*L)) hq
  simp only [one_div,inv_inv] at hinv
  have hh : 1+q⁻¹ ≤ 3*L := by linarith
  calc
    _ ≤ M*L^25*(3*L) := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by ring

/-- Actual nonvanishing and polynomial reciprocal control from the proved 5.5 zero data. -/
theorem chi_actual_reciprocal_contour_from_zero_data {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 8 ≤ Real.log (D:ℝ)) {ρ : ℝ}
    (hρ : 0 ≤ 1-ρ) (hclose : 1-ρ ≤ 1/(4*Real.log (D:ℝ)))
    (hzero : dirichletLFunction χ (ρ:ℂ) = 0)
    (hsimple : deriv (dirichletLFunction χ) (ρ:ℂ) ≠ 0)
    (hunique : ∀ z : ℂ, Lemma55InZeroRegion D z →
      dirichletLFunction χ z = 0 → z = (ρ:ℂ))
    {s : ℂ} (hs : ChiReciprocalContour D s) :
    dirichletLFunction χ s ≠ 0 ∧
      ‖(dirichletLFunction χ s)⁻¹‖ ≤ 3*chiReciprocalConstant*Real.log (D:ℝ)^26 := by
  have hLp : 0 < Real.log (D:ℝ) := by linarith
  obtain ⟨hlo,hhi,ht,hsep⟩ := chi_reciprocal_contour_geometry hD hL hclose hs
  have hsepPos : 0 < ‖s-(ρ:ℂ)‖ := (by positivity : 0 < 1/(2*Real.log (D:ℝ))).trans_le hsep
  have hregion : Lemma55InZeroRegion D s := by
    constructor
    · have hi : 0 < 1/Real.log (D:ℝ) := by positivity
      simp only [div_eq_mul_inv,one_mul] at hlo hi ⊢
      linarith
    · have hDp : (0:ℝ) < D := by exact_mod_cast (by omega : 0 < D)
      linarith
  have hn : dirichletLFunction χ s ≠ 0 := by
    intro he
    have hsρ := hunique s hregion he
    simp [hsρ] at hsepPos
  have hclose' : 1-ρ ≤ 1/Real.log (D:ℝ) := hclose.trans
    (one_div_le_one_div_of_le hLp (by linarith))
  refine ⟨hn,?_⟩
  exact (chi_actual_inverse_strip_from_zero_data χ hD hL hρ hclose' hzero hsimple hunique hlo hhi ht).trans
    (chi_reciprocal_distance_absorption (by linarith) chi_reciprocal_constant_pos.le hsep)

/-- One uniform threshold supplies the genuine exceptional zero and the entire
reciprocal strip bound directly from the original normalized assumption (A). -/
theorem chi_actual_inverse_strip_under_A :
    ∃ D₀ : ℕ, 2 ≤ D₀ ∧ ∀ {D : ℕ} (χ : RealPrimitiveCharacter D), D₀ ≤ D →
      NormalizedAssumptionA χ →
      ∃ ρ : ℝ, 0 < 1-ρ ∧ 1-ρ ≤ 64*Real.log (D:ℝ)^(-2022:ℤ) ∧
        1-ρ ≤ 1/(4*Real.log (D:ℝ)) ∧
        dirichletLFunction χ (ρ:ℂ) = 0 ∧
        deriv (dirichletLFunction χ) (ρ:ℂ) ≠ 0 ∧
        (∀ s : ℂ, 1-1/Real.log (D:ℝ) ≤ s.re → s.re ≤ 1+1/Real.log (D:ℝ) →
          |s.im| ≤ D → ‖(dirichletLFunction χ s)⁻¹‖ ≤
            chiReciprocalConstant * Real.log (D:ℝ)^25 * (1+‖s-(ρ:ℂ)‖⁻¹)) ∧
        (∀ s : ℂ, ChiReciprocalContour D s → dirichletLFunction χ s ≠ 0 ∧
          ‖(dirichletLFunction χ s)⁻¹‖ ≤ 3*chiReciprocalConstant*Real.log (D:ℝ)^26) := by
  obtain ⟨D55,h55⟩ := lemma55_at_constant_sixty_four.2
  let D₀ := max D55 (max 2 lemma57ExplicitModulusThreshold)
  have hD02 : 2 ≤ D₀ := (le_max_left _ _).trans (le_max_right _ _)
  refine ⟨D₀,hD02,?_⟩
  intro D χ hDN hA
  have hD : 1 < D := by omega
  have hD55 : D55 ≤ D := (le_max_left _ _).trans hDN
  have hD57 : lemma57ExplicitModulusThreshold ≤ D :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hDN)
  have hL : 8 ≤ Real.log (D:ℝ) := by linarith [lemma57_log_ge_ten_million hD57]
  have hLp : 0 < Real.log (D:ℝ) := by linarith
  obtain ⟨ρ,hρ,hclose,hzero,hsimple,hunique⟩ := h55 χ hD55 hD hA
  have hsmall : 1-ρ ≤ 1/(4*Real.log (D:ℝ)) := hclose.trans (lemma55_local_zero_budget hD57).2.1
  have hsmall' : 1-ρ ≤ 1/Real.log (D:ℝ) := hsmall.trans
    (one_div_le_one_div_of_le hLp (by linarith))
  refine ⟨ρ,hρ,hclose,hsmall,hzero,hsimple,?_,?_⟩
  · intro s hlo hhi ht
    exact chi_actual_inverse_strip_from_zero_data χ hD hL hρ.le hsmall' hzero hsimple hunique hlo hhi ht
  · intro s hs
    exact chi_actual_reciprocal_contour_from_zero_data χ hD hL hρ.le hsmall hzero hsimple hunique hs

/-- Absolute C, fixed natural exponent K, and D₀ are all chosen before D and χ.
Nonvanishing is a conclusion, obtained from original 5.5 under original (A). -/
theorem chi_actual_polynomial_reciprocal_contour :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, ∃ D₀ : ℕ, 2 ≤ D₀ ∧
      ∀ {D : ℕ} (χ : RealPrimitiveCharacter D), D₀ ≤ D → NormalizedAssumptionA χ →
        ∀ s : ℂ, ChiReciprocalContour D s → dirichletLFunction χ s ≠ 0 ∧
          ‖(dirichletLFunction χ s)⁻¹‖ ≤ C*Real.log (D:ℝ)^K := by
  obtain ⟨D₀,hD02,hmain⟩ := chi_actual_inverse_strip_under_A
  refine ⟨3*chiReciprocalConstant,mul_pos (by norm_num) chi_reciprocal_constant_pos,
    26,D₀,hD02,?_⟩
  intro D χ hDN hA s hs
  obtain ⟨ρ,_,_,_,_,_,_,hcontour⟩ := hmain χ hDN hA
  exact hcontour s hs

end ZhangLS.Spec
