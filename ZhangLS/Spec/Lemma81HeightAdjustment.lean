import ZhangLS.Spec.Lemma81ActualContourShift

/-! # Height adjustment estimates for the actual residue rectangle -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Set MeasureTheory
open scoped Real Classical
set_option maxHeartbeats 2000000

lemma lemma81_height_band_of_near_endpoint {t e center H : ℝ}
    (he : |e-center| = H) (ht : |t-e| ≤ 1) :
    H-1 ≤ |t-center| ∧ |t-center| ≤ H+1 := by
  have hu := abs_add_le (t-e) (e-center)
  rw [sub_add_sub_cancel,he] at hu
  have hl := abs_add_le (e-t) (t-center)
  rw [sub_add_sub_cancel,he,abs_sub_comm e t] at hl
  exact ⟨by linarith only [hl,ht],by linarith only [hu,ht]⟩

lemma lemma81_height_of_mem_uIcc {t a b center H : ℝ}
    (ha : |a-center| ≤ H) (hb : |b-center| ≤ H) (ht : t ∈ uIcc a b) :
    |t-center| ≤ H := by
  rw [mem_uIcc] at ht
  rcases ht with ht | ht <;> apply abs_le.mpr <;>
    constructor <;> linarith only [(abs_le.mp ha).1,(abs_le.mp ha).2,
      (abs_le.mp hb).1,(abs_le.mp hb).2,ht.1,ht.2]

lemma lemma81_integral_height_change_bound (f : ℝ → ℂ) {A B lo hi δ : ℝ}
    (hδ : 0 ≤ δ) (hl : |lo-A| ≤ 1) (hu : |hi-B| ≤ 1)
    (hil : IntervalIntegrable f volume lo A) (him : IntervalIntegrable f volume A B)
    (hiu : IntervalIntegrable f volume B hi)
    (hbl : ∀ t ∈ uIcc lo A, ‖f t‖ ≤ δ)
    (hbu : ∀ t ∈ uIcc B hi, ‖f t‖ ≤ δ) :
    ‖(∫ t in lo..hi, f t)-(∫ t in A..B, f t)‖ ≤ 2*δ := by
  have hlb : ‖∫ t in lo..A, f t‖ ≤ δ := by
    apply (intervalIntegral.norm_integral_le_of_norm_le_const
      (fun t ht => hbl t (uIoc_subset_uIcc ht))).trans
    exact mul_le_of_le_one_right hδ (by rwa [abs_sub_comm])
  have hub : ‖∫ t in B..hi, f t‖ ≤ δ := by
    apply (intervalIntegral.norm_integral_le_of_norm_le_const
      (fun t ht => hbu t (uIoc_subset_uIcc ht))).trans
    exact mul_le_of_le_one_right hδ hu
  rw [← intervalIntegral.integral_add_adjacent_intervals (hil.trans him) hiu,
    ← intervalIntegral.integral_add_adjacent_intervals hil him]
  have he : ((∫ t in lo..A, f t)+(∫ t in A..B, f t))+(∫ t in B..hi, f t)-
      (∫ t in A..B, f t) = (∫ t in lo..A, f t)+(∫ t in B..hi, f t) := by ring
  rw [he]
  exact (norm_add_le _ _).trans (by linarith only [hlb,hub])

/-- Genuine integrability on both extended vertical lines, proved using
actual zero separation and branch nonvanishing. -/
theorem lemma81_uniform_extended_vertical_integrability {c : ℝ} (hc : 0 < c) :
    ∃ N : ℕ, lemma23SectionFourModulusThreshold ≤ N ∧
      ∀ {D p : ℕ} [NeZero p] (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p),
      N ≤ D → Lemma23InPsi1 χ ψ → ∀ Y : ℂ → ℂ, Lemma23ActualBranch ψ Y →
      ∀ a₁ a₂ : ℕ → ℂ, ∀ σ lo hi : ℝ,
      |σ-1/2| = lemma44PaperAlpha D →
      |lo-(lemma23PaperCenter D).im| ≤ lemma23PaperL D^405+1 →
      |hi-(lemma23PaperCenter D).im| ≤ lemma23PaperL D^405+1 →
      IntervalIntegrable (fun t => lemma81TildeIntegrand D c ψ Y a₁ a₂
        ((σ : ℂ)+(t : ℂ)*I)) volume lo hi := by
  obtain ⟨Ns,hNs,hsep⟩ := lemma81_uniform_extended_contour_separation
  obtain ⟨No,hNo,hoff⟩ := lemma52_exists_shift_threshold hc
  refine ⟨max Ns No,hNs.trans (le_max_left _ _),?_⟩
  intro D p _ χ ψ hD hψ Y hY a₁ a₂ σ lo hi hσ hlo hhi
  have hDs := (le_max_left Ns No).trans hD
  have hDo := (le_max_right Ns No).trans hD
  have hL := (lemma44_parameters_at_explicit_threshold (hNs.trans hDs)).1
  have hLp : 0 < lemma23PaperL D := by linarith only [hL]
  have ha := (lemma44_alpha_pos_le_one hL).1
  have ho := lemma52_offset_bounds hL hc (hoff D hDo)
  apply ContinuousOn.intervalIntegrable
  intro t ht
  let s : ℂ := (σ : ℂ)+(t : ℂ)*I
  have hre : s.re = σ := by simp [s]
  have him : s.im = t := by simp [s]
  have hheight : |s.im-(lemma23PaperCenter D).im| ≤ lemma23PaperL D^405+1 := by
    rw [him]
    exact lemma81_height_of_mem_uIcc hlo hhi ht
  have hwide : |s.im-(lemma23PaperCenter D).im| ≤ 2*lemma23PaperL D^405+3 := by
    linarith only [hheight,pow_nonneg hLp.le 405]
  have hspos : 0 < s.im := by linarith only [(lemma61_wide_height_data hL hwide).2.1]
  have hs := (hsep χ ψ hDs hψ).2 s (by rw [hre]; exact hσ) hheight
  have hLne : ψ.LFunction s ≠ 0 := by
    intro hz
    have hh := hs s hz
    simp only [one_mul,sub_self,norm_zero] at hh
    exact (not_le_of_gt ha) hh
  have hMne : lemma23DirichletNormalizedM ψ Y s ≠ 0 := mul_ne_zero
    (lemma52_actual_branch_ne_zero ψ hψ.1.2.1 hψ.1.1.ne_one Y hY hspos) hLne
  have han := lemma81_actual_tilde_integrand_analyticAt c ψ hψ.1.2.1 hψ.1.1.ne_one Y hY a₁ a₂
    hspos hMne (by linarith only [hspos,ho.1.1]) (by linarith only [hspos,ho.2.1.1])
    (by linarith only [hspos,ho.2.2.1])
  have hcpath : ContinuousAt (fun t : ℝ => lemma81TildeIntegrand D c ψ Y a₁ a₂
      ((σ : ℂ)+(t : ℂ)*I)) t :=
    ContinuousAt.comp (f := fun t : ℝ => (σ : ℂ)+(t : ℂ)*I) (x := t) han.continuousAt (by fun_prop)
  exact hcpath.continuousWithinAt

lemma lemma81_rectangle_normalization_vertical :
    (2*(Real.pi : ℂ)*I)⁻¹*I = ((2*Real.pi : ℝ) : ℂ)⁻¹ := by
  have he : ((2*Real.pi : ℝ) : ℂ) = 2*(Real.pi : ℂ) := by push_cast; rfl
  rw [he,mul_inv_rev]
  calc
    I⁻¹*(2*(Real.pi : ℂ))⁻¹*I = (I⁻¹*I)*(2*(Real.pi : ℂ))⁻¹ := by ring
    _ = _ := by rw [inv_mul_cancel₀ I_ne_zero,one_mul]

lemma lemma81_rectangle_normalization_norm_le_one : ‖(2*(Real.pi : ℂ)*I)⁻¹‖ ≤ 1 := by
  have hh := congrArg norm lemma81_rectangle_normalization_vertical
  rw [norm_mul,norm_I,mul_one] at hh
  rw [hh]
  exact lemma81_normalization_factor_norm_le_one

/-- Accounting for both horizontal edges and both vertical height changes.
The six unit-length errors retain their actual contour orientation. -/
lemma lemma81_rectangle_truncation_bound (f : ℂ → ℂ) {a b lo hi A B δ : ℝ}
    (_hδ : 0 ≤ δ)
    (hb : ‖∫ x in a..b, f ((x : ℂ)+(lo : ℂ)*I)‖ ≤ δ)
    (ht : ‖∫ x in a..b, f ((x : ℂ)+(hi : ℂ)*I)‖ ≤ δ)
    (hl : ‖(∫ y in lo..hi, f ((a : ℂ)+(y : ℂ)*I))-
      (∫ y in A..B, f ((a : ℂ)+(y : ℂ)*I))‖ ≤ 2*δ)
    (hr : ‖(∫ y in lo..hi, f ((b : ℂ)+(y : ℂ)*I))-
      (∫ y in A..B, f ((b : ℂ)+(y : ℂ)*I))‖ ≤ 2*δ) :
    ‖(2*(Real.pi : ℂ)*I)⁻¹*lemma81RectangleIntegral f a b lo hi-
      ((2*Real.pi : ℝ) : ℂ)⁻¹*((∫ y in A..B, f ((b : ℂ)+(y : ℂ)*I))-
        (∫ y in A..B, f ((a : ℂ)+(y : ℂ)*I)))‖ ≤ 6*δ := by
  have he : (2*(Real.pi : ℂ)*I)⁻¹*lemma81RectangleIntegral f a b lo hi-
      ((2*Real.pi : ℝ) : ℂ)⁻¹*((∫ y in A..B, f ((b : ℂ)+(y : ℂ)*I))-
        (∫ y in A..B, f ((a : ℂ)+(y : ℂ)*I))) =
      (2*(Real.pi : ℂ)*I)⁻¹*((∫ x in a..b, f ((x : ℂ)+(lo : ℂ)*I))-
        (∫ x in a..b, f ((x : ℂ)+(hi : ℂ)*I)))+
      ((2*Real.pi : ℝ) : ℂ)⁻¹*(((∫ y in lo..hi, f ((b : ℂ)+(y : ℂ)*I))-
        (∫ y in A..B, f ((b : ℂ)+(y : ℂ)*I)))-
        ((∫ y in lo..hi, f ((a : ℂ)+(y : ℂ)*I))-
          (∫ y in A..B, f ((a : ℂ)+(y : ℂ)*I)))) := by
    unfold lemma81RectangleIntegral
    rw [← lemma81_rectangle_normalization_vertical]
    ring
  rw [he]
  apply (norm_add_le _ _).trans
  have hb' : ‖(2*(Real.pi : ℂ)*I)⁻¹*((∫ x in a..b, f ((x : ℂ)+(lo : ℂ)*I))-
      (∫ x in a..b, f ((x : ℂ)+(hi : ℂ)*I)))‖ ≤ 2*δ := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) lemma81_rectangle_normalization_norm_le_one).trans
      ((norm_sub_le _ _).trans (by linarith only [hb,ht]))
  have hv : ‖((2*Real.pi : ℝ) : ℂ)⁻¹*(((∫ y in lo..hi, f ((b : ℂ)+(y : ℂ)*I))-
      (∫ y in A..B, f ((b : ℂ)+(y : ℂ)*I)))-
      ((∫ y in lo..hi, f ((a : ℂ)+(y : ℂ)*I))-
        (∫ y in A..B, f ((a : ℂ)+(y : ℂ)*I))))‖ ≤ 4*δ := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) lemma81_normalization_factor_norm_le_one).trans
      ((norm_sub_le _ _).trans (by linarith only [hl,hr]))
  linarith only [hb',hv]

end ZhangLS.Spec
