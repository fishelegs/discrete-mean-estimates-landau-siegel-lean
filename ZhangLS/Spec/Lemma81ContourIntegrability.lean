import ZhangLS.Spec.Lemma81IntegrandAnalytic

/-! # Actual contour integrability for the original Lemma 8.1

The poles of C̃ are excluded on both original vertical contours using
Proposition 2.2 via the proved all-zero separation, actual branch nonvanishing,
and exact normalized reflection. No contour-integrability assumption is added.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex ComplexConjugate Set MeasureTheory
open scoped Real Topology
set_option maxHeartbeats 2000000

lemma lemma81_right_point_mem_segment {D : ℕ} (hL : 3 ≤ lemma23PaperL D) {t : ℝ}
    (ht : t ∈ uIcc (-(lemma23PaperL D ^ 405)) (lemma23PaperL D ^ 405)) :
    Lemma81OnRightSegment D (lemma81SegmentPoint D (lemma44PaperAlpha D) t) := by
  have hLp : 0 < lemma23PaperL D := by linarith
  have hH : 0 < lemma23PaperL D ^ 405 := pow_pos hLp 405
  rw [uIcc_of_le (by linarith only [hH])] at ht
  constructor
  · simp [lemma81SegmentPoint,lemma23PaperCenter]
  · simpa [lemma81SegmentPoint] using abs_le.mpr ht

lemma lemma81_uniform_right_contour_regular_data {c : ℝ} (hc : 0 < c) :
    ∃ N : ℕ, lemma23SectionFourModulusThreshold ≤ N ∧
    ∀ {D p : ℕ} [NeZero p] (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p),
      N ≤ D → Lemma23InPsi1 χ ψ → ∀ Y : ℂ → ℂ, Lemma23ActualBranch ψ Y →
      ∀ {s : ℂ}, Lemma81OnRightSegment D s →
      0 < s.im ∧ ψ.LFunction s ≠ 0 ∧ lemma23DirichletNormalizedM ψ Y s ≠ 0 ∧
        lemma23DirichletNormalizedM ψ Y (1-conj s) ≠ 0 ∧
        0 < s.im + lemma23PaperOffsetOne D c ∧
        0 < s.im + lemma23PaperOffsetTwo D c ∧
        0 < s.im + lemma23PaperOffsetThree D c := by
  obtain ⟨Nsep,hsep⟩ := lemma81_right_segment_zero_separation
  obtain ⟨Nsmall,hsection,hsmall⟩ := lemma52_exists_shift_threshold hc
  refine ⟨max Nsep Nsmall,hsection.trans (le_max_right _ _),?_⟩
  intro D p _ χ ψ hD hψ Y hY s hs
  have hDsep := (le_max_left Nsep Nsmall).trans hD
  have hDsmall := (le_max_right Nsep Nsmall).trans hD
  have hL := (lemma44_parameters_at_explicit_threshold (hsection.trans hDsmall)).1
  have hLp : 0 < lemma23PaperL D := by linarith
  have ha := (lemma44_alpha_pos_le_one hL).1
  have hre : |s.re-1/2| ≤ lemma44PaperAlpha D := by
    rw [hs.1]
    simpa using (abs_of_pos ha).le
  have hsExt : Lemma51InExtendedRegion D s := ⟨hre,by
    linarith only [hs.2,pow_nonneg hLp.le 405]⟩
  have hT : 0 < lemma51PaperT0 D := by unfold lemma51PaperT0; positivity
  have hspos := hT.trans_le (lemma51_extended_region_data hL hsExt).2.2.1
  have hLne : ψ.LFunction s ≠ 0 := by
    intro hz
    have hh := hsep χ ψ hDsep hψ hs s hz
    simp only [one_mul,sub_self,norm_zero] at hh
    exact (not_le_of_gt ha) hh
  have hYne := lemma52_actual_branch_ne_zero ψ hψ.1.2.1 hψ.1.1.ne_one Y hY hspos
  have hMne : lemma23DirichletNormalizedM ψ Y s ≠ 0 := mul_ne_zero hYne hLne
  have hMleft : lemma23DirichletNormalizedM ψ Y (1-conj s) ≠ 0 := by
    rw [lemma81_actual_M_reflection ψ hψ.1.2.1 hψ.1.1.ne_one Y hY hspos]
    simpa using hMne
  have hb := lemma52_offset_bounds hL hc (hsmall D hDsmall)
  exact ⟨hspos,hLne,hMne,hMleft,by linarith only [hspos,hb.1.1],
    by linarith only [hspos,hb.2.1.1],by linarith only [hspos,hb.2.2.1]⟩

noncomputable def lemma81CIntegrand {p : ℕ} [NeZero p]
    (D : ℕ) (c : ℝ) (ψ : DirichletCharacter ℂ p)
    (a₁ a₂ : ℕ → ℂ) (s : ℂ) : ℂ :=
  lemma81ActualC D c ψ s * lemma81Polynomial D a₁ ψ s *
    lemma81Polynomial D a₂ ψ⁻¹ (1-s) * lemma81Omega D s

lemma lemma81_actual_C_integrand_analyticAt {D p : ℕ} [NeZero p]
    (c : ℝ) (ψ : DirichletCharacter ℂ p) (hψ : ψ.IsPrimitive) (hp : p ≠ 1)
    (a₁ a₂ : ℕ → ℂ) {s : ℂ} (hs : 0 < s.im) (hLne : ψ.LFunction s ≠ 0)
    (h₁ : 0 < s.im + lemma23PaperOffsetOne D c)
    (h₂ : 0 < s.im + lemma23PaperOffsetTwo D c)
    (h₃ : 0 < s.im + lemma23PaperOffsetThree D c) :
    AnalyticAt ℂ (lemma81CIntegrand D c ψ a₁ a₂) s := by
  have hC := lemma81_actual_C_analyticAt c ψ hψ hp hs hLne h₁ h₂ h₃
  have hA₁ := (lemma81_polynomial_differentiable D a₁ ψ).analyticAt s
  have hA₂ := ((lemma81_polynomial_differentiable D a₂ ψ⁻¹).analyticAt (1-s)).comp
    (show AnalyticAt ℂ (fun z : ℂ => 1-z) s by fun_prop)
  exact ((hC.mul hA₁).mul hA₂).mul ((lemma81_omega_differentiable D).analyticAt s)

/-- All four actual integrals used in the replacement and reflection steps
are genuine integrable contours, not merely totalized integral expressions. -/
theorem lemma81_uniform_actual_contour_integrability {c : ℝ} (hc : 0 < c) :
    ∃ N : ℕ, ∀ {D p : ℕ} [NeZero p] (χ : RealPrimitiveCharacter D)
      (ψ : DirichletCharacter ℂ p), N ≤ D → Lemma23InPsi1 χ ψ →
      ∀ Y : ℂ → ℂ, Lemma23ActualBranch ψ Y → ∀ a₁ a₂ : ℕ → ℂ,
      IntervalIntegrable (fun t => lemma81TildeIntegrand D c ψ Y a₁ a₂
        (lemma81SegmentPoint D (lemma44PaperAlpha D) t)) volume
        (-(lemma23PaperL D ^ 405)) (lemma23PaperL D ^ 405) ∧
      IntervalIntegrable (fun t => lemma81TildeIntegrand D c ψ Y a₁ a₂
        (lemma81SegmentPoint D (-lemma44PaperAlpha D) t)) volume
        (-(lemma23PaperL D ^ 405)) (lemma23PaperL D ^ 405) ∧
      IntervalIntegrable (fun t => lemma81CIntegrand D c ψ a₁ a₂
        (lemma81SegmentPoint D (lemma44PaperAlpha D) t)) volume
        (-(lemma23PaperL D ^ 405)) (lemma23PaperL D ^ 405) ∧
      IntervalIntegrable (fun t => lemma81CIntegrand D c ψ a₁ a₂
        (lemma81SegmentPoint D 1 t)) volume
        (-(lemma23PaperL D ^ 405)) (lemma23PaperL D ^ 405) := by
  obtain ⟨N,hN,hdata⟩ := lemma81_uniform_right_contour_regular_data hc
  refine ⟨N,?_⟩
  intro D p _ χ ψ hD hψ Y hY a₁ a₂
  have hL := (lemma44_parameters_at_explicit_threshold (hN.trans hD)).1
  have hpath (x : ℝ) : Continuous (lemma81SegmentPoint D x) := by
    unfold lemma81SegmentPoint
    fun_prop
  have hd (t : ℝ) (ht : t ∈ uIcc (-(lemma23PaperL D ^ 405)) (lemma23PaperL D ^ 405)) :=
    hdata χ ψ hD hψ Y hY (lemma81_right_point_mem_segment hL ht)
  refine ⟨ContinuousOn.intervalIntegrable ?_,ContinuousOn.intervalIntegrable ?_,
    ContinuousOn.intervalIntegrable ?_,ContinuousOn.intervalIntegrable ?_⟩
  · intro t ht
    have hh := hd t ht
    exact ((lemma81_actual_tilde_integrand_analyticAt c ψ hψ.1.2.1 hψ.1.1.ne_one
      Y hY a₁ a₂ hh.1 hh.2.2.1 hh.2.2.2.2.1 hh.2.2.2.2.2.1 hh.2.2.2.2.2.2).continuousAt.comp
      (hpath _).continuousAt).continuousWithinAt
  · intro t ht
    have hh := hd t ht
    have hM : lemma23DirichletNormalizedM ψ Y (lemma81SegmentPoint D (-lemma44PaperAlpha D) t) ≠ 0 := by
      rw [← lemma81_segment_point_reflection]
      exact hh.2.2.2.1
    have him : (lemma81SegmentPoint D (-lemma44PaperAlpha D) t).im =
      (lemma81SegmentPoint D (lemma44PaperAlpha D) t).im := by simp [lemma81SegmentPoint]
    exact ((lemma81_actual_tilde_integrand_analyticAt c ψ hψ.1.2.1 hψ.1.1.ne_one Y hY a₁ a₂
      (by rw [him]; exact hh.1) hM (by rw [him]; exact hh.2.2.2.2.1)
      (by rw [him]; exact hh.2.2.2.2.2.1) (by rw [him]; exact hh.2.2.2.2.2.2)).continuousAt.comp
      (hpath _).continuousAt).continuousWithinAt
  · intro t ht
    have hh := hd t ht
    exact ((lemma81_actual_C_integrand_analyticAt c ψ hψ.1.2.1 hψ.1.1.ne_one a₁ a₂
      hh.1 hh.2.1 hh.2.2.2.2.1 hh.2.2.2.2.2.1 hh.2.2.2.2.2.2).continuousAt.comp
      (hpath _).continuousAt).continuousWithinAt
  · intro t ht
    have hh := hd t ht
    have him : (lemma81SegmentPoint D 1 t).im =
      (lemma81SegmentPoint D (lemma44PaperAlpha D) t).im := by simp [lemma81SegmentPoint]
    have hspos : 0 < (lemma81SegmentPoint D 1 t).im := by rw [him]; exact hh.1
    have hne : lemma81SegmentPoint D 1 t ≠ 1 := by intro he; rw [he] at hspos; simp at hspos
    have hLne := DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ (Or.inr hne)
      (s := lemma81SegmentPoint D 1 t) (by simp [lemma81SegmentPoint,lemma23PaperCenter])
    exact ((lemma81_actual_C_integrand_analyticAt c ψ hψ.1.2.1 hψ.1.1.ne_one a₁ a₂
      hspos hLne (by rw [him]; exact hh.2.2.2.2.1)
      (by rw [him]; exact hh.2.2.2.2.2.1) (by rw [him]; exact hh.2.2.2.2.2.2)).continuousAt.comp
      (hpath _).continuousAt).continuousWithinAt

end ZhangLS.Spec
