import ZhangLS.Spec.Lemma81Objects
import ZhangLS.Spec.Lemma81NormalizedReflection

/-! # Exact reflected contour identity in Lemma 8.1

This proves the actual −Ĩ⁻₁(a₁,a₂)=conj(Ĩ⁺₁(conj a₂,conj a₁)) relation.
No approximate functional equation, mean bound, Assumption (A), or integral
reflection identity is assumed. The prime family, actual branches, actual
shifts, Gaussian, finite polynomials and both oriented contours are retained.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex ComplexConjugate Set MeasureTheory
open scoped Real Topology
set_option maxHeartbeats 2000000

lemma lemma81_Ctilde_reflection_of_domain {D p : ℕ} [NeZero p]
    (c : ℝ) (ψ : DirichletCharacter ℂ p) (hψ : ψ.IsPrimitive) (hp : p ≠ 1)
    (Y : ℂ → ℂ) (hY : Lemma23ActualBranch ψ Y) {s : ℂ} (hs : 0 < s.im)
    (h₁ : 0 < s.im + lemma23PaperOffsetOne D c)
    (h₂ : 0 < s.im + lemma23PaperOffsetTwo D c)
    (h₃ : 0 < s.im + lemma23PaperOffsetThree D c) :
    lemma81ActualCtilde D c ψ Y (1-conj s) = -conj (lemma81ActualCtilde D c ψ Y s) := by
  simpa only [lemma81ActualCtilde,lemma52PaperBetaOne,lemma52PaperBetaTwo,
    lemma52PaperBetaThree] using lemma81_actual_normalized_quotient_reflection
      ψ hψ hp Y hY hs (lemma23PaperOffsetOne D c) (lemma23PaperOffsetTwo D c)
      (lemma23PaperOffsetThree D c) h₁ h₂ h₃

/-- The actual C̃ reflects throughout the original thin strip, uniformly
once the original fixed shift constant has been chosen. -/
theorem lemma81_uniform_Ctilde_reflection {c : ℝ} (hc : 0 < c) :
    ∃ D₀ : ℕ, lemma23SectionFourModulusThreshold ≤ D₀ ∧
    ∀ {D p : ℕ} [NeZero p] (ψ : DirichletCharacter ℂ p),
      D₀ ≤ D → Lemma23InPsi (D := D) ψ → ∀ Y : ℂ → ℂ,
      Lemma23ActualBranch ψ Y → ∀ {s : ℂ}, Lemma51InRegion D s →
      lemma81ActualCtilde D c ψ Y (1-conj s) = -conj (lemma81ActualCtilde D c ψ Y s) := by
  obtain ⟨N,hN,hsmall⟩ := lemma52_exists_shift_threshold hc
  refine ⟨N,hN,?_⟩
  intro D p _ ψ hD hψ Y hY s hs
  have hL := (lemma44_parameters_at_explicit_threshold (hN.trans hD)).1
  have hLp : 0 < lemma23PaperL D := by linarith
  have hT : 0 < lemma51PaperT0 D := by unfold lemma51PaperT0; positivity
  have hsExt : Lemma51InExtendedRegion D s := ⟨hs.1,by
    linarith only [hs.2,pow_nonneg hLp.le 405]⟩
  have hspos := hT.trans_le (lemma51_extended_region_data hL hsExt).2.2.1
  have hb := lemma52_offset_bounds hL hc (hsmall D hD)
  exact lemma81_Ctilde_reflection_of_domain c ψ hψ.2.1 hψ.1.ne_one Y hY hspos
    (by linarith only [hspos,hb.1.1]) (by linarith only [hspos,hb.2.1.1])
    (by linarith only [hspos,hb.2.2.1])

noncomputable def lemma81TildeIntegrand {p : ℕ} [NeZero p]
    (D : ℕ) (c : ℝ) (ψ : DirichletCharacter ℂ p) (Y : ℂ → ℂ)
    (a₁ a₂ : ℕ → ℂ) (s : ℂ) : ℂ :=
  lemma81ActualCtilde D c ψ Y s * lemma81Polynomial D a₁ ψ s *
    lemma81Polynomial D a₂ ψ⁻¹ (1-s) * lemma81Omega D s

/-- The actual upward-oriented normalized integral Ĩ₁ at horizontal offset x. -/
noncomputable def lemma81TildeIntegral {p : ℕ} [NeZero p]
    (D : ℕ) (c : ℝ) (ψ : DirichletCharacter ℂ p) (Y : ℂ → ℂ)
    (a₁ a₂ : ℕ → ℂ) (x : ℝ) : ℂ :=
  lemma81NormalizedSegmentIntegral D x (lemma81TildeIntegrand D c ψ Y a₁ a₂)

lemma lemma81_right_segment_point_in_region {D : ℕ}
    (hL : 3 ≤ lemma23PaperL D) {t : ℝ}
    (ht : t ∈ uIcc (-(lemma23PaperL D ^ 405)) (lemma23PaperL D ^ 405)) :
    Lemma51InRegion D (lemma81SegmentPoint D (lemma44PaperAlpha D) t) := by
  have hLp : 0 < lemma23PaperL D := by linarith
  have hH : 0 < lemma23PaperL D ^ 405 := pow_pos hLp 405
  rw [uIcc_of_le (by linarith only [hH])] at ht
  have hre : (lemma81SegmentPoint D (lemma44PaperAlpha D) t).re - 1 / 2 =
      lemma44PaperAlpha D := by simp [lemma81SegmentPoint,lemma23PaperCenter]
  have him : (lemma81SegmentPoint D (lemma44PaperAlpha D) t).im -
      (lemma23PaperCenter D).im = t := by simp [lemma81SegmentPoint]
  constructor
  · rw [hre,abs_of_nonneg (lemma44_alpha_pos_le_one hL).1.le]
  · rw [him]
    have hh : |t| ≤ lemma23PaperL D ^ 405 := abs_le.mpr ht
    linarith only [hh]

/-- The exact conjugate-and-swap relation on the two original contours.
The outer conjugation in this identity is essential to the full Lemma 8.1. -/
theorem lemma81_uniform_reflected_contour_identity {c : ℝ} (hc : 0 < c) :
    ∃ D₀ : ℕ, ∀ {D p : ℕ} [NeZero p] (ψ : DirichletCharacter ℂ p),
      D₀ ≤ D → Lemma23InPsi (D := D) ψ → ∀ Y : ℂ → ℂ,
      Lemma23ActualBranch ψ Y → ∀ a₁ a₂ : ℕ → ℂ,
      -lemma81TildeIntegral D c ψ Y a₁ a₂ (-lemma44PaperAlpha D) =
        conj (lemma81TildeIntegral D c ψ Y
          (lemma81ConjugateSequence a₂) (lemma81ConjugateSequence a₁) (lemma44PaperAlpha D)) := by
  obtain ⟨N,hN,href⟩ := lemma81_uniform_Ctilde_reflection hc
  refine ⟨N,?_⟩
  intro D p _ ψ hD hψ Y hY a₁ a₂
  have hL := (lemma44_parameters_at_explicit_threshold (hN.trans hD)).1
  let f := lemma81TildeIntegrand D c ψ Y a₁ a₂
  let g := lemma81TildeIntegrand D c ψ Y (lemma81ConjugateSequence a₂) (lemma81ConjugateSequence a₁)
  have hpoint (s : ℂ) (hs : Lemma51InRegion D s) : conj (f (1-conj s)) = -g s := by
    have hC := href ψ hD hψ Y hY hs
    have hP := lemma81_polynomial_weight_reflection D a₁ a₂ ψ (1-conj s)
    simp only [map_sub,map_one,conj_conj,sub_sub_cancel] at hP
    calc
      _ = -lemma81ActualCtilde D c ψ Y s *
        conj (lemma81Polynomial D a₁ ψ (1-conj s) *
          lemma81Polynomial D a₂ ψ⁻¹ (1-(1-conj s)) * lemma81Omega D (1-conj s)) := by
        dsimp [f,lemma81TildeIntegrand]
        rw [hC]
        simp only [map_mul,map_neg,conj_conj]
        ring
      _ = _ := by rw [sub_sub_cancel,hP]; dsimp [g,lemma81TildeIntegrand]; ring
  have hconj : conj (lemma81NormalizedSegmentIntegral D (-lemma44PaperAlpha D) f) =
      -lemma81NormalizedSegmentIntegral D (lemma44PaperAlpha D) g := by
    rw [lemma81_normalized_segment_conjugation,neg_neg]
    unfold lemma81NormalizedSegmentIntegral
    have he : (∫ t in (-(lemma23PaperL D ^ 405))..(lemma23PaperL D ^ 405),
        conj (f (1-conj (lemma81SegmentPoint D (lemma44PaperAlpha D) t)))) =
        ∫ t in (-(lemma23PaperL D ^ 405))..(lemma23PaperL D ^ 405),
          -g (lemma81SegmentPoint D (lemma44PaperAlpha D) t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact hpoint _ (lemma81_right_segment_point_in_region hL ht)
    dsimp only
    rw [he,intervalIntegral.integral_neg]
    ring
  have hfinal := congrArg conj hconj
  simp only [conj_conj,map_neg] at hfinal
  change -lemma81NormalizedSegmentIntegral D (-lemma44PaperAlpha D) f =
    conj (lemma81NormalizedSegmentIntegral D (lemma44PaperAlpha D) g)
  linear_combination -hfinal

end ZhangLS.Spec
