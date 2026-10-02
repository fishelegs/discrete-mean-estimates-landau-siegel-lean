import ZhangLS.Spec.Lemma81BoundaryIntegrandsSmall
import ZhangLS.Spec.Lemma81ActualRectangleResidues

/-! # Actual zero separation and coordinates for the remaining deformations -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Set
open scoped Real Classical
set_option maxHeartbeats 2000000

/-- The right slab and both thin vertical lines avoid every actual L-zero
uniformly throughout the slightly enlarged height window. -/
theorem lemma81_uniform_extended_contour_separation :
    ∃ N : ℕ, lemma23SectionFourModulusThreshold ≤ N ∧
      ∀ {D p : ℕ} [NeZero p] (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p),
      N ≤ D → Lemma23InPsi1 χ ψ →
      (∀ s : ℂ, 1/2+lemma44PaperAlpha D ≤ s.re →
        |s.im-(lemma23PaperCenter D).im| ≤ lemma23PaperL D^405+1 →
        Lemma59ZeroSeparated (D := D) ψ s 1) ∧
      (∀ s : ℂ, |s.re-1/2| = lemma44PaperAlpha D →
        |s.im-(lemma23PaperCenter D).im| ≤ lemma23PaperL D^405+1 →
        Lemma59ZeroSeparated (D := D) ψ s 1) := by
  obtain ⟨cz,hcz,Nz,hzero⟩ := lemma59_uniform_extended_actual_product_zeros
  refine ⟨max Nz lemma23SectionFourModulusThreshold,le_max_right _ _,?_⟩
  intro D p _ χ ψ hD hψ
  have hDz := (le_max_left Nz lemma23SectionFourModulusThreshold).trans hD
  have hsection := (le_max_right Nz lemma23SectionFourModulusThreshold).trans hD
  have hL := (lemma44_parameters_at_explicit_threshold hsection).1
  have ha := (lemma44_alpha_pos_le_one hL).1
  have haq := lemma51_alpha_le_quarter hL
  have hall := hzero χ ψ hDz hψ
  have hθ := lemma59_family_character_nonprincipal ψ hψ.1
  have hprod {ρ : ℂ} (hz : ψ.LFunction ρ = 0) : lemma48ActualProduct χ ψ ρ = 0 := by
    simp only [lemma48ActualProduct,hz,zero_mul]
  have him {s ρ : ℂ}
      (hs : |s.im-(lemma23PaperCenter D).im| ≤ lemma23PaperL D^405+1)
      (hn : ‖s-ρ‖ < lemma44PaperAlpha D) :
      |ρ.im-(lemma23PaperCenter D).im| < lemma23PaperL D^405+13 := by
    have hi : |ρ.im-s.im| ≤ ‖s-ρ‖ := by
      simpa only [sub_im,abs_sub_comm] using Complex.abs_im_le_norm (s-ρ)
    have hh := abs_add_le (ρ.im-s.im) (s.im-(lemma23PaperCenter D).im)
    rw [sub_add_sub_cancel] at hh
    linarith only [hh,hi,hs,hn,haq]
  constructor
  · intro s hsre hsheight ρ hz
    simp only [one_mul]
    by_contra hbad
    have hn : ‖s-ρ‖ < lemma44PaperAlpha D := lt_of_not_ge hbad
    have hre : s.re-ρ.re ≤ ‖s-ρ‖ :=
      (le_abs_self _).trans (by simpa only [sub_re] using Complex.abs_re_le_norm (s-ρ))
    have hrlo : 1/2 < ρ.re := by linarith only [hre,hsre,hn]
    by_cases hrhi : 1 ≤ ρ.re
    · exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ (Or.inl hθ) hrhi) hz
    · have hr : |ρ.re-1/2| < 1/2 := abs_lt.mpr
        ⟨by linarith only [hrlo],by linarith only [lt_of_not_ge hrhi]⟩
      have hc := (hall.2.2 ⟨hr,him hsheight hn⟩ (hprod hz)).1
      linarith only [hc,hrlo]
  · intro s hsre hsheight ρ hz
    simp only [one_mul]
    by_contra hbad
    have hn : ‖s-ρ‖ < lemma44PaperAlpha D := lt_of_not_ge hbad
    have hre : |ρ.re-s.re| ≤ ‖s-ρ‖ := by
      simpa only [sub_re,abs_sub_comm] using Complex.abs_re_le_norm (s-ρ)
    have hr : |ρ.re-1/2| < 1/2 := by
      have hh := abs_add_le (ρ.re-s.re) (s.re-1/2)
      rw [sub_add_sub_cancel,hsre] at hh
      linarith only [hh,hre,hn,haq]
    have hc := (hall.2.2 ⟨hr,him hsheight hn⟩ (hprod hz)).1
    have hh := Complex.abs_re_le_norm (s-ρ)
    rw [sub_re,hc,hsre] at hh
    exact (not_lt_of_ge hh) hn

lemma lemma81_zero_separated_quarter_of_one {D p : ℕ} [NeZero p]
    (hL : 3 ≤ lemma23PaperL D) (ψ : DirichletCharacter ℂ p) {s : ℂ}
    (hs : Lemma59ZeroSeparated (D := D) ψ s 1) :
    Lemma59ZeroSeparated (D := D) ψ s (1/4) := by
  intro ρ hz
  have hh := hs ρ hz
  simp only [one_mul] at hh
  linarith only [hh,(lemma44_alpha_pos_le_one hL).1]

/-- Exact conversion of the upward relative-height segment to absolute
vertical coordinates, preserving its orientation and normalization. -/
lemma lemma81_normalized_segment_eq_vertical (D : ℕ) (x : ℝ) (f : ℂ → ℂ) :
    lemma81NormalizedSegmentIntegral D x f =
      ((2*Real.pi : ℝ) : ℂ)⁻¹ *
        (∫ t in ((lemma23PaperCenter D).im-lemma23PaperL D^405)..
          ((lemma23PaperCenter D).im+lemma23PaperL D^405),
          f (((1/2+x : ℝ) : ℂ)+(t : ℂ)*I)) := by
  have hp (t : ℝ) : lemma81SegmentPoint D x t =
      (((1/2+x : ℝ) : ℂ)+((t+(lemma23PaperCenter D).im : ℝ) : ℂ)*I) := by
    apply Complex.ext <;> simp only [lemma81SegmentPoint,add_re,add_im,mul_re,mul_im,
      ofReal_re,ofReal_im,I_re,I_im,zero_mul,mul_zero,one_mul,mul_one,sub_zero,add_zero,zero_add]
    · rfl
    · ring
  unfold lemma81NormalizedSegmentIntegral
  simp_rw [hp]
  change ((2*Real.pi : ℝ) : ℂ)⁻¹ *
      (∫ t in -(lemma23PaperL D^405)..lemma23PaperL D^405,
        (fun y : ℝ => f (((1/2+x : ℝ) : ℂ)+(y : ℂ)*I))
          (t+(lemma23PaperCenter D).im)) = _
  rw [intervalIntegral.integral_comp_add_right
    (fun y : ℝ => f (((1/2+x : ℝ) : ℂ)+(y : ℂ)*I))
    ((lemma23PaperCenter D).im)]
  rw [show -(lemma23PaperL D^405)+(lemma23PaperCenter D).im =
      (lemma23PaperCenter D).im-lemma23PaperL D^405 by ring,
    show lemma23PaperL D^405+(lemma23PaperCenter D).im =
      (lemma23PaperCenter D).im+lemma23PaperL D^405 by ring]

end ZhangLS.Spec
