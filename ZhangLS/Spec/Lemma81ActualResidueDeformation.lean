import ZhangLS.Spec.Lemma81HeightAdjustment

/-! # Actual residue sum to the original two vertical contours

The selected zero-free rectangle contains exactly the original strict zero
window. All six edge errors are proved for the actual functions, including
both sides of the two height perturbations.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex ComplexConjugate Set MeasureTheory
open scoped Real Classical
set_option maxHeartbeats 2000000

/-- The actual finite zero sum differs negligibly from the original upward
right integral minus the original upward left integral, uniformly per good
character, branch and pair of admissible coefficient sequences. -/
theorem lemma81_uniform_actual_residue_to_segments {c : ℝ} (hc : 0 < c)
    (hcompatible : Lemma52CompatibleConstant c)
    {B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, lemma23SectionFourModulusThreshold ≤ N ∧
      ∀ {D p : ℕ} [NeZero p] (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p),
      N ≤ D → Lemma23InPsi1 χ ψ → ∀ Y : ℂ → ℂ, Lemma23ActualBranch ψ Y →
      ∀ a₁ a₂ : ℕ → ℂ, Lemma81AdmissibleSequence D B₁ a₁ →
      Lemma81AdmissibleSequence D B₂ a₂ →
      ‖(∑ ρ ∈ lemma81ZeroFinset D ψ, lemma81ActualResidueWeight D c ψ Y a₁ a₂ ρ)-
        (lemma81TildeIntegral D c ψ Y a₁ a₂ (lemma44PaperAlpha D)-
          lemma81TildeIntegral D c ψ Y a₁ a₂ (-lemma44PaperAlpha D))‖ ≤ ε := by
  obtain ⟨Nr,hrect⟩ := lemma81_actual_rectangle_residue_identity hc hcompatible
  obtain ⟨Ni,hNi,hint⟩ := lemma81_uniform_extended_vertical_integrability hc
  obtain ⟨Ns,hNs,hsep⟩ := lemma81_uniform_extended_contour_separation
  obtain ⟨Nb,hNb,hbound⟩ := lemma81_uniform_actual_boundary_integrands_small hc hB₁ hB₂
    (ε/6) (by positivity)
  refine ⟨max Nr (max Ni (max Ns Nb)),hNb.trans
    ((le_max_right Ns Nb).trans ((le_max_right Ni (max Ns Nb)).trans (le_max_right Nr _))),?_⟩
  intro D p _ χ ψ hD hψ Y hY a₁ a₂ ha₁ ha₂
  have hDr := (le_max_left Nr (max Ni (max Ns Nb))).trans hD
  have hDi := (le_max_left Ni (max Ns Nb)).trans ((le_max_right Nr _).trans hD)
  have hDs := (le_max_left Ns Nb).trans ((le_max_right Ni _).trans ((le_max_right Nr _).trans hD))
  have hDb := (le_max_right Ns Nb).trans ((le_max_right Ni _).trans ((le_max_right Nr _).trans hD))
  have hL := (lemma44_parameters_at_explicit_threshold (hNb.trans hDb)).1
  have hLp : 0 < lemma23PaperL D := by linarith only [hL]
  have hH : 0 < lemma23PaperL D^405 := pow_pos hLp 405
  have ha := (lemma44_alpha_pos_le_one hL).1
  have haq := lemma51_alpha_le_quarter hL
  let A := (lemma23PaperCenter D).im-lemma23PaperL D^405
  let B := (lemma23PaperCenter D).im+lemma23PaperL D^405
  let a := 1/2-lemma44PaperAlpha D
  let b := 1/2+lemma44PaperAlpha D
  let f := lemma81TildeIntegrand D c ψ Y a₁ a₂
  have hab : a ≤ b := by dsimp [a,b]; linarith only [ha]
  have hwidth : b-a ≤ 1 := by dsimp [a,b]; linarith only [haq]
  have hA : |A-(lemma23PaperCenter D).im| = lemma23PaperL D^405 := by
    dsimp [A]; rw [sub_sub_cancel_left,abs_neg,abs_of_pos hH]
  have hB : |B-(lemma23PaperCenter D).im| = lemma23PaperL D^405 := by
    dsimp [B]; rw [add_sub_cancel_left,abs_of_pos hH]
  obtain ⟨lo,hi,hlo,hhi,horder,hboundary,hres⟩ := hrect χ ψ hDr hψ Y hY a₁ a₂
  have hlnear : |lo-A| ≤ 1 := hlo.trans (by linarith only [haq])
  have hunear : |hi-B| ≤ 1 := hhi.trans (by linarith only [haq])
  have hlot := lemma81_height_band_of_near_endpoint hA hlnear
  have hhit := lemma81_height_band_of_near_endpoint hB hunear
  have hsmall (s : ℂ) (hthin : |s.re-1/2| ≤ lemma44PaperAlpha D)
      (hse : Lemma59ZeroSeparated (D := D) ψ s (1/4))
      (hband : lemma23PaperL D^405-1 ≤ |s.im-(lemma23PaperCenter D).im| ∧
        |s.im-(lemma23PaperCenter D).im| ≤ lemma23PaperL D^405+1) : ‖f s‖ ≤ ε/6 := by
    have hw : Lemma81WideStrip D s := ⟨by linarith only [(abs_le.mp hthin).1],
      by linarith only [(abs_le.mp hthin).2,haq],hband.2⟩
    exact (hbound χ ψ hDb hψ a₁ a₂ ha₁ ha₂ s hw hse hband.1).2 Y hY hthin
  have hhorizontal (t : ℝ) (ht : t = lo ∨ t = hi) :
      ‖∫ x in a..b, f ((x : ℂ)+(t : ℂ)*I)‖ ≤ ε/6 := by
    have hpoint (x : ℝ) (hx : x ∈ Icc a b) : ‖f ((x : ℂ)+(t : ℂ)*I)‖ ≤ ε/6 := by
      have hre : ((x : ℂ)+(t : ℂ)*I).re = x := by simp
      have him : ((x : ℂ)+(t : ℂ)*I).im = t := by simp
      have hthin : |((x : ℂ)+(t : ℂ)*I).re-1/2| ≤ lemma44PaperAlpha D := by
        rw [hre]
        dsimp [a,b] at hx
        exact abs_le.mpr ⟨by linarith only [hx.1],by linarith only [hx.2]⟩
      have hbdy : Lemma81RectangleBoundary D lo hi ((x : ℂ)+(t : ℂ)*I) := by
        refine ⟨⟨hthin,?_,?_⟩,?_⟩
        · rw [him]; rcases ht with rfl | rfl <;> linarith only [horder]
        · rw [him]; rcases ht with rfl | rfl <;> linarith only [horder]
        · exact Or.inr (by simpa only [him] using ht)
      apply hsmall _ hthin (hboundary _ hbdy)
      rw [him]
      rcases ht with rfl | rfl
      · exact hlot
      · exact hhit
    apply (intervalIntegral.norm_integral_le_of_norm_le_const
      (fun x hx => hpoint x (by simpa only [uIcc_of_le hab] using uIoc_subset_uIcc hx))).trans
    rw [abs_of_nonneg (sub_nonneg.mpr hab)]
    exact mul_le_of_le_one_right (by positivity) hwidth
  have hvertical (σ : ℝ) (hσ : |σ-1/2| = lemma44PaperAlpha D) :
      ‖(∫ t in lo..hi, f ((σ : ℂ)+(t : ℂ)*I))-
        (∫ t in A..B, f ((σ : ℂ)+(t : ℂ)*I))‖ ≤ 2*(ε/6) := by
    have hi' (u v : ℝ) (hu : |u-(lemma23PaperCenter D).im| ≤ lemma23PaperL D^405+1)
        (hv : |v-(lemma23PaperCenter D).im| ≤ lemma23PaperL D^405+1) :
        IntervalIntegrable (fun t => f ((σ : ℂ)+(t : ℂ)*I)) volume u v :=
      hint χ ψ hDi hψ Y hY a₁ a₂ σ u v hσ hu hv
    have htail (t e : ℝ) (he : |e-(lemma23PaperCenter D).im| = lemma23PaperL D^405)
        (hte : |t-e| ≤ 1) : ‖f ((σ : ℂ)+(t : ℂ)*I)‖ ≤ ε/6 := by
      have hre : ((σ : ℂ)+(t : ℂ)*I).re = σ := by simp
      have him : ((σ : ℂ)+(t : ℂ)*I).im = t := by simp
      have hband := lemma81_height_band_of_near_endpoint he hte
      have hse := (hsep χ ψ hDs hψ).2 ((σ : ℂ)+(t : ℂ)*I)
        (by rw [hre]; exact hσ) (by rw [him]; exact hband.2)
      exact hsmall _ (by rw [hre,hσ]) (lemma81_zero_separated_quarter_of_one hL ψ hse)
        (by rw [him]; exact hband)
    apply lemma81_integral_height_change_bound _ (by positivity) hlnear hunear
      (hi' lo A hlot.2 (by rw [hA]; linarith))
      (hi' A B (by rw [hA]; linarith) (by rw [hB]; linarith))
      (hi' B hi (by rw [hB]; linarith) hhit.2)
    · intro t ht
      apply htail t A hA
      have hh := abs_sub_right_of_mem_uIcc ht
      rw [abs_sub_comm A t,abs_sub_comm A lo] at hh
      exact hh.trans hlnear
    · intro t ht
      exact htail t B hB ((abs_sub_left_of_mem_uIcc ht).trans hunear)
  have ht := lemma81_rectangle_truncation_bound f (by positivity : 0 ≤ ε/6)
    (hhorizontal lo (Or.inl rfl)) (hhorizontal hi (Or.inr rfl))
    (hvertical a (by dsimp [a]; rw [sub_sub_cancel_left,abs_neg,abs_of_pos ha]))
    (hvertical b (by dsimp [b]; rw [add_sub_cancel_left,abs_of_pos ha]))
  rw [hres] at ht
  unfold lemma81TildeIntegral
  rw [lemma81_normalized_segment_eq_vertical,lemma81_normalized_segment_eq_vertical,← mul_sub]
  have haeq : (1/2 : ℝ)+ -lemma44PaperAlpha D = a := by dsimp [a]; ring
  rw [haeq]
  exact ht.trans_eq (by ring)

/-- Aggregate residue-to-reflected-contour comparison, normalized directly
by the genuine prime mass and uniform over every genuine square-root branch. -/
theorem lemma81_actual_residue_deformation_littleO {c : ℝ} (hc : 0 < c)
    (hcompatible : Lemma52CompatibleConstant c)
    {B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ D : ℕ, N ≤ D →
      ∀ (χ : RealPrimitiveCharacter D) (a₁ a₂ : ℕ → ℂ),
      Lemma81AdmissibleSequence D B₁ a₁ → Lemma81AdmissibleSequence D B₂ a₂ →
      ∀ Y : (ψ : lemma33CharacterIndex D) → ℂ → ℂ,
      (∀ ψ ∈ lemma81GoodFamily χ, Lemma23ActualBranch ψ.2 (Y ψ)) →
      ‖lemma81DiscreteMean χ c Y a₁ a₂-
        (∑ ψ ∈ lemma81GoodFamily χ, lemma81TildeIntegral D c ψ.2 (Y ψ) a₁ a₂ (lemma44PaperAlpha D))-
        conj (∑ ψ ∈ lemma81GoodFamily χ, lemma81TildeIntegral D c ψ.2 (Y ψ)
          (lemma81ConjugateSequence a₂) (lemma81ConjugateSequence a₁) (lemma44PaperAlpha D))‖ ≤
        ε*lemma33ActualPrimeMass D := by
  intro ε hε
  obtain ⟨Ne,hNe,he⟩ := lemma81_uniform_actual_residue_to_segments hc hcompatible hB₁ hB₂ ε hε
  obtain ⟨Nr,href⟩ := lemma81_uniform_reflected_contour_identity hc
  refine ⟨max Ne Nr,?_⟩
  intro D hD χ a₁ a₂ ha₁ ha₂ Y hY
  have hDe := (le_max_left Ne Nr).trans hD
  have hDr := (le_max_right Ne Nr).trans hD
  have hL := (lemma44_parameters_at_explicit_threshold (hNe.trans hDe)).1
  have hpoint (ψ : lemma33CharacterIndex D) (hψ : ψ ∈ lemma81GoodFamily χ) :
      ‖(∑ ρ ∈ lemma81ZeroFinset D ψ.2, lemma81ActualResidueWeight D c ψ.2 (Y ψ) a₁ a₂ ρ)-
        lemma81TildeIntegral D c ψ.2 (Y ψ) a₁ a₂ (lemma44PaperAlpha D)-
        conj (lemma81TildeIntegral D c ψ.2 (Y ψ)
          (lemma81ConjugateSequence a₂) (lemma81ConjugateSequence a₁) (lemma44PaperAlpha D))‖ ≤ ε := by
    have hg := (lemma81_mem_good_family χ ψ).mp hψ
    have hh := he χ ψ.2 hDe hg (Y ψ) (hY ψ hψ) a₁ a₂ ha₁ ha₂
    have hr := href ψ.2 hDr hg.1 (Y ψ) (hY ψ hψ) a₁ a₂
    rw [← hr]
    convert hh using 1
    congr 1
    ring
  have heq : lemma81DiscreteMean χ c Y a₁ a₂-
      (∑ ψ ∈ lemma81GoodFamily χ, lemma81TildeIntegral D c ψ.2 (Y ψ) a₁ a₂ (lemma44PaperAlpha D))-
      conj (∑ ψ ∈ lemma81GoodFamily χ, lemma81TildeIntegral D c ψ.2 (Y ψ)
        (lemma81ConjugateSequence a₂) (lemma81ConjugateSequence a₁) (lemma44PaperAlpha D)) =
      ∑ ψ ∈ lemma81GoodFamily χ, ((∑ ρ ∈ lemma81ZeroFinset D ψ.2,
        lemma81ActualResidueWeight D c ψ.2 (Y ψ) a₁ a₂ ρ)-
        lemma81TildeIntegral D c ψ.2 (Y ψ) a₁ a₂ (lemma44PaperAlpha D)-
        conj (lemma81TildeIntegral D c ψ.2 (Y ψ)
          (lemma81ConjugateSequence a₂) (lemma81ConjugateSequence a₁) (lemma44PaperAlpha D))) := by
    simp only [lemma81DiscreteMean,lemma81ActualResidueWeight,map_sum,Finset.sum_sub_distrib]
  rw [heq]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ ψ ∈ lemma81GoodFamily χ, ε := Finset.sum_le_sum hpoint
    _ = ε*((lemma81GoodFamily χ).card : ℝ) := by simp only [Finset.sum_const,nsmul_eq_mul]; ring
    _ ≤ ε*lemma33ActualPrimeMass D := mul_le_mul_of_nonneg_left
      (lemma81_actual_good_family_card_le_mass hL χ) hε.le

end ZhangLS.Spec
