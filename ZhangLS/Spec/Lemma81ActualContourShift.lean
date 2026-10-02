import ZhangLS.Spec.Lemma81DeformationGeometry
import ZhangLS.Spec.Lemma81ReplacementLittleO

/-! # The actual J(alpha) to J(1) deformation

Cauchy's theorem is applied to the genuine C integrand on the full closed
rectangle. The horizontal errors are proved with the original Gaussian and
are aggregated against the actual prime mass directly by cardinality.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Set MeasureTheory
open scoped Real Classical
set_option maxHeartbeats 2000000

lemma lemma81_rectangle_vertical_difference_bound (f : ℂ → ℂ)
    {a b lo hi δ : ℝ} (hab : a ≤ b) (hwidth : b-a ≤ 1) (hδ : 0 ≤ δ)
    (hzero : lemma81RectangleIntegral f a b lo hi = 0)
    (hbottom : ∀ x ∈ Icc a b, ‖f ((x : ℂ)+(lo : ℂ)*I)‖ ≤ δ)
    (htop : ∀ x ∈ Icc a b, ‖f ((x : ℂ)+(hi : ℂ)*I)‖ ≤ δ) :
    ‖(∫ y in lo..hi, f ((a : ℂ)+(y : ℂ)*I)) -
      (∫ y in lo..hi, f ((b : ℂ)+(y : ℂ)*I))‖ ≤ 2*δ := by
  have hb : ‖∫ x in a..b, f ((x : ℂ)+(lo : ℂ)*I)‖ ≤ δ := by
    apply (intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx => ?_)).trans
    · rw [abs_of_nonneg (sub_nonneg.mpr hab)]
      exact mul_le_of_le_one_right hδ hwidth
    · exact hbottom x ⟨(uIoc_of_le hab ▸ hx).1.le,(uIoc_of_le hab ▸ hx).2⟩
  have ht : ‖∫ x in a..b, f ((x : ℂ)+(hi : ℂ)*I)‖ ≤ δ := by
    apply (intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx => ?_)).trans
    · rw [abs_of_nonneg (sub_nonneg.mpr hab)]
      exact mul_le_of_le_one_right hδ hwidth
    · exact htop x ⟨(uIoc_of_le hab ▸ hx).1.le,(uIoc_of_le hab ▸ hx).2⟩
  have he : I*((∫ y in lo..hi, f ((a : ℂ)+(y : ℂ)*I)) -
      (∫ y in lo..hi, f ((b : ℂ)+(y : ℂ)*I))) =
      (∫ x in a..b, f ((x : ℂ)+(lo : ℂ)*I)) -
      (∫ x in a..b, f ((x : ℂ)+(hi : ℂ)*I)) := by
    unfold lemma81RectangleIntegral at hzero
    linear_combination -hzero
  have hn := congrArg norm he
  simp only [norm_mul,norm_I,one_mul] at hn
  rw [hn]
  exact (norm_sub_le _ _).trans (by linarith only [hb,ht])

/-- Per actual good character, the full contour deformation error tends to
zero uniformly in all admissible coefficients. -/
theorem lemma81_uniform_actual_C_shift_pointwise {c : ℝ} (hc : 0 < c)
    {B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, lemma23SectionFourModulusThreshold ≤ N ∧
      ∀ {D p : ℕ} [NeZero p] (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p),
      N ≤ D → Lemma23InPsi1 χ ψ → ∀ a₁ a₂ : ℕ → ℂ,
      Lemma81AdmissibleSequence D B₁ a₁ → Lemma81AdmissibleSequence D B₂ a₂ →
      ‖lemma81CIntegral D c ψ a₁ a₂ (lemma44PaperAlpha D)-
        lemma81CIntegral D c ψ a₁ a₂ 1‖ ≤ ε := by
  obtain ⟨Ns,hNs,hsep⟩ := lemma81_uniform_extended_contour_separation
  obtain ⟨Nb,hNb,hbound⟩ := lemma81_uniform_actual_boundary_integrands_small hc hB₁ hB₂
    (ε/2) (by positivity)
  obtain ⟨No,hNo,hoff⟩ := lemma52_exists_shift_threshold hc
  refine ⟨max Ns (max Nb No),hNs.trans (le_max_left _ _),?_⟩
  intro D p _ χ ψ hD hψ a₁ a₂ ha₁ ha₂
  have hDs := (le_max_left Ns (max Nb No)).trans hD
  have hDb := (le_max_left Nb No).trans ((le_max_right Ns (max Nb No)).trans hD)
  have hDo := (le_max_right Nb No).trans ((le_max_right Ns (max Nb No)).trans hD)
  have hL := (lemma44_parameters_at_explicit_threshold (hNs.trans hDs)).1
  have hLp : 0 < lemma23PaperL D := by linarith only [hL]
  have hH : 0 < lemma23PaperL D^405 := pow_pos hLp 405
  have ha := (lemma44_alpha_pos_le_one hL).1
  have haq := lemma51_alpha_le_quarter hL
  have ho := lemma52_offset_bounds hL hc (hoff D hDo)
  let a := 1/2+lemma44PaperAlpha D
  let b : ℝ := 1/2+1
  let lo := (lemma23PaperCenter D).im-lemma23PaperL D^405
  let hi := (lemma23PaperCenter D).im+lemma23PaperL D^405
  have hab : a ≤ b := by dsimp [a,b]; linarith only [haq]
  have hlh : lo ≤ hi := by dsimp [lo,hi]; linarith only [hH]
  have hheight {s : ℂ} (hs : s.im ∈ Icc lo hi) :
      |s.im-(lemma23PaperCenter D).im| ≤ lemma23PaperL D^405 := by
    dsimp [lo,hi] at hs
    exact abs_le.mpr ⟨by linarith only [hs.1],by linarith only [hs.2]⟩
  have han : DifferentiableOn ℂ (lemma81CIntegrand D c ψ a₁ a₂) (Icc a b ×ℂ Icc lo hi) := by
    intro s hs
    have ht := hheight hs.2
    have hwide : |s.im-(lemma23PaperCenter D).im| ≤ 2*lemma23PaperL D^405+3 := by
      linarith only [ht,hH]
    have hspos : 0 < s.im := by linarith only [(lemma61_wide_height_data hL hwide).2.1]
    have hsep' := (hsep χ ψ hDs hψ).1 s hs.1.1 (by linarith only [ht])
    have hne : ψ.LFunction s ≠ 0 := by
      intro hz
      have hh := hsep' s hz
      simp only [one_mul,sub_self,norm_zero] at hh
      exact (not_le_of_gt ha) hh
    exact (lemma81_actual_C_integrand_analyticAt c ψ hψ.1.2.1 hψ.1.1.ne_one a₁ a₂ hspos hne
      (by linarith only [hspos,ho.1.1]) (by linarith only [hspos,ho.2.1.1])
      (by linarith only [hspos,ho.2.2.1])).differentiableAt.differentiableWithinAt
  have hedge (x t : ℝ) (hx : x ∈ Icc a b) (ht : t = lo ∨ t = hi) :
      ‖lemma81CIntegrand D c ψ a₁ a₂ ((x : ℂ)+(t : ℂ)*I)‖ ≤ ε/2 := by
    have hre : ((x : ℂ)+(t : ℂ)*I).re = x := by simp
    have him : ((x : ℂ)+(t : ℂ)*I).im = t := by simp
    have habs : |t-(lemma23PaperCenter D).im| = lemma23PaperL D^405 := by
      rcases ht with rfl | rfl <;> dsimp [lo,hi]
      · rw [sub_sub_cancel_left,abs_neg,abs_of_pos hH]
      · rw [add_sub_cancel_left,abs_of_pos hH]
    have hw : Lemma81WideStrip D ((x : ℂ)+(t : ℂ)*I) := by
      change 1/2-lemma44PaperAlpha D ≤ _ ∧ _ ≤ 3/2 ∧ _ ≤ _
      rw [hre,him,habs]
      dsimp [a,b] at hx
      exact ⟨by linarith only [hx.1,ha],by linarith only [hx.2],by linarith⟩
    have hs := (hsep χ ψ hDs hψ).1 ((x : ℂ)+(t : ℂ)*I)
      (by rw [hre]; exact hx.1) (by rw [him,habs]; linarith)
    exact (hbound χ ψ hDb hψ a₁ a₂ ha₁ ha₂ _ hw
      (lemma81_zero_separated_quarter_of_one hL ψ hs) (by rw [him,habs]; linarith)).1
  have hvert := lemma81_rectangle_vertical_difference_bound (lemma81CIntegrand D c ψ a₁ a₂)
    hab (by dsimp [a,b]; linarith only [ha] : b-a ≤ 1) (by positivity : 0 ≤ ε/2)
    (lemma81_rectangle_cauchy _ hab hlh han)
    (fun x hx => hedge x lo hx (Or.inl rfl)) (fun x hx => hedge x hi hx (Or.inr rfl))
  unfold lemma81CIntegral
  rw [lemma81_normalized_segment_eq_vertical,lemma81_normalized_segment_eq_vertical,← mul_sub,norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) lemma81_normalization_factor_norm_le_one).trans
    (hvert.trans_eq (by ring))

/-- The genuine J(alpha) to J(1) shift has o(actual prime mass) total error,
without any appeal to Assumption (A) or a guessed prime-counting rate. -/
theorem lemma81_actual_C_shift_littleO {c : ℝ} (hc : 0 < c)
    {B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ D : ℕ, N ≤ D →
      ∀ (χ : RealPrimitiveCharacter D) (a₁ a₂ : ℕ → ℂ),
      Lemma81AdmissibleSequence D B₁ a₁ → Lemma81AdmissibleSequence D B₂ a₂ →
      ‖(∑ ψ ∈ lemma81GoodFamily χ,
          lemma81CIntegral D c ψ.2 a₁ a₂ (lemma44PaperAlpha D))-
        lemma81ThetaOne χ c a₁ a₂‖ ≤ ε*lemma33ActualPrimeMass D := by
  intro ε hε
  obtain ⟨N,hN,he⟩ := lemma81_uniform_actual_C_shift_pointwise hc hB₁ hB₂ ε hε
  refine ⟨N,?_⟩
  intro D hD χ a₁ a₂ ha₁ ha₂
  have hL := (lemma44_parameters_at_explicit_threshold (hN.trans hD)).1
  rw [lemma81_ThetaOne_eq_sum_CIntegral,← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ ψ ∈ lemma81GoodFamily χ, ε := Finset.sum_le_sum (fun ψ hψ =>
      he χ ψ.2 hD ((lemma81_mem_good_family χ ψ).mp hψ) a₁ a₂ ha₁ ha₂)
    _ = ε*((lemma81GoodFamily χ).card : ℝ) := by simp only [Finset.sum_const,nsmul_eq_mul]; ring
    _ ≤ ε*lemma33ActualPrimeMass D := mul_le_mul_of_nonneg_left
      (lemma81_actual_good_family_card_le_mass hL χ) hε.le

end ZhangLS.Spec
