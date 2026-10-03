import ZhangLS.Spec.Lemma162ActualMellinResidues

/-! A source-tied quantitative obligation. The V bound and its center error
are discharged by the accepted center package. The remaining zeta/L/Gaussian
factor bound and the complete cubic-jet discrepancy remain explicit. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Metric Set
set_option maxHeartbeats 1000000

/-- Every actual numerator factor other than V, including the exact smoothing. -/
noncomputable def lemma162MellinOtherFactors {D : ℕ} (χ : RealPrimitiveCharacter D)
    (γ w : ℂ) : ℂ :=
  lemma57RegularizedZeta w^2*lemma57RegularizedZeta (w-γ)*
    dirichletLFunction χ (1+w)*dirichletLFunction χ (1+w-γ)^2*
      lemma162MellinSmoothing D w

theorem lemma162_mellin_numerator_factors {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β γ w : ℂ) :
    lemma162MellinNumerator χ β γ w =
      lemma162CorrectedEulerProduct χ β γ (1+w)*lemma162MellinOtherFactors χ γ w := by
  unfold lemma162MellinNumerator lemma162MellinOtherFactors
  ring

/-- All smoothing derivatives and all derivatives of both shifted L factors
and of zeta and V are retained in this genuine derivative, not replaced by
the printed L'(1)^3 shortcut. -/
noncomputable def lemma162MellinJetDiscrepancy {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β γ : ℂ) : ℝ :=
  ‖iteratedDeriv 3 (lemma162MellinNumerator χ β γ) 0/6-
    lemma162CorrectedEulerProduct χ β γ 1*LDerivAtOne χ^3‖

theorem lemma162_cauchy_log_budget {L g M : ℝ} (hL : 0<L) (hg : 0≤g)
    (hM : 0≤M) (hsmall : g<(10*L)⁻¹/2) (hglog : g≤3*Real.pi/L^9) :
    M*g/(((10*L)⁻¹)^3*((10*L)⁻¹-g))≤60000*Real.pi*M/L^5 := by
  have hR : 0<(10*L)⁻¹ := inv_pos.mpr (by positivity)
  have hgap : (10*L)⁻¹/2≤(10*L)⁻¹-g := by linarith
  calc
    _ ≤ M*g/(((10*L)⁻¹)^3*((10*L)⁻¹/2)) :=
      div_le_div₀ (mul_nonneg hM hg) le_rfl
        (by positivity) (mul_le_mul_of_nonneg_left hgap (by positivity))
    _ ≤ M*(3*Real.pi/L^9)/(((10*L)⁻¹)^3*((10*L)⁻¹/2)) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hglog hM) (by positivity)
    _ = _ := by field_simp; ring

/-- The actual residue/main comparison with the exact, unsolved jet term
shown. B bounds the ordinary actual zeta/L/smoothing product on the circle;
it is not a hypothesis asserting the desired final error. -/
theorem lemma162_paper_mellin_budget (c : ℝ) (hc : 0<c) :
    ∃ D₀ : ℕ, 3≤D₀ ∧ lemma23SectionFourModulusThreshold≤D₀ ∧
      ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D, ∀ j : Fin 2,
        let β := lemma52PaperBetaOne D c
        let γ := lemma162PaperShift D c j
        let H := lemma162MellinNumerator χ β γ
        ∀ B : ℝ, 0≤B →
          (∀ w∈sphere (0 : ℂ) (lemma162MellinRadius D), ‖lemma162MellinOtherFactors χ γ w‖≤B) →
          ‖lemma162ThirdDividedDifference H γ-lemma162CorrectedCenterMain χ*LDerivAtOne χ^3‖≤
            60000*Real.pi*lemma162SectorConstant*B/lemma23PaperL D^5 +
            lemma162MellinJetDiscrepancy χ β γ +
            (lemma162CorrectedCenterAlphaConstant*Real.pi)*‖LDerivAtOne χ‖^3/lemma23PaperL D^9 := by
  obtain ⟨D₁,hD₁,hs₁,hquant⟩ := lemma162_corrected_quantitative_proved c hc
  obtain ⟨D₂,hs₂,hshift⟩ := lemma52_exists_shift_threshold hc
  refine ⟨max D₁ D₂,hD₁.trans (le_max_left _ _),hs₁.trans (le_max_left _ _),?_⟩
  intro D hD χ j
  dsimp only
  intro B hB0 hB
  have h1 : D₁≤D := (le_max_left _ _).trans hD
  have h2 : D₂≤D := (le_max_right _ _).trans hD
  have hd : 1<D := by have := hD₁.trans h1; omega
  have hL := (lemma44_parameters_at_explicit_threshold (hs₁.trans h1)).1
  have hL0 : 0<lemma23PaperL D := by linarith
  obtain ⟨hγ0,hγlog,hγsmall,hR,hRsmall⟩ :=
    lemma162_paper_mellin_geometry hc hL (hshift D h2) j
  have hγR : ‖lemma162PaperShift D c j‖<lemma162MellinRadius D := by linarith
  obtain ⟨_,_,hdisk,_,hcenter⟩ := hquant D h1 χ j
  have hnum : ∀ w∈sphere (0 : ℂ) (lemma162MellinRadius D),
      ‖lemma162MellinNumerator χ (lemma52PaperBetaOne D c) (lemma162PaperShift D c j) w‖≤
        lemma162SectorConstant*B := by
    intro w hw
    rw [lemma162_mellin_numerator_factors,norm_mul]
    apply mul_le_mul (hdisk (1+w) ?_) (hB w hw) (norm_nonneg _) lemma162_sector_constant_pos.le
    have hwR : ‖w‖=lemma162MellinRadius D := by simpa using mem_sphere_iff_norm.mp hw
    simpa [lemma162MellinRadius] using hwR.le
  have herr := lemma162_third_divided_difference_cubic_error
    (lemma162MellinNumerator χ (lemma52PaperBetaOne D c) (lemma162PaperShift D c j)) hγ0 hγR
    (lemma162_mellin_numerator_disk χ hd _ (lemma161_paper_beta_re D c) _
      (lemma162_paper_shift_re D c j) (by simp) hRsmall).differentiableOn hnum
  have herr' := herr.trans (lemma162_cauchy_log_budget hL0 (norm_nonneg _)
    (mul_nonneg lemma162_sector_constant_pos.le hB0) hγsmall hγlog)
  have hcmain : ‖lemma162CorrectedEulerProduct χ (lemma52PaperBetaOne D c)
      (lemma162PaperShift D c j) 1*LDerivAtOne χ^3-
      lemma162CorrectedCenterMain χ*LDerivAtOne χ^3‖≤
      (lemma162CorrectedCenterAlphaConstant*Real.pi)*‖LDerivAtOne χ‖^3/lemma23PaperL D^9 := by
    rw [← sub_mul,norm_mul,norm_pow]
    calc
      _ ≤ ((lemma162CorrectedCenterAlphaConstant*Real.pi)/lemma23PaperL D^9)*‖LDerivAtOne χ‖^3 :=
        mul_le_mul_of_nonneg_right hcenter (by positivity)
      _ = _ := by ring
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (lemma162ThirdDividedDifference
      (lemma162MellinNumerator χ (lemma52PaperBetaOne D c) (lemma162PaperShift D c j))
      (lemma162PaperShift D c j))
    (iteratedDeriv 3 (lemma162MellinNumerator χ (lemma52PaperBetaOne D c)
      (lemma162PaperShift D c j)) 0/6)
    (lemma162CorrectedCenterMain χ*LDerivAtOne χ^3)
  have ht2 := norm_sub_le_norm_sub_add_norm_sub
    (iteratedDeriv 3 (lemma162MellinNumerator χ (lemma52PaperBetaOne D c)
      (lemma162PaperShift D c j)) 0/6)
    (lemma162CorrectedEulerProduct χ (lemma52PaperBetaOne D c) (lemma162PaperShift D c j) 1*LDerivAtOne χ^3)
    (lemma162CorrectedCenterMain χ*LDerivAtOne χ^3)
  have htotal := ht.trans (add_le_add herr' (ht2.trans (add_le_add (le_refl _) hcmain)))
  simpa only [lemma162MellinJetDiscrepancy,mul_assoc,add_assoc] using htotal

end ZhangLS.Spec
