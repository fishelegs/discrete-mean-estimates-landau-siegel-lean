import ZhangLS.Spec.Lemma162MellinNumerator
import ZhangLS.Spec.Lemma162CauchyCancellation

/-! Both local residues and their sum for the actual source integrand.
The circles are proved legal for both original finite-D shifts. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Metric Set
set_option maxHeartbeats 1000000

noncomputable def lemma162MellinRadius (D : ℕ) : ℝ := (10*lemma23PaperL D)⁻¹

theorem lemma162_mellin_numerator_disk {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (β : ℂ) (hβ : β.re=0) (γ : ℂ) (hγ : γ.re=0)
    {a : ℂ} (ha : a.re=0) {R : ℝ} (hR : R<1/10) :
    AnalyticOnNhd ℂ (lemma162MellinNumerator χ β γ) (closedBall a R) := by
  intro w hw
  apply lemma162_mellin_numerator_analytic χ hD β hβ γ hγ
  have hn : ‖w-a‖≤R := by simpa [mem_closedBall,dist_eq_norm] using hw
  have hre := (Complex.abs_re_le_norm (w-a)).trans hn
  simp only [Complex.sub_re,ha,sub_zero] at hre
  have := (abs_le.mp hre).1
  change -(1/10)<w.re
  linarith

theorem lemma162_actual_circle_pole_removal {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β γ a : ℂ) {R : ℝ} (hR : 0≤R) (h0 : (0 : ℂ)∉sphere a R)
    (hγ : γ∉sphere a R) :
    circleIntegral (lemma162MellinIntegrand χ β γ) a R =
      circleIntegral (fun w => lemma162MellinNumerator χ β γ w/(w^3*(w-γ))) a R := by
  apply circleIntegral.integral_congr hR
  intro w hw
  apply lemma162_mellin_pole_removal χ β γ
  · intro h; subst w; exact h0 hw
  · intro h; subst w; exact hγ hw

theorem lemma162_actual_zero_residue {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (β : ℂ) (hβ : β.re=0) (γ : ℂ) (hγ : γ.re=0)
    {r : ℝ} (hr : 0<r) (hrγ : r<‖γ‖) (hrsmall : r<1/10) :
    (2*Real.pi*I : ℂ)⁻¹*circleIntegral (lemma162MellinIntegrand χ β γ) 0 r =
      lemma162ZeroResidue (lemma162MellinNumerator χ β γ) γ := by
  rw [lemma162_actual_circle_pole_removal χ β γ 0 hr.le
    (by simpa using ne_of_lt hr) (by simpa [mem_sphere] using ne_of_gt hrγ)]
  exact lemma162_zero_residue_circle _ hr hrγ
    (lemma162_mellin_numerator_disk χ hD β hβ γ hγ (by simp) hrsmall).differentiableOn

theorem lemma162_actual_shift_residue {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (β : ℂ) (hβ : β.re=0) (γ : ℂ) (hγ : γ.re=0)
    {r : ℝ} (hr : 0<r) (hrγ : r<‖γ‖) (hrsmall : r<1/10) :
    (2*Real.pi*I : ℂ)⁻¹*circleIntegral (lemma162MellinIntegrand χ β γ) γ r =
      lemma162ShiftResidue (lemma162MellinNumerator χ β γ) γ := by
  rw [lemma162_actual_circle_pole_removal χ β γ γ hr.le
    (by simpa [mem_sphere,dist_eq_norm] using ne_of_gt hrγ) (by simpa using ne_of_lt hr)]
  exact lemma162_shift_residue_circle _ hr hrγ
    (lemma162_mellin_numerator_disk χ hD β hβ γ hγ hγ hrsmall).differentiableOn

theorem lemma162_actual_residue_sum_circle {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (β : ℂ) (hβ : β.re=0) (γ : ℂ) (hγ : γ.re=0) (hγ0 : γ≠0)
    {R : ℝ} (hγR : ‖γ‖<R) (hRsmall : R<1/10) :
    (2*Real.pi*I : ℂ)⁻¹*circleIntegral (lemma162MellinIntegrand χ β γ) 0 R =
      lemma162ZeroResidue (lemma162MellinNumerator χ β γ) γ+
        lemma162ShiftResidue (lemma162MellinNumerator χ β γ) γ ∧
    (2*Real.pi*I : ℂ)⁻¹*circleIntegral (lemma162MellinIntegrand χ β γ) 0 R =
      lemma162ThirdDividedDifference (lemma162MellinNumerator χ β γ) γ := by
  have hR : 0<R := (norm_nonneg _).trans_lt hγR
  rw [lemma162_residue_sum _ hγ0]
  have hh : (2*Real.pi*I : ℂ)⁻¹*circleIntegral (lemma162MellinIntegrand χ β γ) 0 R =
      lemma162ThirdDividedDifference (lemma162MellinNumerator χ β γ) γ := by
    rw [lemma162_actual_circle_pole_removal χ β γ 0 hR.le
      (by simpa using ne_of_lt hR) (by simpa [mem_sphere] using ne_of_lt hγR)]
    exact lemma162_two_pole_circle _ hγ0 hγR
      (lemma162_mellin_numerator_disk χ hD β hβ γ hγ (by simp) hRsmall).differentiableOn
  exact ⟨hh,hh⟩

/-- Explicit disk geometry under the already published shift threshold. -/
theorem lemma162_paper_mellin_geometry {D : ℕ} {c : ℝ} (hc : 0<c)
    (hL : 3≤lemma23PaperL D) (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10)
    (j : Fin 2) :
    lemma162PaperShift D c j≠0 ∧
      ‖lemma162PaperShift D c j‖≤3*Real.pi/lemma23PaperL D^9 ∧
      ‖lemma162PaperShift D c j‖<lemma162MellinRadius D/2 ∧
      0<lemma162MellinRadius D ∧ lemma162MellinRadius D<1/10 := by
  have hL0 : 0<lemma23PaperL D := by linarith
  have hn : ‖lemma162PaperShift D c j‖≤3*Real.pi/lemma23PaperL D^9 := by
    have hh := lemma83_paper_beta_norm hL hc hsmall ⟨j.val,by omega⟩
    simpa [lemma162PaperShift,lemma44PaperAlpha,lemma23PaperP,Real.log_exp,mul_div_assoc] using hh
  have hp : (3:ℝ)^8≤lemma23PaperL D^8 := pow_le_pow_left₀ (by norm_num) hL 8
  have hpi : 60*Real.pi<lemma23PaperL D^8 := by
    nlinarith [Real.pi_le_four]
  have hs : 3*Real.pi/lemma23PaperL D^9<1/(20*lemma23PaperL D) := by
    apply (div_lt_div_iff₀ (pow_pos hL0 9) (by positivity)).mpr
    calc
      _ = (60*Real.pi)*lemma23PaperL D := by ring
      _ < lemma23PaperL D^8*lemma23PaperL D := mul_lt_mul_of_pos_right hpi hL0
      _ = _ := by ring
  refine ⟨lemma162_paper_shift_nonzero hc hL hsmall j,hn,?_,?_,?_⟩
  · apply hn.trans_lt
    convert hs using 1
    unfold lemma162MellinRadius
    field_simp
    norm_num
  · exact inv_pos.mpr (by positivity)
  · unfold lemma162MellinRadius
    apply (inv_lt_comm₀ (by positivity : (0:ℝ)<10*lemma23PaperL D) (by norm_num)).mpr
    norm_num
    linarith

/-- One eventual threshold, uniform in the character and in both original j.
The two local residues and the enclosing integral all use the genuine integrand. -/
theorem lemma162_paper_mellin_residues (c : ℝ) (hc : 0<c) :
    ∃ D₀ : ℕ, 3≤D₀ ∧ lemma23SectionFourModulusThreshold≤D₀ ∧
      ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D, ∀ j : Fin 2,
        let β := lemma52PaperBetaOne D c
        let γ := lemma162PaperShift D c j
        let H := lemma162MellinNumerator χ β γ
        γ≠0 ∧ ‖γ‖<lemma162MellinRadius D/2 ∧
        (∀ r : ℝ, 0<r → r<‖γ‖ →
          (2*Real.pi*I : ℂ)⁻¹*circleIntegral (lemma162MellinIntegrand χ β γ) 0 r =
            lemma162ZeroResidue H γ ∧
          (2*Real.pi*I : ℂ)⁻¹*circleIntegral (lemma162MellinIntegrand χ β γ) γ r =
            lemma162ShiftResidue H γ) ∧
        (2*Real.pi*I : ℂ)⁻¹*circleIntegral (lemma162MellinIntegrand χ β γ) 0
            (lemma162MellinRadius D) = lemma162ZeroResidue H γ+lemma162ShiftResidue H γ ∧
        lemma162ZeroResidue H γ+lemma162ShiftResidue H γ=lemma162ThirdDividedDifference H γ ∧
        ∀ w : ℂ, 0<w.re → lemma162MellinIntegrand χ β γ w =
          lemma162DirichletSeries χ β γ (lemma162GeneralMEulerProduct χ β) (1+w)*
            (lemma56PaperT D : ℂ)^w*lemma57OmegaOne D w/w := by
  obtain ⟨D₁,hsection,hshift⟩ := lemma52_exists_shift_threshold hc
  obtain ⟨D₂,_,harithmetic⟩ := lemma162_paper_actual_arithmetic_bridge c hc
  refine ⟨max 3 (max D₁ D₂),le_max_left _ _,hsection.trans
    ((le_max_left D₁ D₂).trans (le_max_right 3 _)),?_⟩
  intro D hD χ j
  have ht : max D₁ D₂≤D := (le_max_right _ _).trans hD
  have h1 : D₁≤D := (le_max_left _ _).trans ht
  have h2 : D₂≤D := (le_max_right _ _).trans ht
  have hd : 1<D := by have := (le_max_left 3 (max D₁ D₂)).trans hD; omega
  have hL := (lemma44_parameters_at_explicit_threshold (hsection.trans h1)).1
  obtain ⟨hγ0,_,hγR,hR,hRsmall⟩ := lemma162_paper_mellin_geometry hc hL (hshift D h1) j
  have hγbig : ‖lemma162PaperShift D c j‖<lemma162MellinRadius D := by linarith
  have hsum := lemma162_actual_residue_sum_circle χ hd _ (lemma161_paper_beta_re D c)
    _ (lemma162_paper_shift_re D c j) hγ0 hγbig hRsmall
  refine ⟨hγ0,hγR,?_,hsum.1,lemma162_residue_sum _ hγ0,?_⟩
  · intro r hr hrγ
    have hrs : r<1/10 := hrγ.trans (hγbig.trans hRsmall)
    exact ⟨lemma162_actual_zero_residue χ hd _ (lemma161_paper_beta_re D c) _
      (lemma162_paper_shift_re D c j) hr hrγ hrs,
      lemma162_actual_shift_residue χ hd _ (lemma161_paper_beta_re D c) _
        (lemma162_paper_shift_re D c j) hr hrγ hrs⟩
  · intro w hw
    exact lemma162_mellin_actual_series χ _ (lemma161_paper_beta_re D c) _
      (lemma162_paper_shift_re D c j) (((harithmetic D h2 χ).2 j).2.1) w hw

end ZhangLS.Spec
