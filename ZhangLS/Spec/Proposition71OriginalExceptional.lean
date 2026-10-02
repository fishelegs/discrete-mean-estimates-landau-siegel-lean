import ZhangLS.Spec.Proposition71OriginalFrontAttachment

/-! # Original Section7 (7.3) for the literal C integrand

The actual three-shift coefficient identity and strict short support are now
attached to the common proved infinite-long exceptional-family estimate.
Both normalized and original unnormalized upward contour forms are provided.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Finset
open scoped Classical
set_option maxHeartbeats 4500000
set_option maxRecDepth 4096

/-- Original (7.3), normalized by 1/(2πi). The c′ parameter is arbitrary here;
its original positive compatible choice is needed only in later main terms. -/
theorem proposition71_original_seven_three_normalized :
    ∀ B₁ B₂ : ℝ, 0<B₁ → 0<B₂ → ∀ ε : ℝ, 0<ε →
      ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ → ∀ c : ℝ,
      ∀ a₁ a₂ : ℕ → ℂ, Lemma81AdmissibleSequence D B₁ a₁ → Lemma81AdmissibleSequence D B₂ a₂ →
      ‖∑ψ∈proposition21ActualPsi2Family χ,
        lemma81NormalizedSegmentIntegral D 1 (lemma81CIntegrand D c ψ.2 a₁ a₂)‖≤ε*lemma33ActualPrimeMass D := by
  intro B₁ B₂ hB₁ hB₂ ε hε
  obtain ⟨Nm,hNm,hmean⟩ := proposition71_infinite_exceptional_contour_little_o B₁ B₂ 1 hB₁ hB₂ (by norm_num) ε hε
  obtain ⟨Ng,hNg,hgeo⟩ := proposition71_original_short_support_geometry
  refine ⟨max Nm Ng,hNm.trans (le_max_left _ _),?_⟩
  intro D hD χ hA c a₁ a₂ ha₁ ha₂
  have hDm := (le_max_left _ _).trans hD
  have hDg := (le_max_right _ _).trans hD
  obtain ⟨hL,hX,hgeometry⟩ := hgeo D hDg
  letI : ∀ψ : lemma33CharacterIndex D, NeZero ψ.1.val := fun ψ =>
    ⟨(lemma33_mem_prime_window.mp ψ.1.property).1.ne_zero⟩
  have hΨ (ψ : lemma33CharacterIndex D) (hψ : ψ∈proposition21ActualPsi2Family χ) :
      Lemma23InPsi (D := D) ψ.2 := ((proposition21_mem_psi2 χ ψ.1 ψ.2).mp hψ).1
  have hp (ψ : lemma33CharacterIndex D) : ψ.1.val∈lemma56PaperPrimes D := by
    simpa only [lemma35_prime_windows_eq] using ψ.1.property
  have hκ (m : ℕ) (_hm : 0<m) :
      ‖(lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a₁) m‖≤B₁*(lemma34Tau 5 m : ℝ) :=
    proposition71_actual_convolution_le_tau_five _ (lemma83_beta_re D c) hB₁.le a₁ ha₁.1 m
  let w := fun ψ : lemma33CharacterIndex D =>
    -I*(((ψ.1.val : ℝ)*lemma51PaperT0 D : ℝ) : ℂ)^lemma52PaperBetaThree D c
  have hw (ψ : lemma33CharacterIndex D) (_hψ : ψ∈proposition21ActualPsi2Family χ) : ‖w ψ‖≤1 := by
    dsimp [w]
    rw [norm_mul,norm_neg,norm_I,lemma81_actual_phase_norm_one c (by linarith : 0< lemma23PaperL D),one_mul]
  have hb := hmean D hDm χ hA (fun ψ => ψ.1.val) (fun ψ => ψ.2)
    (fun ψ hψ => (hΨ ψ hψ).2.1) (fun ψ hψ => (hΨ ψ hψ).1.ne_one)
    (fun ψ hψ => (hgeometry ψ.1.val (hp ψ)).1) ⌊lemma81Cutoff D⌋₊ hX
    (fun ψ hψ n hn => (hgeometry ψ.1.val (hp ψ)).2 n hn)
    (fun n => (lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a₁) n) a₂ hκ
    (fun n hn => ha₂.1 n) w hw
  apply le_trans _ hb
  apply le_of_eq
  congr 1
  apply sum_congr rfl
  intro ψ hψ
  exact proposition71_actual_C_contour_eq_infinite c a₁ a₂ ha₁ ha₂ ψ.2

lemma proposition71_unnormalized_segment_eq (D : ℕ) (x : ℝ) (f : ℂ → ℂ) :
    I*(∫t in -(lemma23PaperL D^405)..lemma23PaperL D^405, f (lemma81SegmentPoint D x t))=
      (((2*Real.pi : ℝ) : ℂ)*I)*lemma81NormalizedSegmentIntegral D x f := by
  unfold lemma81NormalizedSegmentIntegral
  have hp : (((2*Real.pi : ℝ) : ℂ))≠0 := by exact_mod_cast (mul_ne_zero (by norm_num : (2 : ℝ)≠0) Real.pi_ne_zero)
  field_simp

/-- Exactly original (7.3), with ds=i dt on the upward J(1), no normalization
silently omitted, and all original uniform sequence/family quantifiers. -/
theorem proposition71_original_seven_three :
    ∀ B₁ B₂ : ℝ, 0<B₁ → 0<B₂ → ∀ ε : ℝ, 0<ε →
      ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ → ∀ c : ℝ,
      ∀ a₁ a₂ : ℕ → ℂ, Lemma81AdmissibleSequence D B₁ a₁ → Lemma81AdmissibleSequence D B₂ a₂ →
      ‖∑ψ∈proposition21ActualPsi2Family χ,
        I*(∫t in -(lemma23PaperL D^405)..lemma23PaperL D^405,
          lemma81CIntegrand D c ψ.2 a₁ a₂ (lemma81SegmentPoint D 1 t))‖≤ε*lemma33ActualPrimeMass D := by
  intro B₁ B₂ hB₁ hB₂ ε hε
  obtain ⟨D₀,hD₀,hbound⟩ := proposition71_original_seven_three_normalized B₁ B₂ hB₁ hB₂
    (ε/(2*Real.pi)) (by positivity)
  refine ⟨D₀,hD₀,?_⟩
  intro D hD χ hA c a₁ a₂ ha₁ ha₂
  simp_rw [proposition71_unnormalized_segment_eq]
  rw [←mul_sum,norm_mul,norm_mul,norm_I,mul_one,Complex.norm_of_nonneg (by positivity : 0≤2*Real.pi)]
  exact (mul_le_mul_of_nonneg_left (hbound D hD χ hA c a₁ a₂ ha₁ ha₂) (by positivity)).trans_eq (by field_simp)

end ZhangLS.Spec
