import ZhangLS.Spec.Lemma162ActualDirichletSeries
import ZhangLS.Spec.Lemma162OriginalValueWitness
import ZhangLS.Spec.Lemma161UniformNonzero
import ZhangLS.Spec.Lemma83

/-! Frozen stage-one capstone: genuine original Section16 arithmetic/Euler
bridge, with exactly β₁, β₂ and the shared c′. No assumption(A), old U
holomorphy, repaired U holomorphy or center asymptotic is claimed. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex
set_option maxHeartbeats 1500000

noncomputable def lemma162PaperShift (D : ℕ) (c : ℝ) (j : Fin 2) : ℂ :=
  lemma83PaperBeta D c ⟨j.val,by omega⟩

@[simp] lemma lemma162_paper_shift_zero (D : ℕ) (c : ℝ) :
    lemma162PaperShift D c 0 = lemma52PaperBetaOne D c := by
  simp [lemma162PaperShift,lemma83PaperBeta]

@[simp] lemma lemma162_paper_shift_one (D : ℕ) (c : ℝ) :
    lemma162PaperShift D c 1 = lemma52PaperBetaTwo D c := by
  simp [lemma162PaperShift,lemma83PaperBeta]

lemma lemma162_paper_shift_re (D : ℕ) (c : ℝ) (j : Fin 2) :
    (lemma162PaperShift D c j).re = 0 := lemma83_beta_re D c _

lemma lemma162_paper_shift_nonzero {D : ℕ} {c : ℝ} (hc : 0<c)
    (hL : 3 ≤ lemma23PaperL D)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D ≤ 1/10) (j : Fin 2) :
    lemma162PaperShift D c j ≠ 0 := by
  have ha : 0<lemma44PaperAlpha D := (lemma44_alpha_pos_le_one hL).1
  have hu : 0≤c*lemma44PaperAlpha D*lemma23PaperL D := by positivity
  have h1 : 0<lemma23PaperOffsetOne D c := by
    have he : lemma23PaperOffsetOne D c =
      lemma44PaperAlpha D*(1-5*(c*lemma44PaperAlpha D*lemma23PaperL D)) := by
      unfold lemma23PaperOffsetOne
      ring
    rw [he]
    exact mul_pos ha (by linarith)
  have h2 : 0<lemma23PaperOffsetTwo D c := by
    change 0 < 2*lemma44PaperAlpha D*(1+c*lemma44PaperAlpha D*lemma23PaperL D)
    positivity
  fin_cases j
  · change lemma162PaperShift D c 0 ≠ 0
    rw [lemma162_paper_shift_zero,lemma52PaperBetaOne]
    exact mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr h1.ne')
  · change lemma162PaperShift D c 1 ≠ 0
    rw [lemma162_paper_shift_one,lemma52PaperBetaTwo]
    exact mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr h2.ne')

/-- This is an arithmetic bridge, explicitly not the original numbered lemma. -/
def Lemma162PaperArithmeticBridgeAt (c : ℝ) : Prop :=
  ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D,
    (∀ d l : ℕ, d ≠ 0 → l ≠ 0 →
      Lemma161Continuation χ (lemma52PaperBetaOne D c) d l
        (lemma162GeneralMEulerProduct χ (lemma52PaperBetaOne D c) d l)) ∧
    ∀ j : Fin 2,
      lemma162PaperShift D c j ≠ 0 ∧
      lemma161Star χ (lemma52PaperBetaOne D c) (1-lemma162PaperShift D c j) ≠ 0 ∧
      ∀ s : ℂ, 1<s.re →
        LSeriesSummable
          (lemma162Coefficient χ (lemma52PaperBetaOne D c) (lemma162PaperShift D c j)
            (lemma162GeneralMEulerProduct χ (lemma52PaperBetaOne D c))) s ∧
        HasProd (fun q : Nat.Primes =>
          lemma162ActualLocalSeries χ (lemma52PaperBetaOne D c) (lemma162PaperShift D c j) q s)
          (lemma162DirichletSeries χ (lemma52PaperBetaOne D c) (lemma162PaperShift D c j)
            (lemma162GeneralMEulerProduct χ (lemma52PaperBetaOne D c)) s)

theorem lemma162_paper_actual_arithmetic_bridge (c : ℝ) (hc : 0<c) :
    Lemma162PaperArithmeticBridgeAt c := by
  obtain ⟨D₁,hD₁,hstar⟩ := lemma161_star_ne_zero_eventually c hc
  obtain ⟨D₂,hsection,hshift⟩ := lemma52_exists_shift_threshold hc
  refine ⟨max D₁ D₂,hD₁.trans (le_max_left _ _),?_⟩
  intro D hD χ
  have h1 : D₁≤D := (le_max_left _ _).trans hD
  have h2 : D₂≤D := (le_max_right _ _).trans hD
  have hL := (lemma44_parameters_at_explicit_threshold (hsection.trans h2)).1
  have ha : 0<lemma44PaperAlpha D := (lemma44_alpha_pos_le_one hL).1
  have hsmall := hshift D h2
  refine ⟨fun d l hd hl => lemma162_general_m_actual_continuation χ _
    (lemma161_paper_beta_re D c) hd hl,?_⟩
  intro j
  have hγ : (lemma162PaperShift D c j).re = 0 := lemma162_paper_shift_re D c j
  have hb : ‖lemma162PaperShift D c j‖ ≤ 3*lemma44PaperAlpha D :=
    lemma83_paper_beta_norm hL hc hsmall _
  have hdist : ‖(1-lemma162PaperShift D c j)-1‖ < 5*lemma44PaperAlpha D := by
    rw [show (1-lemma162PaperShift D c j)-1 = -lemma162PaperShift D c j by ring,norm_neg]
    linarith
  have hM := hstar D h1 χ _ hdist
  refine ⟨lemma162_paper_shift_nonzero hc hL hsmall j,hM,?_⟩
  intro s hs
  exact ⟨lemma162_actual_lseries_summable χ _ (lemma161_paper_beta_re D c) _ hγ hM s hs,
    lemma162_actual_dirichlet_series_hasProd χ _ (lemma161_paper_beta_re D c) _ hγ hM s hs⟩

/-- Compatibility with the same earlier c′; no new phase convention is chosen. -/
theorem lemma162_arithmetic_bridge_with_shared_shift_constant :
    ∃ c : ℝ, 0<c ∧ Lemma52CompatibleConstant c ∧ Lemma162PaperArithmeticBridgeAt c := by
  obtain ⟨c,hc,hcompatible,C,hC,D₀,hrest⟩ := lemma52_proved
  exact ⟨c,hc,hcompatible,lemma162_paper_actual_arithmetic_bridge c hc⟩

end ZhangLS.Spec
