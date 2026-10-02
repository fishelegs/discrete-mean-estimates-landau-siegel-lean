import ZhangLS.Spec.Proposition71FiniteCriticalMean
import ZhangLS.Spec.Proposition71FrontFamilyRate

/-! # Actual J(1) exceptional-family estimate for the finite long polynomial

This attaches the proved Gaussian contour shift to the actual Ψ₂ polynomial
saving. The functional-equation character can be ψ or χψ; no conductor loss
survives the exact critical-line modulus.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Finset
open scoped Classical
set_option maxHeartbeats 4000000

/-- The complete finite-long part of the shared Section7/14 exceptional-family
step, with the literal original J(1), Ψ₂ and Assumption (A). -/
theorem proposition71_finite_exceptional_contour_little_o
    (Bc Ba W : ℝ) (hBc : 0<Bc) (hBa : 0<Ba) (hW : 0<W)
    (ε : ℝ) (hε : 0<ε) :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
      ∀ (N : lemma33CharacterIndex D → ℕ) [∀ψ, NeZero (N ψ)]
        (θ : (ψ : lemma33CharacterIndex D) → DirichletCharacter ℂ (N ψ)),
      (∀ψ∈proposition21ActualPsi2Family χ, (θ ψ).IsPrimitive) →
      (∀ψ∈proposition21ActualPsi2Family χ, N ψ≠1) →
      (∀ψ∈proposition21ActualPsi2Family χ, Real.log (N ψ : ℝ)≤3*lemma23PaperL D^9) →
      ∀ (X : ℕ), X≤⌊lemma23PaperP D⌋₊ → ∀ c a : ℕ → ℂ,
      (∀n∈Icc 1 ⌊lemma23PaperP D^2⌋₊, ‖c n‖≤Bc*(lemma34Tau 5 n : ℝ)) →
      (∀n∈Icc 1 X, ‖a n‖≤Ba) →
      ∀ w : lemma33CharacterIndex D → ℂ, (∀ψ∈proposition21ActualPsi2Family χ, ‖w ψ‖≤W) →
      ‖∑ψ∈proposition21ActualPsi2Family χ, w ψ*lemma81NormalizedSegmentIntegral D 1
        (proposition71FiniteFrontKernel D (θ ψ) ψ.2 ⌊lemma23PaperP D^2⌋₊ X c a)‖≤ε*lemma33ActualPrimeMass D := by
  obtain ⟨Nc,hNc,hcritical⟩ := proposition71_finite_critical_exceptional_little_o Bc Ba W hBc hBa hW
    (ε/2) (by positivity)
  obtain ⟨Ns,hNs,hshift⟩ := proposition71_finite_front_shift hBc.le hBa.le
    (show 0<ε/(2*W) by positivity)
  refine ⟨max Nc Ns,hNc.trans (le_max_left _ _),?_⟩
  intro D hD χ hA N _ θ hθ hN hlog X hX c a hc ha w hw
  have hDc := (le_max_left _ _).trans hD
  have hDs := (le_max_right _ _).trans hD
  have hL := (lemma44_parameters_at_explicit_threshold (hNs.trans hDs)).1
  let E := proposition21ActualPsi2Family χ
  let F := fun ψ : lemma33CharacterIndex D =>
    proposition71FiniteFrontKernel D (θ ψ) ψ.2 ⌊lemma23PaperP D^2⌋₊ X c a
  let A := ∑ψ∈E, w ψ*lemma81NormalizedSegmentIntegral D 1 (F ψ)
  let B := ∑ψ∈E, w ψ*lemma81NormalizedSegmentIntegral D 0 (F ψ)
  have hb : ‖B‖≤(ε/2)*lemma33ActualPrimeMass D :=
    hcritical D hDc χ hA N θ hθ hN X hX c a hc ha w hw
  have hcard : (E.card : ℝ)≤lemma33ActualPrimeMass D := by
    have hs : E⊆lemma33ActualFamily D := filter_subset _ _
    exact (by exact_mod_cast card_le_card hs : (E.card : ℝ)≤(lemma33ActualFamily D).card).trans
      (proposition71_actual_family_card_le_mass hL)
  have hdiff : ‖A-B‖≤(ε/2)*lemma33ActualPrimeMass D := by
    dsimp only [A,B]
    rw [←sum_sub_distrib]
    calc
      _≤∑ψ∈E, ‖w ψ*lemma81NormalizedSegmentIntegral D 1 (F ψ)-
          w ψ*lemma81NormalizedSegmentIntegral D 0 (F ψ)‖ := norm_sum_le _ _
      _≤∑_ψ∈E, W*(ε/(2*W)) := by
        apply sum_le_sum
        intro ψ hψ
        rw [←mul_sub,norm_mul]
        exact mul_le_mul (hw ψ hψ)
          (hshift hDs (θ ψ) (hθ ψ hψ) (hN ψ hψ) (hlog ψ hψ) ψ.2 X hX c a hc ha)
          (norm_nonneg _) hW.le
      _=(W*(ε/(2*W)))*(E.card : ℝ) := by simp [mul_comm]
      _≤(W*(ε/(2*W)))*lemma33ActualPrimeMass D := mul_le_mul_of_nonneg_left hcard (by positivity)
      _=_ := by field_simp
  change ‖A‖≤ε*lemma33ActualPrimeMass D
  exact (norm_le_norm_sub_add A B).trans ((add_le_add hdiff hb).trans_eq (by ring))

end ZhangLS.Spec
