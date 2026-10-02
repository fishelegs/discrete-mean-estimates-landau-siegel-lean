import ZhangLS.Spec.Lemma102MixedInteriorLittleO
import ZhangLS.Spec.Lemma102MixedBoundaryLittleO
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Filter Topology
set_option maxHeartbeats 2000000

/-- The actual Section 10 mixed sum tolerates the proved Π-dependent and
weaker boundary estimates. This proves the full ξ-factor replacement only;
no later arithmetic summation or final mean asymptotic is inferred. -/
theorem lemma102_mixed_full_xi_replacement_little_o :
    ∀ c : ℝ, 0<c → ∀ ε : ℝ, 0<ε → ∃ D₀ : ℕ, 2≤D₀ ∧
      ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
      ∀ j : Fin 3, ‖lemma102MixedRaw χ c j-lemma102MixedMain χ c j‖≤ε*lemma44PaperAlpha D := by
  intro c hc ε hε
  obtain ⟨Ni,hNi,hi⟩ := lemma102_mixed_interior_little_o c hc (ε/2) (by positivity)
  obtain ⟨Nb,hNb,hb⟩ := lemma102_mixed_boundary_little_o c hc (ε/2) (by positivity)
  refine ⟨max Ni Nb,hNi.trans (le_max_left _ _),?_⟩
  intro D hDD χ hA j
  have h₁ := hi D ((le_max_left _ _).trans hDD) χ hA j
  have h₂ := hb D ((le_max_right _ _).trans hDD) χ hA j
  have hid : lemma102MixedRaw χ c j-lemma102MixedMain χ c j=
      (lemma102MixedRaw χ c j-lemma102MixedHybrid χ c j)+
        (lemma102MixedHybrid χ c j-lemma102MixedMain χ c j) := by ring
  rw [hid]
  exact (norm_add_le _ _).trans ((add_le_add h₁ h₂).trans_eq (by ring))

/-- Fully literal source κ/ξ/tent mixed sum, with the same finite outer
support as the actual Section 10 display. -/
noncomputable def lemma102MixedSource {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) : ℂ :=
  ∑ a∈lemma84Section8Pairs D, lemma84Section8Weight χ c j a.1 a.2*
    (lemma84Section8FirstSource χ c j 6 (a.1*a.2)+
      lemma84Section8Iota*lemma84Section8FirstSource χ c j 7 (a.1*a.2))*
    (∑' n : ℕ, χ.evalNat n*lemma83Xi (lemma83PaperBeta D c) j n a.1 a.2/(n:ℂ)*
      (lemma111Tent (Real.log ((a.1*a.2:ℝ)*(n:ℝ))/Real.log (lemma23PaperP D)):ℂ))

/-- Source-facing weighted capstone. It makes no assumption of the desired
weighted estimate and retains all three boundary bands. -/
theorem lemma102_source_full_xi_replacement_little_o :
    ∀ c : ℝ, 0<c → ∀ ε : ℝ, 0<ε → ∃ D₀ : ℕ, 2≤D₀ ∧
      ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
      ∀ j : Fin 3, ‖lemma102MixedSource χ c j-lemma102MixedMain χ c j‖≤ε*lemma44PaperAlpha D := by
  intro c hc ε hε
  obtain ⟨Ni,hNi,hi⟩ := lemma102_mixed_full_xi_replacement_little_o c hc ε hε
  obtain ⟨Nq,hq⟩ := eventually_atTop.mp lemma84_section8_cutoffs_eventually
  refine ⟨max Ni Nq,hNi.trans (le_max_left _ _),?_⟩
  intro D hDD χ hA j
  have hqD := hq D ((le_max_right _ _).trans hDD)
  have he : lemma102MixedRaw χ c j=lemma102MixedSource χ c j :=
    lemma102_mixed_source_exact χ (by omega) c j (hqD.2.2 6).1 (hqD.2.2 7).1
  rw [←he]
  exact hi D ((le_max_left _ _).trans hDD) χ hA j

end ZhangLS.Spec
