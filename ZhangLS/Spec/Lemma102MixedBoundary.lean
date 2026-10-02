import ZhangLS.Spec.Lemma102MixedMainBound
import ZhangLS.Spec.Lemma102MixedLayers
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset Filter Topology
open scoped Classical
set_option maxHeartbeats 3000000

noncomputable def lemma102MixedBoundaryTotalExponent : ℕ := lemma102MixedBoundaryExponent+42
noncomputable def lemma102MixedBoundaryTotalConstant : ℝ :=
  96*lemma84CompanionConstant*(1+‖lemma84Section8Iota‖)*lemma102MixedBoundaryConstant*
    Real.exp (12/Real.log 2)*Real.exp (2/Real.log 2)

lemma lemma102_mixed_boundary_total_constant_pos : 0< lemma102MixedBoundaryTotalConstant := by
  unfold lemma102MixedBoundaryTotalConstant
  positivity [lemma84_companion_constant_pos,lemma102_mixed_boundary_constant_pos]

/-- All three literal knot layers are controlled in the actual mixed sum.
No pointwise O(L^-7) or weighted desired bound is an input hypothesis. -/
theorem lemma102_mixed_boundary_quantitative :
    ∀ c : ℝ, 0<c → ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      1≤lemma23PaperL D ∧ ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
      ∀ j : Fin 3, ‖lemma102MixedHybrid χ c j-lemma102MixedMain χ c j‖≤
        lemma102MixedBoundaryTotalConstant*(1+9*Real.log (lemma23PaperL D))^lemma102MixedBoundaryTotalExponent*
          (Real.log (lemma56PaperT D))^5*lemma23PaperL D^(-15:ℤ) := by
  intro c hc
  obtain ⟨Nb,hNb,hboundary⟩ := lemma102_mixed_boundary_pointwise c hc
  obtain ⟨Nf,hNf,hfirst⟩ := lemma84_section8_inner_bounds c hc
  obtain ⟨D₀,hD₀⟩ := eventually_atTop.mp (show ∀ᶠ D : ℕ in atTop,
      Nb≤D ∧ Nf≤D ∧ 2≤D ∧ lemma23PaperP D^(63/125:ℝ)<lemma23PaperP D*lemma56PaperT D^(-2:ℤ) from by
    filter_upwards [eventually_ge_atTop Nb,eventually_ge_atTop Nf,lemma84_section8_cutoffs_eventually]
      with D hb hf hq
    exact ⟨hb,hf,hq.1,by simpa [lemma84Section8Cutoff,lemma84Section8P1] using (hq.2.2 6).2.1⟩)
  refine ⟨D₀,(hD₀ D₀ le_rfl).2.2.1,?_⟩
  intro D hDD
  obtain ⟨hNbD,hNfD,hD2,hPcut⟩ := hD₀ D hDD
  have hL := (hboundary D hNbD).1
  refine ⟨by linarith,?_⟩
  intro χ hA j
  have hD : 1<D := by omega
  have hLp : 0< lemma23PaperL D := by linarith
  let F := 4*lemma84CompanionConstant*(1+‖lemma84Section8Iota‖)*lemma23PaperL D^(-6:ℤ)
  let E := lemma102MixedBoundaryConstant*(1+9*Real.log (lemma23PaperL D))^lemma102MixedBoundaryExponent*
    (Real.log (lemma56PaperT D))^4*lemma23PaperL D^(-9:ℤ)
  have hF0 : 0≤F := by dsimp [F]; positivity [lemma84_companion_constant_pos]
  have hE0 : 0≤E := by
    have hlog := Real.log_nonneg (by linarith : 1≤lemma23PaperL D)
    dsimp [E]
    positivity [lemma102_mixed_boundary_constant_pos,hlog]
  have hF (n : ℕ) (hn : 0<n) : ‖lemma84Section8FirstCombined χ c j n‖≤F := by
    have h6 := ((hfirst D hNfD).2 χ hA j 6).1 n hn
    have h7 := ((hfirst D hNfD).2 χ hA j 7).1 n hn
    unfold lemma84Section8FirstCombined
    apply (norm_add_le _ _).trans
    rw [norm_mul]
    have hh := mul_le_mul_of_nonneg_left h7 (norm_nonneg lemma84Section8Iota)
    dsimp [F]
    nlinarith only [h6,hh]
  have hid : lemma102MixedHybrid χ c j-lemma102MixedMain χ c j=
      ∑ a∈lemma102TransitionPairs D, lemma84Section8Weight χ c j a.1 a.2*
        lemma84Section8FirstCombined χ c j (a.1*a.2)*
          (lemma102Sum χ c j a.1 a.2-lemma102FullMain χ c j a.1 a.2) := by
    rw [lemma102MixedHybrid,lemma102MixedMain,←sum_sub_distrib,lemma102TransitionPairs,sum_filter]
    apply sum_congr rfl
    intro a ha
    split_ifs <;> ring
  rw [hid]
  calc
    _ ≤ ∑ a∈lemma102TransitionPairs D, ‖lemma84Section8Weight χ c j a.1 a.2‖*F*E := by
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro a ha
      have hs := mem_filter.mp ha
      obtain ⟨hd,hr,_⟩ := (lemma84_section8_pairs_exact D a.1 a.2).mp hs.1
      rw [norm_mul,norm_mul]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hF _ (Nat.mul_pos hd hr)) (norm_nonneg _))
        ((hboundary D hNbD).2 χ hA j a.1 a.2 hd hr hs.2) (norm_nonneg _)
        (mul_nonneg (norm_nonneg _) hF0)
    _ = (∑ a∈lemma102TransitionPairs D, ‖lemma84Section8Weight χ c j a.1 a.2‖)*F*E := by rw [sum_mul,sum_mul]
    _ ≤ (24*lemma84WeightScale (lemma23PaperL D^9)*Real.log (lemma56PaperT D))*F*E :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (lemma102_transition_weight_mass χ hD (by linarith) c j hPcut) hF0) hE0
    _ = _ := by
      dsimp [F,E,lemma102MixedBoundaryTotalConstant,lemma102MixedBoundaryTotalExponent,lemma84WeightScale]
      rw [Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      simp only [pow_add,zpow_neg,zpow_ofNat]
      field_simp <;> ring

end ZhangLS.Spec
