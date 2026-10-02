import ZhangLS.Spec.Lemma84Section8LittleO
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex Filter Topology
open scoped Classical
set_option maxHeartbeats 2000000

/-- Exact untouched boundary remainder for one true xi inner sum. -/
noncomputable def lemma84Section8BoundaryInner {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (μ d r : ℕ) : ℂ :=
  if lemma84Section8Cutoff D μ/lemma56PaperT D≤(d*r:ℕ) ∧
      (d*r:ℕ)<lemma84Section8Cutoff D μ then
    (lemma84XiSum χ c j μ d r (lemma84Section8Cutoff D μ/(d*r:ℕ))-
      LDerivAtOne χ*lemma83Pi χ d r*
        lemma84MainTerm D c j μ (lemma84Section8Cutoff D μ/(d*r:ℕ))) /
      (Real.log (lemma84Section8Cutoff D μ):ℂ)
  else 0

theorem lemma84_section8_boundary_inner_exact {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (μ d r : ℕ) :
    lemma84Section8SecondHybrid χ c j μ d r-lemma84Section8SecondMain χ c j μ d r=
      lemma84Section8BoundaryInner χ c j μ d r := by
  unfold lemma84Section8SecondHybrid lemma84Section8SecondMain lemma84Section8Second
    lemma84Section8BoundaryInner
  by_cases hi : ((d*r:ℕ):ℝ)<lemma84Section8Cutoff D μ/lemma56PaperT D
  · simp only [hi,if_true,sub_self,not_le_of_gt hi,false_and,if_false]
  · by_cases hQ : ((d*r:ℕ):ℝ)<lemma84Section8Cutoff D μ
    · simp only [hi,if_false,hQ,if_true,le_of_not_gt hi,true_and]
      ring
    · simp only [hi,if_false,hQ,and_false,sub_self]

/-- Both genuinely outstanding cutoff layers, with all λ,μ,φ,Π and iota
factors retained. Equality at Pμ/T is assigned to the boundary explicitly. -/
theorem lemma84_section8_boundary_exact {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) :
    lemma84Section8Boundary χ c j=
      ∑ a∈lemma84Section8Pairs D, lemma84Section8Weight χ c j a.1 a.2*
        lemma84Section8FirstCombined χ c j (a.1*a.2)*
        (lemma84Section8BoundaryInner χ c j 6 a.1 a.2+
          star lemma84Section8Iota*lemma84Section8BoundaryInner χ c j 7 a.1 a.2) := by
  rw [lemma84Section8Boundary,lemma84Section8Hybrid,lemma84Section8FullSecondMain,←sum_sub_distrib]
  apply sum_congr rfl
  intro a ha
  rw [←lemma84_section8_boundary_inner_exact,←lemma84_section8_boundary_inner_exact]
  ring

/-- Explicit remaining condition, not a theorem: the two boundary layers must
be o(α) before the xi main term can replace the actual xi sum everywhere. -/
def Lemma84Section8BoundaryTarget : Prop :=
  ∀ c : ℝ, 0<c → ∀ ε : ℝ, 0<ε → ∃ D₀ : ℕ, 2≤D₀ ∧
    ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
      ∀ j : Fin 3, ‖lemma84Section8Boundary χ c j‖≤ε*lemma44PaperAlpha D

/-- The repaired theorem supplies all interior work. The single explicitly
named missing hypothesis here is the exact boundary target above. -/
theorem lemma84_section8_full_second_of_boundary (hboundary : Lemma84Section8BoundaryTarget) :
    ∀ c : ℝ, 0<c → ∀ ε : ℝ, 0<ε → ∃ D₀ : ℕ, 2≤D₀ ∧
      ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
        ∀ j : Fin 3,
          ‖lemma84Section8Raw χ c j-lemma84Section8FullSecondMain χ c j‖≤ε*lemma44PaperAlpha D := by
  intro c hc ε hε
  obtain ⟨Di,hDi,hi⟩ := lemma84_section8_repaired_interior_little_o c hc (ε/2) (by positivity)
  obtain ⟨Db,hDb,hb⟩ := hboundary c hc (ε/2) (by positivity)
  refine ⟨max Di Db,le_trans hDi (le_max_left _ _),?_⟩
  intro D hD χ hA j
  rw [lemma84_section8_exact_error_split]
  apply (norm_add_le _ _).trans
  have hh := add_le_add (hi D (le_trans (le_max_left _ _) hD) χ hA j)
    (hb D (le_trans (le_max_right _ _) hD) χ hA j)
  nlinarith only [hh]

end ZhangLS.Spec
