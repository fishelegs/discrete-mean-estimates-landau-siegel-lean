import ZhangLS.Spec.Lemma121Transition

/-! # All three actual κ13 branches, with an explicit source repair
The low exponential bound has the original conclusion. The transition bound
is concretely L^-7, without defining the source's unexplained α1. The high
branch keeps the exact phase instead of the unsupported 10^-5 linearization.
This must not be advertised as the printed Lemma 12.1. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset Filter Topology
open scoped Real

noncomputable def lemma121ConcreteConstant : ℝ :=
  36+lemma121TransitionConstant+lemma121ExactHighConstant

lemma lemma121_concrete_constant_pos : 0<lemma121ConcreteConstant := by
  unfold lemma121ConcreteConstant
  positivity [lemma121_transition_constant_pos,lemma121_exact_high_constant_pos]

/-- Three checked actual branches with one absolute constant chosen before
shared c′ and one modulus threshold. The two source qualifications above are
part of the theorem's intended use. -/
def Lemma121ConcreteExactTarget : Prop :=
  ∃ C κ : ℝ, 0<C ∧ 0<κ ∧ ∀ c : ℝ, 0<c → ∃ D₀ : ℕ, 2≤D₀ ∧
    ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ → ∀ j : Fin 3, ∀ d : ℕ,
      (1≤d → (d:ℝ)≤lemma121PDoublePrimeOne D/lemma56PaperT D →
        ‖lemma121Sum χ c j d‖≤C*lemma56PaperT D^(-κ)) ∧
      (lemma121PDoublePrimeOne D/lemma56PaperT D<(d:ℝ) →
        (d:ℝ)≤lemma121PDoublePrimeOne D →
        ‖lemma121Sum χ c j d‖≤C*lemma23PaperL D^(-7:ℤ)) ∧
      (lemma121PDoublePrimeOne D<(d:ℝ) → (d:ℝ)<lemma121P2 D →
        ‖lemma121Sum χ c j d-lemma121ExactMain χ c j d‖≤C*lemma23PaperL D^(-15:ℤ))

/-- Complete checked concrete three-branch replacement. It does not prove
Lemma121PrintedTarget or assign a definition to α1. -/
theorem lemma121_concrete_exact_proved : Lemma121ConcreteExactTarget := by
  refine ⟨lemma121ConcreteConstant,1/2,lemma121_concrete_constant_pos,by norm_num,?_⟩
  intro c hc
  obtain ⟨N,hN,hh⟩ := lemma82_uniform_threshold c hc
  obtain ⟨M,hM⟩ := Filter.eventually_atTop.mp lemma121_tail_absorption_eventually
  obtain ⟨K,hK⟩ := Filter.eventually_atTop.mp lemma121_exponential_absorption_eventually
  let D₀ := max (max N M) K
  have hNN : N≤D₀ := (le_max_left N M).trans (le_max_left _ _)
  have hMM : M≤D₀ := (le_max_right N M).trans (le_max_left _ _)
  have hKK : K≤D₀ := le_max_right _ _
  refine ⟨D₀,hN.trans hNN,?_⟩
  intro D hDN χ hA j d
  have hn := hh D (hNN.trans hDN)
  have hm := hM D (hMM.trans hDN)
  have hk := hK D (hKK.trans hDN)
  have hD : 1<D := by omega
  have hC0 : 36≤lemma121ConcreteConstant := by
    unfold lemma121ConcreteConstant
    have := lemma121_transition_constant_pos
    have := lemma121_exact_high_constant_pos
    linarith
  have hC1 : lemma121TransitionConstant≤lemma121ConcreteConstant := by
    unfold lemma121ConcreteConstant
    have := lemma121_exact_high_constant_pos
    linarith
  have hC2 : lemma121ExactHighConstant≤lemma121ConcreteConstant := by
    unfold lemma121ConcreteConstant
    have := lemma121_transition_constant_pos
    linarith
  have hLp : 0<lemma23PaperL D := by linarith [hn.2.1]
  have hTp : 0<lemma56PaperT D := Real.exp_pos _
  refine ⟨?_,?_,?_⟩
  · intro hd hdhi
    exact (lemma121_low_exponential_estimate χ hD hn.2.1 hc hn.2.2.1 hk j
      (by exact_mod_cast (show 0<d by omega)) hdhi).trans
      (mul_le_mul_of_nonneg_right hC0 (by positivity))
  · intro hdlo hdhi
    exact (lemma121_transition_estimate χ hD hn.2.1 hA hc hn.2.2.1 hm j hdlo hdhi).trans
      (mul_le_mul_of_nonneg_right hC1 (by positivity))
  · intro hdlo hdhi
    exact (lemma121_high_error_absorption χ hD hn.2.1 hA hc hn.2.2.1 hm j hdlo hdhi).trans
      (mul_le_mul_of_nonneg_right hC2 (by positivity))

end ZhangLS.Spec
