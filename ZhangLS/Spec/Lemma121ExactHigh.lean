import ZhangLS.Spec.Lemma121Ranges

/-! # Source-repaired high-range part of Lemma 12.1
The exact phase replaces the unsupported printed 10^-5 linearization.
This is explicitly not a proof of Lemma121PrintedHighTarget. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace ZhangLS.Spec
open Complex Finset Filter Topology
open scoped Real

noncomputable def lemma121ExactHighConstant : ℝ := 20+2*lemma82LocalErrorConstant
lemma lemma121_exact_high_constant_pos : 0<lemma121ExactHighConstant := by
  unfold lemma121ExactHighConstant
  positivity [lemma82_local_error_constant_pos]

lemma lemma121_high_error_absorption {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) (hA : NormalizedAssumptionA χ)
    {c : ℝ} (hc : 0<c) (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10)
    (htail : ∀ x : ℝ, lemma56PaperT D<x → (D:ℝ)/x≤lemma23PaperL D^(-15:ℤ))
    (j : Fin 3) {d : ℝ} (hdlo : lemma121PDoublePrimeOne D<d) (hdhi : d<lemma121P2 D) :
    ‖lemma121Sum χ c j d-lemma121ExactMain χ c j d‖≤
      lemma121ExactHighConstant*lemma23PaperL D^(-15:ℤ) := by
  have hg := lemma121_endpoint_geometry hD hL
  have hr := lemma121_high_range_geometry hD hL hdlo hdhi
  have hQ : 0<Real.log (lemma121P1 D) := zero_lt_one.trans_le hg.2.2.2.2.1
  have hLp : 0<lemma23PaperL D := by linarith
  have hx : 0<lemma121PDoublePrimeTwo D/d := zero_lt_one.trans_le hr.2.1
  have he := lemma121_actual_exact_phase_bound χ hD hL hA hc hsmall j
    hg.1 hg.2.1 hdlo hQ hg.2.2.1 hr.2.1 hr.2.2
  have hco : (4*Real.log (lemma121PDoublePrimeTwo D/lemma121PDoublePrimeOne D)+16)/
      Real.log (lemma121P1 D)≤20 := by
    apply (div_le_iff₀ hQ).mpr
    have hh := hg.2.2.2.2.2.2
    have hq := hg.2.2.2.2.1
    nlinarith
  have hco0 : 0≤(4*Real.log (lemma121PDoublePrimeTwo D/lemma121PDoublePrimeOne D)+16)/
      Real.log (lemma121P1 D) := by
    rw [hg.2.2.2.2.2.1]
    positivity
  have hfirst : (4*Real.log (lemma121PDoublePrimeTwo D/lemma121PDoublePrimeOne D)+16)*(D:ℝ)/
      (Real.log (lemma121P1 D)*(lemma121PDoublePrimeTwo D/d))≤20*lemma23PaperL D^(-15:ℤ) := by
    calc
      _ = ((4*Real.log (lemma121PDoublePrimeTwo D/lemma121PDoublePrimeOne D)+16)/
          Real.log (lemma121P1 D))*((D:ℝ)/(lemma121PDoublePrimeTwo D/d)) := by ring
      _ ≤ 20*lemma23PaperL D^(-15:ℤ) :=
        mul_le_mul hco (htail _ hr.1) (by positivity) (by norm_num)
  have hsecond : lemma82LocalErrorConstant*lemma23PaperL D^(-6:ℤ)/Real.log (lemma121P1 D)≤
      2*lemma82LocalErrorConstant*lemma23PaperL D^(-15:ℤ) := by
    rw [lemma121_log_P1]
    have heq : lemma82LocalErrorConstant*lemma23PaperL D^(-6:ℤ)/
        ((63/125:ℝ)*lemma23PaperL D^9)=
        (125/63:ℝ)*lemma82LocalErrorConstant*lemma23PaperL D^(-15:ℤ) := by
      rw [zpow_neg,zpow_neg,zpow_ofNat,zpow_ofNat]
      field_simp
    rw [heq]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by norm_num : (125/63:ℝ)≤2)
        lemma82_local_error_constant_pos.le) (by positivity)
  apply he.trans ((add_le_add hfirst hsecond).trans_eq _)
  unfold lemma121ExactHighConstant
  ring

/-- Uniform exact-phase replacement on the full original high range.
The absolute constant precedes the fixed shared c′. -/
def Lemma121ExactHighTarget : Prop :=
  ∃ C : ℝ, 0<C ∧ ∀ c : ℝ, 0<c → ∃ D₀ : ℕ, 2≤D₀ ∧
    ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ → ∀ j : Fin 3, ∀ d : ℝ,
      lemma121PDoublePrimeOne D<d → d<lemma121P2 D →
      ‖lemma121Sum χ c j d-lemma121ExactMain χ c j d‖≤C*lemma23PaperL D^(-15:ℤ)

/-- Complete actual exact-phase high-range theorem. The two low-range
branches of the printed lemma are outside this theorem's scope. -/
theorem lemma121_exact_high_proved : Lemma121ExactHighTarget := by
  refine ⟨lemma121ExactHighConstant,lemma121_exact_high_constant_pos,?_⟩
  intro c hc
  obtain ⟨N,hN,hh⟩ := lemma82_uniform_threshold c hc
  obtain ⟨M,hM⟩ := Filter.eventually_atTop.mp lemma121_tail_absorption_eventually
  refine ⟨max N M,hN.trans (le_max_left _ _),?_⟩
  intro D hDN χ hA j d hdlo hdhi
  have hn := hh D ((le_max_left N M).trans hDN)
  have hm := hM D ((le_max_right N M).trans hDN)
  exact lemma121_high_error_absorption χ (by omega) hn.2.1 hA hc hn.2.2.1 hm j hdlo hdhi

end ZhangLS.Spec
