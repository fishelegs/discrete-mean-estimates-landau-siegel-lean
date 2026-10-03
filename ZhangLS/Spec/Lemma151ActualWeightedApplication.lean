import ZhangLS.Spec.Lemma151ActualPointwiseDecay
import ZhangLS.Spec.Lemma151ActualWeightedSourceBudget
import ZhangLS.Spec.Lemma153DownstreamNormalization

/-! Only the actual finite pointwise-substitution contribution to (15.22).
Neither the smooth-tail truncation from (15.20), the rough varpi replacement
from (15.21), nor deletion of N(Q) is asserted by these theorems. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace ZhangLS.Spec
open Finset Complex Filter
open scoped Classical

noncomputable def actual151PaperVarpi {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (n : ℕ) : ℂ :=
  lemma153Varpi χ (lemma152PaperBeta D c) (lemma83PaperBeta D c j)
    (lemma153GeneralMEulerProduct χ (lemma152PaperBeta D c)) n

lemma actual151_pointwise_constant_nonneg {c : ℝ} (hc : 0<c) :
    0≤actual151PointwiseConstant c := by
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨D,hE,hL⟩ := ((actual151_pointwise_error_rate hc).and
    (ht.eventually_gt_atTop 0)).exists
  have hr : 0<actual151Rate D := Real.rpow_pos_of_pos hL _
  exact (mul_nonneg_iff_of_pos_right hr).mp (hE.1.trans hE.2)

/-- Actual finite substitution with the original smooth n1 domain, genuine
psi-basis arithmetic sum, actual varpi, and the proved terminal-residue main
constant. The stronger external character is retained in the error budget. -/
theorem actual151_actual_weighted_substitution_uniform (c : ℝ) (hc : 0<c) :
    ∃ D₀ : ℕ,2≤D₀ ∧ ∀ D : ℕ,D₀≤D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ → ∀ j : Fin 3,∀ S : Finset ℕ,
      (∀ n∈S,Lemma151Supported (lemma151Q D) n ∧ 0<n ∧ (n:ℝ)<lemma56PaperT D) →
      ‖(∑ n∈S,actual151PaperVarpi χ c j n/(n:ℂ)*
          lemma151ArithmeticSum χ c j (lemma151BPsi χ) n)-
        actual151MainConstant (j.val+1)*
          (∑ n∈S,χ.evalNat n*(lemma34Tau 2 n:ℂ)*actual151PaperVarpi χ c j n/(n:ℂ))‖≤
        (actual151PointwiseConstant c*actual151WeightedPrefixConstant)*
          lemma23PaperL D^(-7/2:ℝ) := by
  obtain ⟨D₁,hD₁,hpoint⟩ := actual151_repaired_power_uniform hc
  obtain ⟨D₂,hprefix⟩ := actual151_actual_paper_varpi_prefix c hc
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨D₃,hL⟩ := eventually_atTop.mp (ht.eventually_ge_atTop 1)
  refine ⟨max D₁ (max D₂ D₃),hD₁.trans (le_max_left _ _),?_⟩
  intro D hD χ hA j S hS
  have h1 : D₁≤D := (le_max_left _ _).trans hD
  have h2 : D₂≤D := (le_max_left _ _).trans ((le_max_right _ _).trans hD)
  have h3 : D₃≤D := (le_max_right _ _).trans ((le_max_right _ _).trans hD)
  have hL1 := hL D h3
  have hL0 : 0<lemma23PaperL D := by linarith
  let e : ℕ→ℂ := fun n => lemma151ArithmeticSum χ c j (lemma151BPsi χ) n-
    χ.evalNat n*(lemma34Tau 2 n:ℂ)*actual151MainConstant (j.val+1)
  have hpoint' (n : ℕ) (hn : n∈S) :
      ‖e n‖≤‖χ.evalNat n‖*(actual151PointwiseConstant c*actual151Rate D)*(lemma34Tau 2 n:ℝ) :=
    hpoint D h1 χ hA j n (hS n hn).1 (hS n hn).2.2
  have hprefix' :
      (∑ n∈S,‖χ.evalNat n‖*(lemma34Tau 2 n:ℝ)*‖actual151PaperVarpi χ c j n‖/(n:ℝ))≤
        actual151WeightedPrefixConstant*lemma23PaperL D^(22/5:ℝ) := by
    simpa only [actual151PaperVarpi,lemma34_tau2_eq_divisor_card] using
      hprefix D h2 χ j S (fun n hn => ⟨(hS n hn).2.1,(hS n hn).2.2.le⟩)
  have hscale : 0≤actual151PointwiseConstant c*actual151Rate D :=
    mul_nonneg (actual151_pointwise_constant_nonneg hc) (actual151_rate_nonneg D)
  have he :
      (∑ n∈S,actual151PaperVarpi χ c j n/(n:ℂ)*
        lemma151ArithmeticSum χ c j (lemma151BPsi χ) n)-
      actual151MainConstant (j.val+1)*
        (∑ n∈S,χ.evalNat n*(lemma34Tau 2 n:ℂ)*actual151PaperVarpi χ c j n/(n:ℂ)) =
      ∑ n∈S,actual151PaperVarpi χ c j n/(n:ℂ)*e n := by
    rw [mul_sum,←sum_sub_distrib]
    apply sum_congr rfl
    intro n hn
    dsimp [e]
    ring
  rw [he]
  calc
    _ ≤ ∑ n∈S,‖actual151PaperVarpi χ c j n/(n:ℂ)*e n‖ := norm_sum_le _ _
    _ ≤ ∑ n∈S,(‖actual151PaperVarpi χ c j n‖/(n:ℝ))*
        (‖χ.evalNat n‖*(actual151PointwiseConstant c*actual151Rate D)*(lemma34Tau 2 n:ℝ)) := by
      apply sum_le_sum
      intro n hn
      rw [norm_mul,norm_div,norm_natCast]
      exact mul_le_mul_of_nonneg_left (hpoint' n hn)
        (div_nonneg (norm_nonneg _) (Nat.cast_nonneg _))
    _ = (actual151PointwiseConstant c*actual151Rate D)*
        (∑ n∈S,‖χ.evalNat n‖*(lemma34Tau 2 n:ℝ)*‖actual151PaperVarpi χ c j n‖/(n:ℝ)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro n hn
      ring
    _ ≤ (actual151PointwiseConstant c*actual151Rate D)*
        (actual151WeightedPrefixConstant*lemma23PaperL D^(22/5:ℝ)) :=
      mul_le_mul_of_nonneg_left hprefix' hscale
    _ = (actual151PointwiseConstant c*actual151WeightedPrefixConstant)*
        (actual151Rate D*lemma23PaperL D^(22/5:ℝ)) := by ring
    _ = _ := by rw [actual151_outer_four_log_scale hL0]

/-- Multiplication by the actual M(1,1;1-beta_j) has an absolute cost already
proved for the original Section 15 normalization. This still bounds only the
finite pointwise-substitution contribution to (15.22). -/
theorem actual151_actual_M_weighted_substitution_uniform (c : ℝ) (hc : 0<c) :
    ∃ D₀ : ℕ,2≤D₀ ∧ ∀ D : ℕ,D₀≤D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ → ∀ j : Fin 3,∀ S : Finset ℕ,
      (∀ n∈S,Lemma151Supported (lemma151Q D) n ∧ 0<n ∧ (n:ℝ)<lemma56PaperT D) →
      let M := lemma153GeneralMEulerProduct χ (lemma152PaperBeta D c) 1 1
        (1-lemma83PaperBeta D c j)
      ‖M*(∑ n∈S,actual151PaperVarpi χ c j n/(n:ℂ)*
          lemma151ArithmeticSum χ c j (lemma151BPsi χ) n)-
        M*actual151MainConstant (j.val+1)*
          (∑ n∈S,χ.evalNat n*(lemma34Tau 2 n:ℂ)*actual151PaperVarpi χ c j n/(n:ℂ))‖≤
        (lemma152ProductBound*(actual151PointwiseConstant c*actual151WeightedPrefixConstant))*
          lemma23PaperL D^(-7/2:ℝ) := by
  obtain ⟨D₀,hD₀,h⟩ := actual151_actual_weighted_substitution_uniform c hc
  refine ⟨D₀,hD₀,?_⟩
  intro D hD χ hA j S hS
  dsimp only
  have hM := lemma153_general_M_normalization_uniform_bound χ (lemma152PaperBeta D c)
    (lemma152_beta_re D c) (lemma83PaperBeta D c j) (lemma83_beta_re D c j)
  have he := h D hD χ hA j S hS
  rw [mul_assoc,←mul_sub,norm_mul]
  exact (mul_le_mul hM he (norm_nonneg _) lemma152_product_bound_pos.le).trans_eq (by ring)

end ZhangLS.Spec
