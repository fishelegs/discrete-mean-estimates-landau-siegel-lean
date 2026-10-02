import ZhangLS.Spec.Lemma171ResidueBound
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Absolute uniform thresholds for the Lemma 17.1 analytic errors -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Filter
open scoped Topology
set_option maxHeartbeats 2000000

lemma lemma171_log_tendsto_atTop :
    Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))

/-- The paper's T scale beats every fixed power of D and every fixed log power.
This is a proved numerical absorption theorem, not a contour-bound hypothesis. -/
lemma lemma171_subexponential_absorption (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c)
    (k n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ D₀ : ℕ, 2 ≤ D₀ ∧ ∀ D : ℕ, D₀ ≤ D →
      C*(D : ℝ)^k*lemma23PaperL D^n*
        Real.exp (-c*lemma23PaperL D^(11/10 : ℝ)) < ε := by
  have hlog := lemma171_log_tendsto_atTop
  have hpow : Tendsto (fun D : ℕ => lemma23PaperL D^(1/10 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/10)).comp hlog
  have hsmall : Tendsto (fun D : ℕ => C*(lemma23PaperL D^n*Real.exp (-lemma23PaperL D)))
      atTop (𝓝 0) := by
    have hh := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n : ℝ) 1 (by norm_num)).comp hlog
    simpa only [Real.rpow_natCast,one_mul,neg_one_mul,mul_zero,Function.comp_apply] using hh.const_mul C
  have he : ∀ᶠ D : ℕ in atTop,
      2 ≤ D ∧ C*(D : ℝ)^k*lemma23PaperL D^n*
        Real.exp (-c*lemma23PaperL D^(11/10 : ℝ)) < ε := by
    filter_upwards [eventually_ge_atTop (2 : ℕ),hlog.eventually (eventually_ge_atTop 1),
      hpow.eventually (eventually_ge_atTop (((k : ℝ)+1)/c)),
      hsmall.eventually (eventually_lt_nhds hε)] with D hD hL hratio hsmallD
    refine ⟨hD,?_⟩
    let L := lemma23PaperL D
    have hL0 : 0 < L := by dsimp [L]; linarith
    have hq : L^(11/10 : ℝ) = L*L^(1/10 : ℝ) := by
      calc
        _ = L^(1+(1/10 : ℝ)) := by norm_num
        _ = L^((1 : ℝ))*L^(1/10 : ℝ) := Real.rpow_add hL0 _ _
        _ = _ := by rw [Real.rpow_one]
    have hdom : ((k : ℝ)+1)*L ≤ c*L^(11/10 : ℝ) := by
      have hr : (k : ℝ)+1 ≤ L^(1/10 : ℝ)*c := (div_le_iff₀ hc).mp hratio
      rw [hq]
      nlinarith [mul_le_mul_of_nonneg_right hr hL0.le]
    have hDreal : 0 < (D : ℝ) := Nat.cast_pos.mpr (by omega)
    have hDexp : (D : ℝ)^k = Real.exp ((k : ℝ)*L) := by
      dsimp [L,lemma23PaperL]
      rw [Real.exp_nat_mul,Real.exp_log hDreal]
    have hbound : C*(D : ℝ)^k*L^n*Real.exp (-c*L^(11/10 : ℝ)) ≤
        C*(L^n*Real.exp (-L)) := by
      rw [hDexp]
      calc
        _ = C*L^n*Real.exp ((k : ℝ)*L-c*L^(11/10 : ℝ)) := by
          rw [sub_eq_add_neg,Real.exp_add]
          ring
        _ ≤ C*L^n*Real.exp (-L) := mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (by linarith)) (mul_nonneg hC (pow_nonneg hL0.le _))
        _ = _ := by ring
    exact hbound.trans_lt hsmallD
  obtain ⟨D₀,hD₀⟩ := eventually_atTop.mp he
  refine ⟨max 2 D₀,le_max_left _ _,?_⟩
  intro D hD
  exact (hD₀ D ((le_max_right _ _).trans hD)).2

/-- Uniform o(1) for the actual residue, under exactly the normalized (A). -/
lemma lemma171_uniform_residue_error (ε : ℝ) (hε : 0 < ε) :
    ∃ D₀ : ℕ, 2 ≤ D₀ ∧ ∀ D : ℕ, D₀ ≤ D →
      ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
        ‖lemma171ActualResidue χ-(lemma171MainTerm χ : ℂ)‖ < ε := by
  have hlog := lemma171_log_tendsto_atTop
  have ht : Tendsto (fun D : ℕ => lemma171ResidueErrorConstant*
      lemma23PaperL D^(-2018 : ℤ)) atTop (𝓝 0) := by
    simpa only [mul_zero,Function.comp_apply] using
      ((tendsto_zpow_atTop_zero (by norm_num : (-2018 : ℤ) < 0)).comp hlog).const_mul
        lemma171ResidueErrorConstant
  have he : ∀ᶠ D : ℕ in atTop,
      2 ≤ D ∧ 2 ≤ lemma23PaperL D ∧ lemma171ResidueErrorConstant*
        lemma23PaperL D^(-2018 : ℤ) < ε := by
    filter_upwards [eventually_ge_atTop (2 : ℕ),hlog.eventually (eventually_ge_atTop 2),
      ht.eventually (eventually_lt_nhds hε)] with D hD hL hsmall
    exact ⟨hD,hL,hsmall⟩
  obtain ⟨D₀,hD₀⟩ := eventually_atTop.mp he
  refine ⟨max 2 D₀,le_max_left _ _,?_⟩
  intro D hD χ hA
  have hh := hD₀ D ((le_max_right _ _).trans hD)
  exact (lemma171_actual_residue_error_bound χ (by omega) hh.2.1 hA).trans_lt hh.2.2

end ZhangLS.Spec
