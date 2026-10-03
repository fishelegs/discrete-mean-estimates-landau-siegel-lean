import ZhangLS.Spec.Proposition71PrincipalEnvelopeWeights
import ZhangLS.Spec.Proposition71PrincipalLocalScales
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The actual fixed logarithmic loss from all principal exterior weights
is absorbed by the shorter-contour stretched exponential. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Filter
open scoped Topology
set_option maxHeartbeats 2500000

lemma proposition71_stretched_exponential_decay (A : ℝ) {δ : ℝ} (hδ : 0<δ) :
    Tendsto (fun x : ℝ => x^A*Real.exp (-(x^δ))) atTop (𝓝 0) := by
  have hh := (_root_.tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (A/δ) 1 (by norm_num)).comp
    (_root_.tendsto_rpow_atTop hδ)
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  have hp : (x^δ)^(A/δ)=x^A := by
    rw [←Real.rpow_mul hx]
    congr 1
    field_simp [hδ.ne']
  simp only [Function.comp_apply,hp,one_mul,neg_one_mul]

/-- The exact logarithmic order produced by the genuine four-variable
arithmetic budget, together with the local contour's L^3244 loss. -/
lemma proposition71_principal_outer_decay :
    Tendsto (fun D : ℕ => lemma23PaperL D^1642614*
      Real.exp (-(lemma23PaperL D^(1/10 : ℝ)))) atTop (𝓝 0) := by
  have hlog : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hh := (proposition71_stretched_exponential_decay ((1642614 : ℕ) : ℝ)
    (by norm_num : (0 : ℝ)<1/10)).comp hlog
  simpa only [Function.comp_apply,Real.rpow_natCast] using hh

/-- Every fixed positive coefficient constant admits the uniform smallness
threshold needed after the complete original prime sum. -/
theorem proposition71_principal_outer_rate (C : ℝ) (hC : 0≤C) (ε : ℝ) (hε : 0<ε) :
    ∃D₀ : ℕ, 2≤D₀ ∧ ∀D : ℕ, D₀≤D →
      C*(lemma23PaperL D^1642614*
        Real.exp (-(lemma23PaperL D^(1/10 : ℝ))))≤ε := by
  have ht := proposition71_principal_outer_decay.const_mul C
  simp only [mul_zero] at ht
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((tendsto_order.1 ht).2 ε hε)
  refine ⟨max 2 N,le_max_left _ _,?_⟩
  intro D hD
  exact (hN D ((le_max_right _ _).trans hD)).le

end ZhangLS.Spec
