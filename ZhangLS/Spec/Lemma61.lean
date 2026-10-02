import ZhangLS.Spec.Lemma61Approximation

/-! # Faithful original Lemma 6.1

Finite short-polynomial Gaussian inversion, actual original-left integral
decomposition and N approximation, actual full horizontal L edges and
uniform constants/thresholds yield lemma61_proved : Lemma61Target.
Original Psi, strict region and actual L/K/N/E1 are retained.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Real Topology
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

lemma lemma61_approximation_constant_pos : 0 < lemma61ApproximationConstant := by
  have hm2 : 0 ≤ lemma44InverseSquareMass := tsum_nonneg (fun _ => by positivity)
  have hm4 : 0 ≤ lemma61QuarterSeriesMass := tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)
  unfold lemma61ApproximationConstant lemma61LeftApproximationConstant
  positivity

noncomputable def lemma61ModulusThreshold : ℕ := ⌈Real.exp 64⌉₊ + 1

lemma lemma61_parameters_at_threshold {D : ℕ} (hD : lemma61ModulusThreshold ≤ D) :
    1 < D ∧ 64 ≤ lemma23PaperL D := by
  have hn : ⌈Real.exp 64⌉₊ ≤ D :=
    (Nat.le_succ _).trans hD
  have hx : Real.exp 64 ≤ (D : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hlog := Real.log_le_log (Real.exp_pos 64) hx
  rw [Real.log_exp] at hlog
  have he := Real.add_one_le_exp (64 : ℝ)
  refine ⟨?_,hlog⟩
  exact_mod_cast (show (1 : ℝ) < (D : ℝ) by linarith only [hx,he])

theorem lemma61_proved : Lemma61Target := by
  refine ⟨lemma61ApproximationConstant,1 / 8,lemma61_approximation_constant_pos,
    by norm_num,lemma61ModulusThreshold,?_⟩
  intro D p inst ψ hD hψ s hs
  have hp := lemma61_parameters_at_threshold hD
  exact lemma61_actual_approximation_bound ψ hψ hp.1 hp.2 hs

end ZhangLS.Spec
