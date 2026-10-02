import ZhangLS.Spec.Lemma56PrincipalPerronKernel
import ZhangLS.Spec.Lemma56PerronMellinIdentity

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set Metric
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

lemma lemma56_actual_principal_perron_mellin_identity {B x : ℝ} (hB : 0 < B) (hx : 0 < x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
      -(logDeriv riemannZeta ((2 : ℂ) + (t : ℂ) * I)) * lemma56PerronKernel B 2 x t =
        lemma56PerronMangoldtSum (1 : DirichletCharacter ℂ 1) B x 0 := by
  have hi := lemma56_actual_perron_mellin_identity (1 : DirichletCharacter ℂ 1) hB hx 0
  rw [DirichletCharacter.LFunction_modOne_eq] at hi
  simpa only [ofReal_zero, zero_mul, sub_zero] using hi

end ZhangLS.Spec
