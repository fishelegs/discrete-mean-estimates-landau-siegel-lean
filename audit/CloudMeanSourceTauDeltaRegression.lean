import ZhangLS.Spec.TauWeightedDeltaCoefficients
set_option autoImplicit false
open ZhangLS.Spec Complex Finset
open scoped Classical
example (D d:ℕ) (κ:ℕ→ℂ) (q:ℝ) : tauDeltaDilatedAbsolute D κ d q 0=0 := by
  simp [tauDeltaDilatedAbsolute]
example (D d:ℕ) (κ w:ℕ→ℂ) (q:ℝ) : tauDeltaDilatedTerm D κ w d q 0=0 := by
  simp [tauDeltaDilatedTerm]
example (D d n:ℕ) (w:ℕ→ℂ) (q:ℝ) : tauDeltaDilatedTerm D (fun _=>0) w d q n=0 := by
  simp [tauDeltaDilatedTerm]
example {D:ℕ} (hD:1<D) (hL:2000≤lemma23PaperL D) :
    Summable (fun n:ℕ=>(lemma34Tau 5 n:ℝ)*‖lemma53PaperDelta D ((n:ℝ)/lemma23PaperP D^10)‖) ∧
      (∑'n:ℕ,(lemma34Tau 5 n:ℝ)*‖lemma53PaperDelta D ((n:ℝ)/lemma23PaperP D^10)‖)≤
        tauDeltaAbsoluteConstant*lemma23PaperP D^10*lemma23PaperL D^575 := by
  apply tauDelta_actual_absolute_sum hD hL _ le_rfl
  exact one_le_pow₀ (Real.one_le_exp (by positivity))
example {D:ℕ} (hD:1<D) (hL:2000≤lemma23PaperL D) :
    ‖lemma53PaperDelta D 1‖≤tauDeltaUniformConstant :=
  tauDelta_actual_uniform_bound hD (by linarith) (by norm_num)
#print axioms ZhangLS.Spec.tauDeltaUniformConstant
#print axioms ZhangLS.Spec.tauDelta_uniform_constant_pos
#print axioms ZhangLS.Spec.tauDelta_actual_uniform_bound
#print axioms ZhangLS.Spec.tauDelta_tau_five_partial_sum
#print axioms ZhangLS.Spec.tauDelta_t0_cutoff
#print axioms ZhangLS.Spec.tauDelta_head_geometry
#print axioms ZhangLS.Spec.tauDelta_tail_scale
#print axioms ZhangLS.Spec.tauDelta_tau_five_square_summable
#print axioms ZhangLS.Spec.tauDelta_scaled_large_tail
#print axioms ZhangLS.Spec.tauDeltaHead
#print axioms ZhangLS.Spec.tauDelta_head_hasSum
#print axioms ZhangLS.Spec.tauDelta_term_majorant
#print axioms ZhangLS.Spec.tauDelta_actual_absolute_head_tail
#print axioms ZhangLS.Spec.tauDeltaAbsoluteConstant
#print axioms ZhangLS.Spec.tauDelta_absolute_constant_pos
#print axioms ZhangLS.Spec.tauDelta_actual_absolute_sum
#print axioms ZhangLS.Spec.tauDeltaDilatedAbsolute
#print axioms ZhangLS.Spec.tauDeltaDilatedTerm
#print axioms ZhangLS.Spec.tauDelta_dilated_absolute_majorant
#print axioms ZhangLS.Spec.tauDelta_actual_dilated_absolute_sum
#print axioms ZhangLS.Spec.tauDelta_dilated_term_norm_le
#print axioms ZhangLS.Spec.tauDelta_actual_dilated_character_sum
