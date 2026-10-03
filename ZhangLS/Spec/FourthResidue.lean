import ZhangLS.Spec.Lemma171ResidueBound

/-! The actual fourth-pole residue obtained by one further division by w. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex Metric Set
open scoped Classical

noncomputable def lemma171LogMellinIntegrand {D : ℕ}
    (χ : RealPrimitiveCharacter D) (w : ℂ) : ℂ := lemma171MellinIntegrand χ w / w

noncomputable def lemma171ActualLogResidue {D : ℕ} (χ : RealPrimitiveCharacter D) : ℂ :=
  iteratedDeriv 3 (lemma171RegularNumerator χ) 0 / (Nat.factorial 3 : ℂ)

lemma lemma171_log_regular_numerator_eq {D : ℕ} (χ : RealPrimitiveCharacter D)
    (w : ℂ) (hw : -1/2 < w.re) (h0 : w ≠ 0) :
    lemma171RegularNumerator χ w = w ^ 4 * lemma171LogMellinIntegrand χ w := by
  rw [lemma171_regular_numerator_eq χ w hw h0]
  unfold lemma171LogMellinIntegrand
  field_simp

lemma lemma171_actual_log_circle_integral_eq_residue {D : ℕ}
    (χ : RealPrimitiveCharacter D) (hD : 1 < D) (r : ℝ) (hr : 0 < r) (hs : r ≤ 1/4) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ * circleIntegral (lemma171LogMellinIntegrand χ) 0 r =
      lemma171ActualLogResidue χ := by
  have hd : DifferentiableOn ℂ (lemma171RegularNumerator χ) (closedBall 0 r) := by
    intro w hw
    have hn : ‖w‖ ≤ r := by simpa [mem_closedBall, dist_eq_norm] using hw
    have hb := (abs_le.mp ((Complex.abs_re_le_norm w).trans (hn.trans hs))).1
    exact (lemma171_regular_numerator_differentiableAt χ hD w (by linarith)).differentiableWithinAt
  have hc : circleIntegral (fun w : ℂ => 1 / w ^ 4 * lemma171RegularNumerator χ w) 0 r =
      ((2 * Real.pi * Complex.I : ℂ) / (Nat.factorial 3 : ℂ)) *
        iteratedDeriv 3 (lemma171RegularNumerator χ) 0 := by
    simpa only [sub_zero, smul_eq_mul, Nat.reduceAdd] using
      hd.circleIntegral_one_div_sub_center_pow_smul hr 3
  have he : circleIntegral (lemma171LogMellinIntegrand χ) 0 r =
      circleIntegral (fun w : ℂ => 1 / w ^ 4 * lemma171RegularNumerator χ w) 0 r := by
    apply circleIntegral.integral_congr hr.le
    intro w hw
    have hn : ‖w‖ = r := by simpa [mem_sphere, dist_eq_norm] using hw
    have h0 : w ≠ 0 := by intro h; rw [h, norm_zero] at hn; linarith
    have hb := (abs_le.mp ((Complex.abs_re_le_norm w).trans (hn.le.trans hs))).1
    change lemma171LogMellinIntegrand χ w = 1 / w ^ 4 * lemma171RegularNumerator χ w
    rw [lemma171_log_regular_numerator_eq χ w (by linarith) h0]
    field_simp
  rw [he, hc]
  unfold lemma171ActualLogResidue
  field_simp [Complex.two_pi_I_ne_zero]

lemma lemma171_third_deriv_mul (f g : ℂ → ℂ) (x : ℂ)
    (hf : AnalyticAt ℂ f x) (hg : AnalyticAt ℂ g x) :
    iteratedDeriv 3 (fun z => f z * g z) x =
      f x * iteratedDeriv 3 g x + 3 * deriv f x * iteratedDeriv 2 g x +
        3 * iteratedDeriv 2 f x * deriv g x + iteratedDeriv 3 f x * g x := by
  have h := iteratedDeriv_fun_mul (n := 3) (x := x) hf.contDiffAt hg.contDiffAt
  simpa [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one, Nat.choose,
    mul_assoc, add_assoc] using h

lemma lemma171_third_deriv_mul_square (f g : ℂ → ℂ) (x : ℂ)
    (hf : AnalyticAt ℂ f x) (hg : AnalyticAt ℂ g x) :
    iteratedDeriv 3 (fun z => f z * g z ^ 2) x / 6 =
      f x * deriv g x * iteratedDeriv 2 g x + deriv f x * (deriv g x) ^ 2 +
        g x * (f x * iteratedDeriv 3 g x / 3 +
          deriv f x * iteratedDeriv 2 g x + iteratedDeriv 2 f x * deriv g x +
          iteratedDeriv 3 f x * g x / 6) := by
  have h3 : iteratedDeriv 3 (fun z => g z ^ 2) x =
      g x * iteratedDeriv 3 g x + 3 * deriv g x * iteratedDeriv 2 g x +
        3 * iteratedDeriv 2 g x * deriv g x + iteratedDeriv 3 g x * g x := by
    simpa only [pow_two] using lemma171_third_deriv_mul g g x hg hg
  have h2 : iteratedDeriv 2 (fun z => g z ^ 2) x =
      g x * iteratedDeriv 2 g x + 2 * deriv g x * deriv g x +
        iteratedDeriv 2 g x * g x := by
    simpa only [pow_two] using lemma171_second_deriv_mul g g x hg hg
  rw [lemma171_third_deriv_mul f (fun z => g z ^ 2) x hf (hg.pow 2), h3, h2,
    deriv_fun_pow hg.differentiableAt]
  norm_num
  ring

/-- Exact decomposition: all remainder terms contain the genuine L(1,χ). -/
lemma lemma171_actual_log_residue_decomposition {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) :
    lemma171ActualLogResidue χ =
      lemma171AnalyticCorrection D 1 * LDerivAtOne χ *
        iteratedDeriv 2 (dirichletLFunction χ) 1 +
      deriv (lemma171ResiduePrefactor D) 0 * (LDerivAtOne χ) ^ 2 +
      LAtOne χ * (lemma171AnalyticCorrection D 1 *
          iteratedDeriv 3 (dirichletLFunction χ) 1 / 3 +
        deriv (lemma171ResiduePrefactor D) 0 * iteratedDeriv 2 (dirichletLFunction χ) 1 +
        iteratedDeriv 2 (lemma171ResiduePrefactor D) 0 * LDerivAtOne χ +
        iteratedDeriv 3 (lemma171ResiduePrefactor D) 0 * LAtOne χ / 6) := by
  have ha : AnalyticAt ℂ (fun w : ℂ => 1+w) 0 := by fun_prop
  have hl : AnalyticAt ℂ (fun w : ℂ => dirichletLFunction χ (1+w)) 0 :=
    ((differentiable_dirichletLFunction_of_one_lt_modulus χ hD).analyticAt 1).comp_of_eq ha (by simp)
  have hh := lemma171_third_deriv_mul_square (lemma171ResiduePrefactor D)
    (fun w : ℂ => dirichletLFunction χ (1+w)) 0 (lemma171_residue_prefactor_analyticAt D) hl
  unfold lemma171ActualLogResidue
  rw [lemma171_regular_numerator_factorization]
  norm_num only [Nat.factorial, Nat.cast_ofNat]
  rw [hh, lemma171_residue_prefactor_zero, deriv_comp_const_add,
    iteratedDeriv_comp_const_add, iteratedDeriv_comp_const_add]
  simp only [add_zero]
  rfl

lemma lemma171_prefactor_third_derivative_bound {D : ℕ} (hL : 2 ≤ lemma23PaperL D) :
    ‖iteratedDeriv 3 (lemma171ResiduePrefactor D) 0‖ ≤
      384 * lemma171PrefactorBound * lemma23PaperL D ^ 6 := by
  have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    3 (lemma171_residue_radius_properties hL).1 (lemma171_prefactor_diffContOnCl hL)
    (fun w hw => lemma171_prefactor_local_bound hL w (by
      exact le_of_eq (by simpa [mem_sphere, dist_eq_norm] using hw)))
  calc
    _ ≤ 6 * lemma171PrefactorBound / lemma171ResidueRadius D ^ 3 := by
      simpa [Nat.factorial] using hc
    _ = _ := by unfold lemma171ResidueRadius; field_simp; ring

end ZhangLS.Spec
