import ZhangLS.Spec.Proposition71MellinFiniteSum

/-! # The rigorous finite-prime Mellin estimate in (7.14)

The actual transform δ and positive hr/l scale are retained. This bound
comes from exact inversion plus proved absolute integrability and the original
Lemma5.4 bound. It is uniform over arbitrary finite coefficient sequences.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set Finset
open scoped Classical Topology
set_option maxHeartbeats 2000000

lemma proposition71_weighted_prime_polynomial_continuous
    (S : Finset ℕ) (hS : ∀ p∈S, 0<p) (a : ℕ → ℂ) :
    Continuous (fun t : ℝ => ∑ p∈S, a p*(p : ℂ)^((1 : ℂ)+(t : ℂ)*I)) := by
  apply continuous_finsetSum
  intro p hp
  apply continuous_const.mul
  exact Continuous.const_cpow (by fun_prop)
    (Or.inl (Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt (hS p hp))))

lemma proposition71_weighted_prime_polynomial_norm
    (S : Finset ℕ) (hS : ∀ p∈S, 0<p) (a : ℕ → ℂ) (t : ℝ) :
    ‖∑ p∈S, a p*(p : ℂ)^((1 : ℂ)+(t : ℂ)*I)‖ ≤
      ∑ p∈S, ‖a p‖*(p : ℝ) := by
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro p hp
  have hp' : 0<(p : ℝ) := by exact_mod_cast hS p hp
  rw [norm_mul,←Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos hp']
  simp

lemma proposition71_weighted_prime_kernel_integrable
    (S : Finset ℕ) (hS : ∀ p∈S, 0<p) (a : ℕ → ℂ) :
    Integrable (fun t : ℝ =>
      ‖∑ p∈S, a p*(p : ℂ)^((1 : ℂ)+(t : ℂ)*I)‖/(1+t^2)) := by
  have hcont := proposition71_weighted_prime_polynomial_continuous S hS a
  have hmeas : AEStronglyMeasurable (fun t : ℝ =>
      ‖∑ p∈S, a p*(p : ℂ)^((1 : ℂ)+(t : ℂ)*I)‖/(1+t^2)) :=
    (hcont.norm.div (by fun_prop) (fun t => by positivity)).aestronglyMeasurable
  apply (integrable_inv_one_add_sq.const_mul (∑ p∈S, ‖a p‖*(p : ℝ))).mono' hmeas
  apply ae_of_all
  intro t
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_right
    (proposition71_weighted_prime_polynomial_norm S hS a t) (by positivity : 0≤(1+t^2)⁻¹)

/-- Actual (7.14) with explicit constant and the previously missing hr factor. -/
theorem proposition71_actual_mellin_prime_bound {D : ℕ}
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) {h r l : ℝ}
    (hh : 0<h) (hr : 0<r) (hl : 0<l)
    (S : Finset ℕ) (hS : ∀ p∈S, 0<p) (a : ℕ → ℂ) :
    ‖∑ p∈S, a p*lemma53PaperDelta D (l/((p : ℝ)*h*r))‖ ≤
      (lemma54MellinStripConstant/(2*Real.pi))*lemma23PaperL D^3200*(h*r/l)*
        ∫ t : ℝ, ‖∑ p∈S, a p*(p : ℂ)^((1 : ℂ)+(t : ℂ)*I)‖/(1+t^2) := by
  let P : ℝ → ℂ := fun t => ∑ p∈S, a p*(p : ℂ)^((1 : ℂ)+(t : ℂ)*I)
  let F : ℝ → ℂ := fun t =>
    lemma54PaperDeltaMellin D ((1 : ℂ)+(t : ℂ)*I)*
      ((h*r/l : ℝ) : ℂ)^((1 : ℂ)+(t : ℂ)*I)*P t
  let K : ℝ := lemma54MellinStripConstant*lemma23PaperL D^3200*(h*r/l)
  have hCM := lemma54_mellin_strip_constant_pos
  have hLp : 0≤lemma23PaperL D := by linarith
  have hK : 0≤K := by dsimp [K]; positivity
  have hw : Integrable (fun t : ℝ => ‖P t‖/(1+t^2)) :=
    proposition71_weighted_prime_kernel_integrable S hS a
  have hbound (t : ℝ) : ‖F t‖≤K*(‖P t‖/(1+t^2)) := by
    have hb := lemma54_actual_mellin_closed_strip_bound hD hL
      (s := (1 : ℂ)+(t : ℂ)*I) (by norm_num) (by norm_num)
    have hn : ‖(1 : ℂ)+(t : ℂ)*I‖^2=1+t^2 := by
      rw [Complex.sq_norm,Complex.normSq_apply]
      simp [pow_two]
    rw [hn,Real.rpow_ofNat] at hb
    dsimp [F]
    rw [norm_mul,norm_mul,proposition71_extracted_scale_norm hh hr hl]
    calc
      _≤(lemma54MellinStripConstant*lemma23PaperL D^3200/(1+t^2))*(h*r/l)*‖P t‖ := by gcongr
      _=_ := by dsimp [K]; ring
  have hcontδ : Continuous (fun t : ℝ => lemma54PaperDeltaMellin D ((1 : ℂ)+(t : ℂ)*I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact ((lemma54_mellin_analyticOnNhd hD hL) _ (by norm_num)).continuousAt.comp (by fun_prop)
  have hcontR : Continuous (fun t : ℝ => ((h*r/l : ℝ) : ℂ)^((1 : ℂ)+(t : ℂ)*I)) :=
    Continuous.const_cpow (by fun_prop) (Or.inl (Complex.ofReal_ne_zero.mpr (by positivity)))
  have hcontP : Continuous P := proposition71_weighted_prime_polynomial_continuous S hS a
  have hF : Integrable F := (hw.const_mul K).mono'
    ((hcontδ.mul hcontR).mul hcontP).aestronglyMeasurable (ae_of_all _ hbound)
  have hi : (∫ t : ℝ, ‖F t‖)≤K*∫ t : ℝ, ‖P t‖/(1+t^2) := by
    rw [←integral_const_mul]
    exact integral_mono_ae hF.norm (hw.const_mul K) (ae_of_all _ hbound)
  rw [proposition71_actual_finite_mellin_sum hD hL (by norm_num : (1/2 : ℝ)≤1) hh hr hl S hS a]
  change ‖((1/(2*Real.pi) : ℝ) : ℂ)*∫ t : ℝ, F t‖≤_
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity : 0<(1/(2*Real.pi) : ℝ))]
  calc
    _≤(1/(2*Real.pi))*∫ t : ℝ, ‖F t‖ :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
    _≤(1/(2*Real.pi))*(K*∫ t : ℝ, ‖P t‖/(1+t^2)) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _=_ := by dsimp [K,P]; ring

end ZhangLS.Spec
