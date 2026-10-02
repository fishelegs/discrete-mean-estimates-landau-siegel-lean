import ZhangLS.Spec.Lemma54KernelDerivatives

/-! # The actual Δ, Δ′ and Δ″ identities on the positive real axis -/

namespace ZhangLS.Spec

open Complex MeasureTheory Set Filter
open scoped Topology

set_option maxHeartbeats 1000000

theorem lemma54_actual_delta_hasDerivAt {D : ℕ} (hD : 1 < D) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (lemma53PaperDelta D) (lemma54FirstIntegral D x) x := by
  apply (lemma54_oscillatory_hasDerivAt hD x).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact lemma53_mellin_oscillatory_identity hD hy

theorem lemma54_actual_delta_deriv {D : ℕ} (hD : 1 < D) {x : ℝ} (hx : 0 < x) :
    deriv (lemma53PaperDelta D) x = lemma54FirstIntegral D x :=
  (lemma54_actual_delta_hasDerivAt hD hx).deriv

theorem lemma54_actual_delta_first_deriv_formula {D : ℕ} (hD : 1 < D) {x : ℝ} (hx : 0 < x) :
    deriv (lemma53PaperDelta D) x =
      (-(2 * Real.pi : ℂ) * I) *
        (∫ u : ℝ, ((Real.exp u : ℂ) - 1) * lemma53OscillatoryKernel D x (u : ℂ)) := by
  rw [lemma54_actual_delta_deriv hD hx]
  unfold lemma54FirstIntegral lemma54FirstKernel lemma54DerivativeFactor
  simp_rw [mul_assoc]
  rw [integral_const_mul, integral_const_mul]

theorem lemma54_actual_delta_deriv_hasDerivAt {D : ℕ} (hD : 1 < D) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (deriv (lemma53PaperDelta D)) (lemma54SecondIntegral D x) x := by
  apply (lemma54_first_integral_hasDerivAt hD x).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact lemma54_actual_delta_deriv hD hy

theorem lemma54_actual_delta_second_deriv {D : ℕ} (hD : 1 < D) {x : ℝ} (hx : 0 < x) :
    deriv (deriv (lemma53PaperDelta D)) x = lemma54SecondIntegral D x :=
  (lemma54_actual_delta_deriv_hasDerivAt hD hx).deriv

theorem lemma54_derivative_factor_sq (u : ℝ) :
    lemma54DerivativeFactor u ^ 2 = -(4 * Real.pi ^ 2 : ℂ) * ((Real.exp u : ℂ) - 1) ^ 2 := by
  unfold lemma54DerivativeFactor
  ring_nf
  rw [I_sq]
  ring

theorem lemma54_actual_delta_second_deriv_formula {D : ℕ} (hD : 1 < D) {x : ℝ} (hx : 0 < x) :
    deriv (deriv (lemma53PaperDelta D)) x =
      -(4 * Real.pi ^ 2 : ℂ) *
        (∫ u : ℝ, ((Real.exp u : ℂ) - 1) ^ 2 * lemma53OscillatoryKernel D x (u : ℂ)) := by
  rw [lemma54_actual_delta_second_deriv hD hx]
  unfold lemma54SecondIntegral lemma54SecondKernel
  simp_rw [lemma54_derivative_factor_sq, mul_assoc]
  rw [integral_const_mul]

end ZhangLS.Spec
