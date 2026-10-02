import ZhangLS.Spec.Lemma54EighthContour
import ZhangLS.Spec.Lemma54IntegrationByParts

/-! # Actual derivative integrals through order eight

Iₙ is the actual weighted oscillatory integral. I₀ agrees with the original
Delta on x>0, and each derivative is proved by dominated differentiation.
All Mellin endpoint limits and convergence are derived, not assumed.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex MeasureTheory Set Filter Asymptotics
open scoped Topology

noncomputable def lemma54EighthIntegral (D n : ℕ) (x : ℝ) : ℂ :=
  ∫ u : ℝ, lemma54WeightedKernel D x n (u:ℂ)

@[simp] theorem lemma54_eighth_integral_zero (D : ℕ) (x : ℝ) :
    lemma54EighthIntegral D 0 x = lemma53OscillatoryDelta D x := by
  simp only [lemma54EighthIntegral,lemma54WeightedKernel,pow_zero,one_mul,
    lemma53OscillatoryDelta]

theorem lemma54_eighth_integral_zero_actual {D : ℕ} (hD : 1<D) {x : ℝ} (hx : 0<x) :
    lemma54EighthIntegral D 0 x = lemma53PaperDelta D x := by
  rw [lemma54_eighth_integral_zero]
  exact (lemma53_mellin_oscillatory_identity hD hx).symm

/-- Exact derivative of the existing weighted kernel, at every order. -/
theorem lemma54_eighth_kernel_hasDerivAt (D n : ℕ) (x u : ℝ) :
    HasDerivAt (fun y : ℝ => lemma54WeightedKernel D y n (u:ℂ))
      (lemma54WeightedKernel D x (n+1) (u:ℂ)) x := by
  have hh := (lemma54_kernel_hasDerivAt D x u).const_mul (lemma54DerivativeFactor u^n)
  convert hh using 1
  · ext y
    simp only [lemma54WeightedKernel,lemma54ContourFactor,lemma54DerivativeFactor,
      Complex.ofReal_exp]
  · simp only [lemma54WeightedKernel,lemma54ContourFactor,lemma54DerivativeFactor,
      lemma54FirstKernel,Complex.ofReal_exp,pow_succ]
    ring

/-- Dominated differentiation for the genuine Iₙ integral. -/
theorem lemma54_eighth_integral_hasDerivAt {D n : ℕ} (hD : 1<D) (hn : n<8) (x : ℝ) :
    HasDerivAt (lemma54EighthIntegral D n) (lemma54EighthIntegral D (n+1) x) x := by
  have hcont (y : ℝ) : Continuous (fun u : ℝ => lemma54WeightedKernel D y n (u:ℂ)) := by
    unfold lemma54WeightedKernel lemma54ContourFactor lemma53OscillatoryKernel
    fun_prop
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun y u : ℝ => lemma54WeightedKernel D y n (u:ℂ))
    (F' := fun y u : ℝ => lemma54WeightedKernel D y (n+1) (u:ℂ))
    (bound := lemma54EighthMajorant D) (s := Set.univ) (by simp)
    (Eventually.of_forall fun y => (hcont y).aestronglyMeasurable)
    (lemma54_eighth_weighted_kernel_integrable hD (by omega : n≤8) x)
    (lemma54_eighth_weighted_kernel_integrable hD (by omega : n+1≤8) x).aestronglyMeasurable
    (Eventually.of_forall fun u y _ => lemma54_eighth_weighted_kernel_norm_real (by omega : n+1≤8) D y u)
    (lemma54_eighth_weighted_majorant_integrable hD)
    (Eventually.of_forall fun u y _ => lemma54_eighth_kernel_hasDerivAt D n y u)
  exact h.2

theorem lemma54_eighth_integral_continuous {D n : ℕ} (hD : 1<D) (hn : n≤8) :
    Continuous (lemma54EighthIntegral D n) := by
  apply continuous_of_dominated (bound := lemma54EighthMajorant D)
  · intro x
    exact (lemma54_eighth_weighted_kernel_integrable hD hn x).aestronglyMeasurable
  · intro x
    exact Eventually.of_forall (lemma54_eighth_weighted_kernel_norm_real hn D x)
  · exact lemma54_eighth_weighted_majorant_integrable hD
  · apply Eventually.of_forall
    intro u
    unfold lemma54WeightedKernel lemma53OscillatoryKernel
    fun_prop

/-- Global bound supplies the genuine x=0 Mellin endpoint. -/
theorem lemma54_eighth_integral_norm_bound {D n : ℕ} (hD : 1<D) (hn : n≤8)
    (hB : 1≤lemma53PaperScale D) (x : ℝ) :
    ‖lemma54EighthIntegral D n x‖ ≤
      2*lemma54EighthConstant*Real.sqrt Real.pi*Real.exp 19/lemma53PaperScale D := by
  have h := norm_integral_le_of_norm_le (lemma54_eighth_weighted_majorant_integrable hD)
    (Eventually.of_forall (lemma54_eighth_weighted_kernel_norm_real hn D x))
  exact h.trans (lemma54_eighth_weighted_majorant_integral_bound hD hB)

theorem lemma54_eighth_integral_large_range {D n : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) (hn : n≤8) {x : ℝ} (hx : 0<x)
    (hxhi : lemma51PaperT0 D^(51/50:ℝ)<x) :
    ‖lemma54EighthIntegral D n x‖ ≤ lemma54EighthDerivativeTail D x :=
  lemma54_eighth_weighted_large_range_estimate hD hL hn hx hxhi

theorem lemma54_eighth_integral_isBigO_atTop {D n : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) (hn : n≤8) {a : ℝ} (ha : 0<a) :
    lemma54EighthIntegral D n =O[atTop] (fun x : ℝ => x^(-a)) := by
  apply IsBigO.of_bound (lemma54EighthConstant*(4+2*Real.exp 1) +
    2*lemma54EighthConstant*Real.sqrt Real.pi*Real.exp 20)
  filter_upwards [lemma54_log_gaussian_le_rpow_eventually (lemma53_scale_pos hD) ha,
    lemma54_stretched_exp_le_rpow_eventually (lemma53_scale_pos hD) ha,
    eventually_gt_atTop (lemma51PaperT0 D^(51/50:ℝ)),
    eventually_gt_atTop (0:ℝ)] with x hfirst hsecond hxhi hx
  have he := lemma54_eighth_integral_large_range hD hL hn hx hxhi
  have h1 := mul_le_mul_of_nonneg_left hfirst
    (show 0≤lemma54EighthConstant*(4+2*Real.exp 1) by
      exact mul_nonneg lemma54_eighth_weighted_constant_pos.le (by positivity))
  have h2 := mul_le_mul_of_nonneg_left hsecond
    (show 0≤2*lemma54EighthConstant*Real.sqrt Real.pi*Real.exp 20 by
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) lemma54_eighth_weighted_constant_pos.le)
        (Real.sqrt_nonneg _)) (Real.exp_nonneg _))
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hx.le _)]
  unfold lemma54EighthDerivativeTail at he
  nlinarith only [he,h1,h2]

theorem lemma54_eighth_integral_isBigO_at_zero {D n : ℕ} (hD : 1<D)
    (hn : n≤8) (hB : 1≤lemma53PaperScale D) :
    lemma54EighthIntegral D n =O[𝓝[>] 0] (fun x : ℝ => x^(-(0:ℝ))) := by
  apply IsBigO.of_bound (2*lemma54EighthConstant*Real.sqrt Real.pi*Real.exp 19/lemma53PaperScale D)
  filter_upwards [] with x
  simpa only [neg_zero,Real.rpow_zero,norm_one,mul_one] using
    lemma54_eighth_integral_norm_bound hD hn hB x

theorem lemma54_eighth_integral_mellin_convergent {D n : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) (hn : n≤8) {s : ℂ} (hs : 0<s.re) :
    MellinConvergent (lemma54EighthIntegral D n) s := by
  apply mellinConvergent_of_isBigO_rpow
    ((lemma54_eighth_integral_continuous hD hn).continuousOn.locallyIntegrableOn measurableSet_Ioi)
    (lemma54_eighth_integral_isBigO_atTop hD hL hn (a := s.re+1) (by linarith))
    (by linarith) (lemma54_eighth_integral_isBigO_at_zero hD hn (lemma54_scale_ge_one hL)) hs

theorem lemma54_eighth_integral_boundary_products {D n : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) (hn : n≤8) {s : ℂ} (hs : 0<s.re) :
    Tendsto (fun x : ℝ => (x:ℂ)^s*lemma54EighthIntegral D n x) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun x : ℝ => (x:ℂ)^s*lemma54EighthIntegral D n x) atTop (𝓝 0) :=
  ⟨lemma54_cpow_mul_tendsto_at_zero hs
      (lemma54_eighth_integral_isBigO_at_zero hD hn (lemma54_scale_ge_one hL)),
    lemma54_cpow_mul_tendsto_atTop s
      (lemma54_eighth_integral_isBigO_atTop hD hL hn (a := s.re+1) (by linarith))⟩

/-- Each integration-by-parts step is on the actual integrals and has both
endpoint terms proved to vanish. -/
theorem lemma54_eighth_mellin_step {D n : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) (hn : n<8) {s : ℂ} (hs : 0<s.re) :
    s*mellin (lemma54EighthIntegral D n) s =
      -mellin (lemma54EighthIntegral D (n+1)) (s+1) := by
  have hb := lemma54_eighth_integral_boundary_products hD hL (by omega : n≤8) hs
  exact lemma54_mellin_integration_by_parts hs
    (fun x _ => lemma54_eighth_integral_hasDerivAt hD hn x)
    (lemma54_eighth_integral_mellin_convergent hD hL (by omega : n≤8) hs)
    (lemma54_eighth_integral_mellin_convergent hD hL (by omega : n+1≤8)
      (by simp only [add_re,one_re]; linarith)) hb.1 hb.2

/-- The zeroth Mellin integral is exactly the original δ, not a new definition. -/
theorem lemma54_eighth_zero_mellin_actual {D : ℕ} (hD : 1<D) (s : ℂ) :
    mellin (lemma54EighthIntegral D 0) s = lemma54PaperDeltaMellin D s := by
  unfold lemma54PaperDeltaMellin mellin
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [lemma54_eighth_integral_zero_actual hD hx]

end ZhangLS.Spec
