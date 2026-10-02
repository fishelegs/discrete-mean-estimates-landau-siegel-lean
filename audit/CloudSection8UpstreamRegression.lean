import ZhangLS.Spec.Section8UpstreamGeometry
set_option autoImplicit false
open Complex ZhangLS.Spec Section8Upstream Filter Topology
#print axioms Section8Upstream.eps
#print axioms Section8Upstream.t
#print axioms Section8Upstream.r
#print axioms Section8Upstream.F
#print axioms Section8Upstream.G
#print axioms Section8Upstream.paper_beta_scaled
#print axioms Section8Upstream.paper_beta_agreement
#print axioms Section8Upstream.smoothing_scaled
#print axioms Section8Upstream.smoothing_agreement
#print axioms Section8Upstream.alpha_log_P
#print axioms Section8Upstream.scale_log_rpow
#print axioms Section8Upstream.exponent_scaled
#print axioms Section8Upstream.actual_F_normalized
#print axioms Section8Upstream.G_scale
#print axioms Section8Upstream.actual_G_normalized
#print axioms Section8Upstream.all_F_at_zero
#print axioms Section8Upstream.all_G_at_zero
#print axioms Section8Upstream.log_D_tendsto
#print axioms Section8Upstream.eps_eq
#print axioms Section8Upstream.eps_tendsto
#print axioms Section8Upstream.continuous_t
#print axioms Section8Upstream.continuous_F
#print axioms Section8Upstream.continuous_G
#print axioms Section8Upstream.actual_F_tendsto
#print axioms Section8Upstream.actual_G_tendsto
#print axioms Section8Upstream.delta
#print axioms Section8Upstream.delta_eq
#print axioms Section8Upstream.delta_tendsto
#print axioms Section8Upstream.alpha_log_T_eq
#print axioms Section8Upstream.alpha_log_T_tendsto
#print axioms Section8Upstream.exact_log_P1
#print axioms Section8Upstream.exact_log_P2
#print axioms Section8Upstream.exact_log_ratio
#print axioms Section8Upstream.exact_pi_normalization
#print axioms Section8Upstream.cross_expansion
#print axioms Section8Upstream.cross_symmetrization
#print axioms ZhangLS.Spec.lemma84_paper_model_circle_integral
example (z : ℝ) : F 0 0 6 z=Section8.f16 z := (all_F_at_zero z).1
example (z : ℝ) : G 0 0 6 z=Section8.g16 z := (all_G_at_zero z).1
example {D : ℕ} (hL : 0<lemma23PaperL D) :
    Real.log (lemma84Section8P1 D/lemma84Section8P2 D)/Real.log (lemma23PaperP D)=1/250+Section8Upstream.delta D := exact_log_ratio hL
example (c : ℝ) (j : Fin 3) (μ : ℕ) (z : ℝ) :
    Tendsto (fun D : ℕ => lemma84MainTerm D c j μ ((lemma23PaperP D)^z)) atTop (𝓝 (G 0 j μ z)) := actual_G_tendsto c j μ z
