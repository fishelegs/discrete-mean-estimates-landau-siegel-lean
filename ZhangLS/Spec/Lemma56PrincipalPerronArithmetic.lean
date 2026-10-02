import ZhangLS.Spec.Lemma56PrincipalPerronEdges

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set Metric
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

noncomputable def lemma56PrincipalPerronArithmeticIntegrand (B x : ℝ) (s : ℂ) : ℂ :=
  -(logDeriv riemannZeta s) * lemma56PerronComplexKernel B x s

noncomputable def lemma56PrincipalPerronRegularIntegrand (B x : ℝ) (s : ℂ) : ℂ :=
  -(logDeriv zetaPoleRemoved s) * lemma56PerronComplexKernel B x s

lemma lemma56_actual_principal_regular_perron_analytic {x : ℝ} (hx : 0 < x) (B : ℝ)
    {s : ℂ} (hre : 0 < s.re) (hR : zetaPoleRemoved s ≠ 0) :
    AnalyticAt ℂ (lemma56PrincipalPerronRegularIntegrand B x) s := by
  have hA := lemma55_actual_zeta_pole_removed_analyticAt hre
  have hs : s ≠ 0 := by intro he; simp [he] at hre
  exact (hA.deriv.div hA hR).neg.mul (lemma56_perron_complex_kernel_analytic hx B hs)

lemma lemma56_actual_principal_perron_pole_split (B x : ℝ) {s : ℂ}
    (hre : 0 < s.re) (hs1 : s ≠ 1) (hR : zetaPoleRemoved s ≠ 0) :
    lemma56PrincipalPerronArithmeticIntegrand B x s =
      lemma56PerronComplexKernel B x s / (s - 1) + lemma56PrincipalPerronRegularIntegrand B x s := by
  have hζ : riemannZeta s ≠ 0 := by
    intro he
    exact hR ((lemma55_actual_zeta_pole_removed_zero_iff hre).mpr he)
  unfold lemma56PrincipalPerronArithmeticIntegrand lemma56PrincipalPerronRegularIntegrand
  rw [lemma55_actual_zeta_pole_removed_logDeriv hre hs1 hζ]
  ring

end ZhangLS.Spec
