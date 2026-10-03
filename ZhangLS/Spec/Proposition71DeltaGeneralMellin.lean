import ZhangLS.Spec.Proposition71MellinDoubleSum
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Actual Δ inversion for a summable coefficient Dirichlet series on the
every actual line σ≥1/2 with summable coefficients. All series/integral interchanges are justified
by the actual δ vertical integrability; there is no assumed contour formula. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Filter
open scoped Topology
set_option maxHeartbeats 2500000

noncomputable def proposition71GeneralDeltaMellinKernel (D : ℕ) (σ x t : ℝ) : ℂ :=
  (x : ℂ)^(-((σ : ℂ)+(t : ℂ)*I))*lemma54PaperDeltaMellin D ((σ : ℂ)+(t : ℂ)*I)

noncomputable def proposition71GeneralDeltaDirichletTerm (D : ℕ) (σ : ℝ) (c : ℕ → ℂ) (Q : ℝ)
    (n : ℕ) (t : ℝ) : ℂ :=
  LSeries.term c ((σ : ℂ)+(t : ℂ)*I) n *
    (Q : ℂ)^((σ : ℂ)+(t : ℂ)*I)*lemma54PaperDeltaMellin D ((σ : ℂ)+(t : ℂ)*I)

lemma proposition71_general_delta_dirichlet_series_term_norm (D : ℕ) (σ : ℝ) (c : ℕ → ℂ)
    {Q : ℝ} (hQ : 0<Q) (n : ℕ) (t : ℝ) :
    ‖proposition71GeneralDeltaDirichletTerm D σ c Q n t‖=
      Q^σ*‖LSeries.term c (σ : ℂ) n‖*‖lemma54PaperDeltaMellin D ((σ : ℂ)+(t : ℂ)*I)‖ := by
  have ht : ‖LSeries.term c ((σ : ℂ)+(t : ℂ)*I) n‖=‖LSeries.term c (σ : ℂ) n‖ := by
    simp only [LSeries.norm_term_eq]
    norm_num
  unfold proposition71GeneralDeltaDirichletTerm
  rw [norm_mul,norm_mul,ht,Complex.norm_cpow_eq_rpow_re_of_pos hQ]
  have hsr : ((σ : ℂ)+(t : ℂ)*I).re=σ := by simp
  rw [hsr]
  ring

lemma proposition71_general_delta_dirichlet_series_term_kernel (D : ℕ) (σ : ℝ) (c : ℕ → ℂ)
    {Q : ℝ} (hQ : 0<Q) {n : ℕ} (hn : n≠0) (t : ℝ) :
    proposition71GeneralDeltaDirichletTerm D σ c Q n t=c n*proposition71GeneralDeltaMellinKernel D σ ((n : ℝ)/Q) t := by
  have hnp : 0<(n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have he := proposition71_positive_ratio_cpow hnp hQ (-((σ : ℂ)+(t : ℂ)*I))
  simp only [Complex.ofReal_natCast,neg_neg] at he
  unfold proposition71GeneralDeltaDirichletTerm proposition71GeneralDeltaMellinKernel
  rw [LSeries.term_of_ne_zero hn,he,Complex.cpow_neg]
  ring

lemma proposition71_general_delta_dirichlet_series_term_integrable {D : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) {σ : ℝ} (hσ : 1/2≤σ) (c : ℕ → ℂ) {Q : ℝ} (hQ : 0<Q) (n : ℕ) :
    Integrable (proposition71GeneralDeltaDirichletTerm D σ c Q n) := by
  by_cases hn : n=0
  · subst n
    have he : proposition71GeneralDeltaDirichletTerm D σ c Q 0=fun _ => 0 := by funext t; simp [proposition71GeneralDeltaDirichletTerm]
    rw [he]; exact integrable_zero _ _ _
  have hi := (proposition71_inverse_mellin_integrand_integrable hD hL hσ
    (div_pos (by exact_mod_cast Nat.pos_of_ne_zero hn : 0<(n : ℝ)) hQ)).const_mul (c n)
  apply hi.congr
  exact ae_of_all _ (fun t => by
    simpa only [proposition71GeneralDeltaMellinKernel,Complex.ofReal_div,Complex.ofReal_ofNat] using
      (proposition71_general_delta_dirichlet_series_term_kernel D σ c hQ hn t).symm)

lemma proposition71_general_delta_dirichlet_series_integral_norm_summable (D : ℕ) (σ : ℝ) (c : ℕ → ℂ)
    {Q : ℝ} (hQ : 0<Q) (hseries : LSeriesSummable c (σ : ℂ)) :
    Summable (fun n : ℕ => ∫t : ℝ, ‖proposition71GeneralDeltaDirichletTerm D σ c Q n t‖) := by
  have hn : Summable (fun n : ℕ => ‖LSeries.term c (σ : ℂ) n‖) := summable_norm_iff.mpr hseries
  let K := Q^σ*(∫t : ℝ, ‖lemma54PaperDeltaMellin D ((σ : ℂ)+(t : ℂ)*I)‖)
  apply (hn.mul_left K).congr
  intro n
  simp_rw [proposition71_general_delta_dirichlet_series_term_norm D σ c hQ,integral_const_mul]
  dsimp [K]
  ring

lemma proposition71_general_delta_dirichlet_series_tsum_integrable {D : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) {σ : ℝ} (hσ : 1/2≤σ) (c : ℕ → ℂ) {Q : ℝ} (hQ : 0<Q) (hseries : LSeriesSummable c (σ : ℂ)) :
    Integrable (fun t : ℝ => ∑' n, proposition71GeneralDeltaDirichletTerm D σ c Q n t) := by
  have hn : Summable (fun n : ℕ => ‖LSeries.term c (σ : ℂ) n‖) := summable_norm_iff.mpr hseries
  let K := Q^σ*(∑' n : ℕ, ‖LSeries.term c (σ : ℂ) n‖)
  have hδ : Integrable (fun t : ℝ => lemma54PaperDeltaMellin D ((σ : ℂ)+(t : ℂ)*I)) := by
    simpa only [VerticalIntegrable] using
      proposition71_actual_delta_vertical_integrable hD hL hσ
  apply (hδ.norm.const_mul K).mono' 
  · exact AEStronglyMeasurable.tsum (fun n => (proposition71_general_delta_dirichlet_series_term_integrable hD hL hσ c hQ n).1)
  · apply ae_of_all
    intro t
    have ht : Summable (fun n => ‖proposition71GeneralDeltaDirichletTerm D σ c Q n t‖) := by
      apply (hn.mul_left (Q^σ*‖lemma54PaperDeltaMellin D ((σ : ℂ)+(t : ℂ)*I)‖)).congr
      intro n
      rw [proposition71_general_delta_dirichlet_series_term_norm D σ c hQ]
      ring
    calc
      _≤∑' n, ‖proposition71GeneralDeltaDirichletTerm D σ c Q n t‖ := norm_tsum_le_tsum_norm ht
      _=∑' n, (Q^σ*‖lemma54PaperDeltaMellin D ((σ : ℂ)+(t : ℂ)*I)‖)*‖LSeries.term c (σ : ℂ) n‖ := by
        apply tsum_congr; intro n
        rw [proposition71_general_delta_dirichlet_series_term_norm D σ c hQ]
        ring
      _=K*‖lemma54PaperDeltaMellin D ((σ : ℂ)+(t : ℂ)*I)‖ := by rw [tsum_mul_left]; dsimp [K]; ring

lemma proposition71_general_delta_dirichlet_integral {D : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) {σ : ℝ} (hσ : 1/2≤σ) {x : ℝ} (hx : 0<x) :
    lemma53PaperDelta D x=((1/(2*Real.pi) : ℝ) : ℂ)*(∫t : ℝ, proposition71GeneralDeltaMellinKernel D σ x t) := by
  rw [←proposition71_actual_delta_mellin_inversion hD hL hσ hx]
  simp only [mellinInv, proposition71GeneralDeltaMellinKernel, Complex.real_smul, smul_eq_mul]

lemma proposition71_general_delta_dirichlet_series_term_integral {D : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) {σ : ℝ} (hσ : 1/2≤σ) (c : ℕ → ℂ)
    {Q : ℝ} (hQ : 0<Q) (n : ℕ) :
    ((1/(2*Real.pi) : ℝ) : ℂ)*(∫t : ℝ, proposition71GeneralDeltaDirichletTerm D σ c Q n t)=
      if n=0 then 0 else c n*lemma53PaperDelta D ((n : ℝ)/Q) := by
  by_cases hn : n=0
  · subst n; simp [proposition71GeneralDeltaDirichletTerm]
  rw [if_neg hn]
  simp_rw [proposition71_general_delta_dirichlet_series_term_kernel D σ c hQ hn,integral_const_mul]
  rw [proposition71_general_delta_dirichlet_integral hD hL hσ (div_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) hQ)]
  ring

/-- Actual inverse Mellin/Dirichlet-series interchange. All summability and
integrability conclusions are proved, with no mean-value or contour oracle. -/
theorem proposition71_actual_general_delta_dirichlet_series {D : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) {σ : ℝ} (hσ : 1/2≤σ) (c : ℕ → ℂ) {Q : ℝ} (hQ : 0<Q) (hseries : LSeriesSummable c (σ : ℂ)) :
    Integrable (fun t : ℝ => LSeries c ((σ : ℂ)+(t : ℂ)*I)*
      (Q : ℂ)^((σ : ℂ)+(t : ℂ)*I)*lemma54PaperDeltaMellin D ((σ : ℂ)+(t : ℂ)*I)) ∧
      Summable (fun n : ℕ => if n=0 then 0 else c n*lemma53PaperDelta D ((n : ℝ)/Q)) ∧
        ((1/(2*Real.pi) : ℝ) : ℂ)*(∫t : ℝ, LSeries c ((σ : ℂ)+(t : ℂ)*I)*
          (Q : ℂ)^((σ : ℂ)+(t : ℂ)*I)*lemma54PaperDeltaMellin D ((σ : ℂ)+(t : ℂ)*I))=
            ∑' n : ℕ, if n=0 then 0 else c n*lemma53PaperDelta D ((n : ℝ)/Q) := by
  have hpoint (t : ℝ) : (∑' n, proposition71GeneralDeltaDirichletTerm D σ c Q n t)=
      LSeries c ((σ : ℂ)+(t : ℂ)*I)*(Q : ℂ)^((σ : ℂ)+(t : ℂ)*I)*lemma54PaperDeltaMellin D ((σ : ℂ)+(t : ℂ)*I) := by
    unfold proposition71GeneralDeltaDirichletTerm LSeries
    rw [tsum_mul_right,tsum_mul_right]
  have hi := proposition71_general_delta_dirichlet_series_tsum_integrable hD hL hσ c hQ hseries
  have hint : Integrable (fun t : ℝ => LSeries c ((σ : ℂ)+(t : ℂ)*I)*
      (Q : ℂ)^((σ : ℂ)+(t : ℂ)*I)*lemma54PaperDeltaMellin D ((σ : ℂ)+(t : ℂ)*I)) :=
    hi.congr (ae_of_all _ hpoint)
  have hh := hasSum_integral_of_summable_integral_norm
    (fun n => proposition71_general_delta_dirichlet_series_term_integrable hD hL hσ c hQ n)
    (proposition71_general_delta_dirichlet_series_integral_norm_summable D σ c hQ hseries)
  have hs := hh.mul_left (((1/(2*Real.pi) : ℝ) : ℂ))
  simp_rw [proposition71_general_delta_dirichlet_series_term_integral hD hL hσ c hQ,hpoint] at hs
  exact ⟨hint,hs.summable,hs.tsum_eq.symm⟩

end ZhangLS.Spec
