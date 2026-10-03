import ZhangLS.Spec.Proposition71MellinDoubleSum
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Actual Δ inversion for a summable coefficient Dirichlet series on the
literal 3/2 line of source (7.19). All series/integral interchanges are justified
by the actual δ vertical integrability; there is no assumed contour formula. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Filter
open scoped Topology
set_option maxHeartbeats 2500000

noncomputable def proposition71DeltaMellinKernel (D : ℕ) (x t : ℝ) : ℂ :=
  (x : ℂ)^(-((3/2 : ℂ)+(t : ℂ)*I))*lemma54PaperDeltaMellin D ((3/2 : ℂ)+(t : ℂ)*I)

noncomputable def proposition71DeltaDirichletTerm (D : ℕ) (c : ℕ → ℂ) (Q : ℝ)
    (n : ℕ) (t : ℝ) : ℂ :=
  LSeries.term c ((3/2 : ℂ)+(t : ℂ)*I) n *
    (Q : ℂ)^((3/2 : ℂ)+(t : ℂ)*I)*lemma54PaperDeltaMellin D ((3/2 : ℂ)+(t : ℂ)*I)

lemma proposition71_delta_dirichlet_series_term_norm (D : ℕ) (c : ℕ → ℂ)
    {Q : ℝ} (hQ : 0<Q) (n : ℕ) (t : ℝ) :
    ‖proposition71DeltaDirichletTerm D c Q n t‖=
      Q^(3/2 : ℝ)*‖LSeries.term c (3/2 : ℂ) n‖*‖lemma54PaperDeltaMellin D ((3/2 : ℂ)+(t : ℂ)*I)‖ := by
  have ht : ‖LSeries.term c ((3/2 : ℂ)+(t : ℂ)*I) n‖=‖LSeries.term c (3/2 : ℂ) n‖ := by
    simp only [LSeries.norm_term_eq]
    norm_num
  unfold proposition71DeltaDirichletTerm
  rw [norm_mul,norm_mul,ht,Complex.norm_cpow_eq_rpow_re_of_pos hQ]
  have hsr : ((3/2 : ℂ)+(t : ℂ)*I).re=(3/2 : ℝ) := by norm_num
  rw [hsr]
  ring

lemma proposition71_delta_dirichlet_series_term_kernel (D : ℕ) (c : ℕ → ℂ)
    {Q : ℝ} (hQ : 0<Q) {n : ℕ} (hn : n≠0) (t : ℝ) :
    proposition71DeltaDirichletTerm D c Q n t=c n*proposition71DeltaMellinKernel D ((n : ℝ)/Q) t := by
  have hnp : 0<(n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have he := proposition71_positive_ratio_cpow hnp hQ (-((3/2 : ℂ)+(t : ℂ)*I))
  simp only [Complex.ofReal_natCast,neg_neg] at he
  unfold proposition71DeltaDirichletTerm proposition71DeltaMellinKernel
  rw [LSeries.term_of_ne_zero hn,he,Complex.cpow_neg]
  ring

lemma proposition71_delta_dirichlet_series_term_integrable {D : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) (c : ℕ → ℂ) {Q : ℝ} (hQ : 0<Q) (n : ℕ) :
    Integrable (proposition71DeltaDirichletTerm D c Q n) := by
  by_cases hn : n=0
  · subst n
    have he : proposition71DeltaDirichletTerm D c Q 0=fun _ => 0 := by funext t; simp [proposition71DeltaDirichletTerm]
    rw [he]; exact integrable_zero _ _ _
  have hi := (proposition71_inverse_mellin_integrand_integrable hD hL (by norm_num : (1/2:ℝ)≤3/2)
    (div_pos (by exact_mod_cast Nat.pos_of_ne_zero hn : 0<(n : ℝ)) hQ)).const_mul (c n)
  apply hi.congr
  exact ae_of_all _ (fun t => by
    simpa only [proposition71DeltaMellinKernel,Complex.ofReal_div,Complex.ofReal_ofNat] using
      (proposition71_delta_dirichlet_series_term_kernel D c hQ hn t).symm)

lemma proposition71_delta_dirichlet_series_integral_norm_summable (D : ℕ) (c : ℕ → ℂ)
    {Q : ℝ} (hQ : 0<Q) (hseries : LSeriesSummable c (3/2 : ℂ)) :
    Summable (fun n : ℕ => ∫t : ℝ, ‖proposition71DeltaDirichletTerm D c Q n t‖) := by
  have hn : Summable (fun n : ℕ => ‖LSeries.term c (3/2 : ℂ) n‖) := summable_norm_iff.mpr hseries
  let K := Q^(3/2 : ℝ)*(∫t : ℝ, ‖lemma54PaperDeltaMellin D ((3/2 : ℂ)+(t : ℂ)*I)‖)
  apply (hn.mul_left K).congr
  intro n
  simp_rw [proposition71_delta_dirichlet_series_term_norm D c hQ,integral_const_mul]
  dsimp [K]
  ring

lemma proposition71_delta_dirichlet_series_tsum_integrable {D : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) (c : ℕ → ℂ) {Q : ℝ} (hQ : 0<Q) (hseries : LSeriesSummable c (3/2 : ℂ)) :
    Integrable (fun t : ℝ => ∑' n, proposition71DeltaDirichletTerm D c Q n t) := by
  have hn : Summable (fun n : ℕ => ‖LSeries.term c (3/2 : ℂ) n‖) := summable_norm_iff.mpr hseries
  let K := Q^(3/2 : ℝ)*(∑' n : ℕ, ‖LSeries.term c (3/2 : ℂ) n‖)
  have hδ : Integrable (fun t : ℝ => lemma54PaperDeltaMellin D ((3/2 : ℂ)+(t : ℂ)*I)) := by
    simpa only [VerticalIntegrable,Complex.ofReal_div,Complex.ofReal_ofNat] using
      proposition71_actual_delta_vertical_integrable hD hL (by norm_num : (1/2:ℝ)≤3/2)
  apply (hδ.norm.const_mul K).mono' 
  · exact AEStronglyMeasurable.tsum (fun n => (proposition71_delta_dirichlet_series_term_integrable hD hL c hQ n).1)
  · apply ae_of_all
    intro t
    have ht : Summable (fun n => ‖proposition71DeltaDirichletTerm D c Q n t‖) := by
      apply (hn.mul_left (Q^(3/2 : ℝ)*‖lemma54PaperDeltaMellin D ((3/2 : ℂ)+(t : ℂ)*I)‖)).congr
      intro n
      rw [proposition71_delta_dirichlet_series_term_norm D c hQ]
      ring
    calc
      _≤∑' n, ‖proposition71DeltaDirichletTerm D c Q n t‖ := norm_tsum_le_tsum_norm ht
      _=∑' n, (Q^(3/2 : ℝ)*‖lemma54PaperDeltaMellin D ((3/2 : ℂ)+(t : ℂ)*I)‖)*‖LSeries.term c (3/2 : ℂ) n‖ := by
        apply tsum_congr; intro n
        rw [proposition71_delta_dirichlet_series_term_norm D c hQ]
        ring
      _=K*‖lemma54PaperDeltaMellin D ((3/2 : ℂ)+(t : ℂ)*I)‖ := by rw [tsum_mul_left]; dsimp [K]; ring

lemma proposition71_delta_dirichlet_integral {D : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) {x : ℝ} (hx : 0<x) :
    lemma53PaperDelta D x=((1/(2*Real.pi) : ℝ) : ℂ)*(∫t : ℝ, proposition71DeltaMellinKernel D x t) := by
  rw [←proposition71_actual_delta_mellin_inversion hD hL (by norm_num : (1/2:ℝ)≤3/2) hx]
  simp only [mellinInv, proposition71DeltaMellinKernel, Complex.real_smul, smul_eq_mul,
    Complex.ofReal_div,Complex.ofReal_ofNat]

lemma proposition71_delta_dirichlet_series_term_integral {D : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) (c : ℕ → ℂ)
    {Q : ℝ} (hQ : 0<Q) (n : ℕ) :
    ((1/(2*Real.pi) : ℝ) : ℂ)*(∫t : ℝ, proposition71DeltaDirichletTerm D c Q n t)=
      if n=0 then 0 else c n*lemma53PaperDelta D ((n : ℝ)/Q) := by
  by_cases hn : n=0
  · subst n; simp [proposition71DeltaDirichletTerm]
  rw [if_neg hn]
  simp_rw [proposition71_delta_dirichlet_series_term_kernel D c hQ hn,integral_const_mul]
  rw [proposition71_delta_dirichlet_integral hD hL (div_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) hQ)]
  ring

/-- Actual inverse Mellin/Dirichlet-series interchange. All summability and
integrability conclusions are proved, with no mean-value or contour oracle. -/
theorem proposition71_actual_delta_dirichlet_series {D : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) (c : ℕ → ℂ) {Q : ℝ} (hQ : 0<Q) (hseries : LSeriesSummable c (3/2 : ℂ)) :
    Integrable (fun t : ℝ => LSeries c ((3/2 : ℂ)+(t : ℂ)*I)*
      (Q : ℂ)^((3/2 : ℂ)+(t : ℂ)*I)*lemma54PaperDeltaMellin D ((3/2 : ℂ)+(t : ℂ)*I)) ∧
      Summable (fun n : ℕ => if n=0 then 0 else c n*lemma53PaperDelta D ((n : ℝ)/Q)) ∧
        ((1/(2*Real.pi) : ℝ) : ℂ)*(∫t : ℝ, LSeries c ((3/2 : ℂ)+(t : ℂ)*I)*
          (Q : ℂ)^((3/2 : ℂ)+(t : ℂ)*I)*lemma54PaperDeltaMellin D ((3/2 : ℂ)+(t : ℂ)*I))=
            ∑' n : ℕ, if n=0 then 0 else c n*lemma53PaperDelta D ((n : ℝ)/Q) := by
  have hpoint (t : ℝ) : (∑' n, proposition71DeltaDirichletTerm D c Q n t)=
      LSeries c ((3/2 : ℂ)+(t : ℂ)*I)*(Q : ℂ)^((3/2 : ℂ)+(t : ℂ)*I)*lemma54PaperDeltaMellin D ((3/2 : ℂ)+(t : ℂ)*I) := by
    unfold proposition71DeltaDirichletTerm LSeries
    rw [tsum_mul_right,tsum_mul_right]
  have hi := proposition71_delta_dirichlet_series_tsum_integrable hD hL c hQ hseries
  have hint : Integrable (fun t : ℝ => LSeries c ((3/2 : ℂ)+(t : ℂ)*I)*
      (Q : ℂ)^((3/2 : ℂ)+(t : ℂ)*I)*lemma54PaperDeltaMellin D ((3/2 : ℂ)+(t : ℂ)*I)) :=
    hi.congr (ae_of_all _ hpoint)
  have hh := hasSum_integral_of_summable_integral_norm
    (fun n => proposition71_delta_dirichlet_series_term_integrable hD hL c hQ n)
    (proposition71_delta_dirichlet_series_integral_norm_summable D c hQ hseries)
  have hs := hh.mul_left (((1/(2*Real.pi) : ℝ) : ℂ))
  simp_rw [proposition71_delta_dirichlet_series_term_integral hD hL c hQ,hpoint] at hs
  exact ⟨hint,hs.summable,hs.tsum_eq.symm⟩

end ZhangLS.Spec
