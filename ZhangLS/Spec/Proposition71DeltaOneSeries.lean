import ZhangLS.Spec.Proposition71GammaOmegaTail
import ZhangLS.Spec.Proposition71MellinDoubleSum
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Actual Δ₁ inversion for an absolutely convergent arbitrary coefficient series

The coefficients are independent of the functional-equation character. This
is the common Section7/14 analytic bridge, with all integral/series exchanges
proved by summable integrals of actual norms.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Filter
open scoped Topology
set_option maxHeartbeats 2500000

noncomputable def proposition71DeltaOneSeriesTerm (D : ℕ) (c : ℕ → ℂ) (Q : ℝ)
    (n : ℕ) (t : ℝ) : ℂ :=
  LSeries.term c ((3/2 : ℂ)+(t : ℂ)*I) n *
    (Q : ℂ)^((3/2 : ℂ)+(t : ℂ)*I)*proposition71GammaOmegaKernel D t

lemma proposition71_delta_one_series_term_norm (D : ℕ) (c : ℕ → ℂ)
    {Q : ℝ} (hQ : 0<Q) (n : ℕ) (t : ℝ) :
    ‖proposition71DeltaOneSeriesTerm D c Q n t‖=
      Q^(3/2 : ℝ)*‖LSeries.term c (3/2 : ℂ) n‖*‖proposition71GammaOmegaKernel D t‖ := by
  have ht : ‖LSeries.term c ((3/2 : ℂ)+(t : ℂ)*I) n‖=‖LSeries.term c (3/2 : ℂ) n‖ := by
    simp only [LSeries.norm_term_eq]
    norm_num
  unfold proposition71DeltaOneSeriesTerm
  rw [norm_mul,norm_mul,ht,Complex.norm_cpow_eq_rpow_re_of_pos hQ]
  have hsr : ((3/2 : ℂ)+(t : ℂ)*I).re=(3/2 : ℝ) := by norm_num
  rw [hsr]
  ring

lemma proposition71_delta_one_series_term_kernel (D : ℕ) (c : ℕ → ℂ)
    {Q : ℝ} (hQ : 0<Q) {n : ℕ} (hn : n≠0) (t : ℝ) :
    proposition71DeltaOneSeriesTerm D c Q n t=c n*lemma53MellinIntegrand D ((n : ℝ)/Q) t := by
  have hnp : 0<(n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have he := proposition71_positive_ratio_cpow hnp hQ (-((3/2 : ℂ)+(t : ℂ)*I))
  simp only [Complex.ofReal_natCast,neg_neg] at he
  unfold proposition71DeltaOneSeriesTerm proposition71GammaOmegaKernel lemma53MellinIntegrand
  rw [LSeries.term_of_ne_zero hn,he,Complex.cpow_neg]
  ring

lemma proposition71_delta_one_series_term_integrable {D : ℕ} (hD : 1<D)
    (c : ℕ → ℂ) {Q : ℝ} (hQ : 0<Q) (n : ℕ) :
    Integrable (proposition71DeltaOneSeriesTerm D c Q n) := by
  by_cases hn : n=0
  · subst n
    have he : proposition71DeltaOneSeriesTerm D c Q 0=fun _ => 0 := by funext t; simp [proposition71DeltaOneSeriesTerm]
    rw [he]; exact integrable_zero _ _ _
  have hi := (lemma53_mellin_integrand_integrable hD
    (div_pos (by exact_mod_cast Nat.pos_of_ne_zero hn : 0<(n : ℝ)) hQ)).const_mul (c n)
  apply hi.congr
  exact ae_of_all _ (fun t => (proposition71_delta_one_series_term_kernel D c hQ hn t).symm)

lemma proposition71_delta_one_series_integral_norm_summable (D : ℕ) (c : ℕ → ℂ)
    {Q : ℝ} (hQ : 0<Q) (hseries : LSeriesSummable c (3/2 : ℂ)) :
    Summable (fun n : ℕ => ∫t : ℝ, ‖proposition71DeltaOneSeriesTerm D c Q n t‖) := by
  have hn : Summable (fun n : ℕ => ‖LSeries.term c (3/2 : ℂ) n‖) := summable_norm_iff.mpr hseries
  let K := Q^(3/2 : ℝ)*(∫t : ℝ, ‖proposition71GammaOmegaKernel D t‖)
  apply (hn.mul_left K).congr
  intro n
  simp_rw [proposition71_delta_one_series_term_norm D c hQ,integral_const_mul]
  dsimp [K]
  ring

lemma proposition71_delta_one_series_tsum_integrable {D : ℕ} (hD : 1<D)
    (c : ℕ → ℂ) {Q : ℝ} (hQ : 0<Q) (hseries : LSeriesSummable c (3/2 : ℂ)) :
    Integrable (fun t : ℝ => ∑' n, proposition71DeltaOneSeriesTerm D c Q n t) := by
  have hn : Summable (fun n : ℕ => ‖LSeries.term c (3/2 : ℂ) n‖) := summable_norm_iff.mpr hseries
  let K := Q^(3/2 : ℝ)*(∑' n : ℕ, ‖LSeries.term c (3/2 : ℂ) n‖)
  apply ((proposition71_gamma_omega_integrable hD).norm.const_mul K).mono'
  · exact AEStronglyMeasurable.tsum (fun n => (proposition71_delta_one_series_term_integrable hD c hQ n).1)
  · apply ae_of_all
    intro t
    have ht : Summable (fun n => ‖proposition71DeltaOneSeriesTerm D c Q n t‖) := by
      apply (hn.mul_left (Q^(3/2 : ℝ)*‖proposition71GammaOmegaKernel D t‖)).congr
      intro n
      rw [proposition71_delta_one_series_term_norm D c hQ]
      ring
    calc
      _≤∑' n, ‖proposition71DeltaOneSeriesTerm D c Q n t‖ := norm_tsum_le_tsum_norm ht
      _=∑' n, (Q^(3/2 : ℝ)*‖proposition71GammaOmegaKernel D t‖)*‖LSeries.term c (3/2 : ℂ) n‖ := by
        apply tsum_congr; intro n
        rw [proposition71_delta_one_series_term_norm D c hQ]
        ring
      _=K*‖proposition71GammaOmegaKernel D t‖ := by rw [tsum_mul_left]; dsimp [K]; ring

lemma proposition71_delta_one_integral (D : ℕ) (x : ℝ) :
    lemma53PaperDeltaOne D x=((1/(2*Real.pi) : ℝ) : ℂ)*(∫t : ℝ, lemma53MellinIntegrand D x t) := by
  unfold lemma53PaperDeltaOne mellinInv lemma53MellinIntegrand
  simp only [Complex.real_smul,smul_eq_mul,Complex.ofReal_div,Complex.ofReal_ofNat,mul_assoc]

lemma proposition71_delta_one_series_term_integral (D : ℕ) (c : ℕ → ℂ)
    {Q : ℝ} (hQ : 0<Q) (n : ℕ) :
    ((1/(2*Real.pi) : ℝ) : ℂ)*(∫t : ℝ, proposition71DeltaOneSeriesTerm D c Q n t)=
      if n=0 then 0 else c n*lemma53PaperDeltaOne D ((n : ℝ)/Q) := by
  by_cases hn : n=0
  · subst n; simp [proposition71DeltaOneSeriesTerm]
  rw [if_neg hn]
  simp_rw [proposition71_delta_one_series_term_kernel D c hQ hn,integral_const_mul]
  rw [proposition71_delta_one_integral]
  ring

/-- Actual inverse Mellin/Dirichlet-series interchange. All summability and
integrability conclusions are proved, with no mean-value or contour oracle. -/
theorem proposition71_actual_delta_one_series {D : ℕ} (hD : 1<D)
    (c : ℕ → ℂ) {Q : ℝ} (hQ : 0<Q) (hseries : LSeriesSummable c (3/2 : ℂ)) :
    Integrable (fun t : ℝ => LSeries c ((3/2 : ℂ)+(t : ℂ)*I)*
      (Q : ℂ)^((3/2 : ℂ)+(t : ℂ)*I)*proposition71GammaOmegaKernel D t) ∧
      Summable (fun n : ℕ => if n=0 then 0 else c n*lemma53PaperDeltaOne D ((n : ℝ)/Q)) ∧
        ((1/(2*Real.pi) : ℝ) : ℂ)*(∫t : ℝ, LSeries c ((3/2 : ℂ)+(t : ℂ)*I)*
          (Q : ℂ)^((3/2 : ℂ)+(t : ℂ)*I)*proposition71GammaOmegaKernel D t)=
            ∑' n : ℕ, if n=0 then 0 else c n*lemma53PaperDeltaOne D ((n : ℝ)/Q) := by
  have hpoint (t : ℝ) : (∑' n, proposition71DeltaOneSeriesTerm D c Q n t)=
      LSeries c ((3/2 : ℂ)+(t : ℂ)*I)*(Q : ℂ)^((3/2 : ℂ)+(t : ℂ)*I)*proposition71GammaOmegaKernel D t := by
    unfold proposition71DeltaOneSeriesTerm LSeries
    rw [tsum_mul_right,tsum_mul_right]
  have hi := proposition71_delta_one_series_tsum_integrable hD c hQ hseries
  have hint : Integrable (fun t : ℝ => LSeries c ((3/2 : ℂ)+(t : ℂ)*I)*
      (Q : ℂ)^((3/2 : ℂ)+(t : ℂ)*I)*proposition71GammaOmegaKernel D t) :=
    hi.congr (ae_of_all _ hpoint)
  have hh := hasSum_integral_of_summable_integral_norm
    (fun n => proposition71_delta_one_series_term_integrable hD c hQ n)
    (proposition71_delta_one_series_integral_norm_summable D c hQ hseries)
  have hs := hh.mul_left (((1/(2*Real.pi) : ℝ) : ℂ))
  simp_rw [proposition71_delta_one_series_term_integral D c hQ,hpoint] at hs
  exact ⟨hint,hs.summable,hs.tsum_eq.symm⟩

end ZhangLS.Spec
