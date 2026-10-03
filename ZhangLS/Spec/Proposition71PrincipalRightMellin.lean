import ZhangLS.Spec.Proposition71PrincipalMellinSource
import ZhangLS.Spec.Proposition71DeltaGeneralMellin
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Classical Topology
set_option maxHeartbeats 2000000

/-- Genuine source (7.19) on every genuine convergence line σ>1, including absolute summability and vertical
integrability, derived from the actual coefficients and actual Δ inversion. -/
theorem proposition71_actual_general_principal_mellin_source {D : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) (β : Fin 3 → ℂ) (hβ : ∀ j, (β j).re=0)
    {σ : ℝ} (hσ : 1<σ) {d m : ℕ} (hd : d≠0) (hm : m≠0) {q : ℝ} (hq : 0<q) :
    Summable (fun n : Proposition71CoprimeIndex m =>
      lemma83Kappa β (d*n.val)*lemma53PaperDelta D ((n.val : ℝ)/q)) ∧
    Integrable (fun t : ℝ => proposition71PrincipalMellinIntegrand D β d m q
      ((σ : ℂ)+(t : ℂ)*I)) ∧
    (∑' n : Proposition71CoprimeIndex m,
      lemma83Kappa β (d*n.val)*lemma53PaperDelta D ((n.val : ℝ)/q))=
        ((1/(2*Real.pi) : ℝ) : ℂ)*∫t : ℝ,
          proposition71PrincipalMellinIntegrand D β d m q ((σ : ℂ)+(t : ℂ)*I) := by
  let a := fun n => if n.Coprime m then lemma83Kappa β (d*n) else 0
  have hs := proposition71_shifted_coprime_kappa_summable β hβ hd hm (s := (σ : ℂ)) (by simpa using hσ)
  obtain ⟨hI,hS,he⟩ := proposition71_actual_general_delta_dirichlet_series hD hL (by linarith : 1/2≤σ) a hq hs
  have hpoint (t : ℝ) : LSeries a ((σ : ℂ)+(t : ℂ)*I)*(q : ℂ)^((σ : ℂ)+(t : ℂ)*I)*
      lemma54PaperDeltaMellin D ((σ : ℂ)+(t : ℂ)*I)=
        proposition71PrincipalMellinIntegrand D β d m q ((σ : ℂ)+(t : ℂ)*I) := by
    unfold proposition71PrincipalMellinIntegrand
    rw [show LSeries a ((σ : ℂ)+(t : ℂ)*I)=_ from
      proposition71_shifted_coprime_kappa_LSeries β hβ hd hm (by simpa using hσ)]
  have hss : Summable (fun n : Proposition71CoprimeIndex m =>
      lemma83Kappa β (d*n.val)*lemma53PaperDelta D ((n.val : ℝ)/q)) := by
    have hh := hS.subtype (fun n => n ≠ 0 ∧ n.Coprime m)
    apply hh.congr
    intro n
    simp only [Function.comp_apply,if_neg n.property.1,a,if_pos n.property.2]
  refine ⟨hss,hI.congr (ae_of_all _ hpoint),?_⟩
  rw [proposition71_coprime_index_weight_tsum m
    (fun n => lemma83Kappa β (d*n)*lemma53PaperDelta D ((n : ℝ)/q))]
  have hsum : (∑' n : ℕ, if n=0 then 0 else if n.Coprime m then
      lemma83Kappa β (d*n)*lemma53PaperDelta D ((n : ℝ)/q) else 0)=
      ∑' n : ℕ, if n=0 then 0 else a n*lemma53PaperDelta D ((n : ℝ)/q) := by
    apply tsum_congr
    intro n
    simp only [a,ite_mul,zero_mul]
  rw [hsum,←he]
  congr 1
  exact integral_congr_ae (ae_of_all _ hpoint)


end ZhangLS.Spec
