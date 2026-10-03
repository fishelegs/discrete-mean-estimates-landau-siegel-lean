import ZhangLS.Spec.Proposition71ShiftedKappaSeries
import ZhangLS.Spec.Proposition71DeltaDirichletMellin
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Classical Topology
set_option maxHeartbeats 2000000

/-- The exact finite-prime corrected integrand in source (7.19), before any
continuation or contour displacement. -/
noncomputable def proposition71PrincipalMellinIntegrand (D : ℕ) (β : Fin 3 → ℂ)
    (d m : ℕ) (q : ℝ) (s : ℂ) : ℂ :=
  lemma83ModifiedKappa β d m s * lemma83Lambda β (d*m) s *
    (riemannZeta (s+β 0)*riemannZeta (s+β 1)*riemannZeta (s+β 2)/riemannZeta s) *
      (q : ℂ)^s * lemma54PaperDeltaMellin D s

lemma proposition71_coprime_index_weight_tsum (m : ℕ) (f : ℕ → ℂ) :
    (∑' n : Proposition71CoprimeIndex m, f n.val)=
      ∑' n : ℕ, if n=0 then 0 else if n.Coprime m then f n else 0 := by
  change (∑' n : {n : ℕ | n ≠ 0 ∧ n.Coprime m}, f n.val)=_
  rw [_root_.tsum_subtype]
  apply tsum_congr
  intro n
  by_cases hn : n=0
  · subst n; simp
  · by_cases hc : n.Coprime m
    · rw [Set.indicator_of_mem (show n ∈ {n : ℕ | n ≠ 0 ∧ n.Coprime m} from ⟨hn,hc⟩),
        if_neg hn,if_pos hc]
    · rw [Set.indicator_of_notMem (show n ∉ {n : ℕ | n ≠ 0 ∧ n.Coprime m} from fun h => hc h.2),
        if_neg hn,if_neg hc]

/-- Genuine source (7.19), including absolute summability and vertical
integrability, derived from the actual coefficients and actual Δ inversion. -/
theorem proposition71_actual_principal_mellin_source {D : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) (β : Fin 3 → ℂ) (hβ : ∀ j, (β j).re=0)
    {d m : ℕ} (hd : d≠0) (hm : m≠0) {q : ℝ} (hq : 0<q) :
    Summable (fun n : Proposition71CoprimeIndex m =>
      lemma83Kappa β (d*n.val)*lemma53PaperDelta D ((n.val : ℝ)/q)) ∧
    Integrable (fun t : ℝ => proposition71PrincipalMellinIntegrand D β d m q
      ((3/2 : ℂ)+(t : ℂ)*I)) ∧
    (∑' n : Proposition71CoprimeIndex m,
      lemma83Kappa β (d*n.val)*lemma53PaperDelta D ((n.val : ℝ)/q))=
        ((1/(2*Real.pi) : ℝ) : ℂ)*∫t : ℝ,
          proposition71PrincipalMellinIntegrand D β d m q ((3/2 : ℂ)+(t : ℂ)*I) := by
  let a := fun n => if n.Coprime m then lemma83Kappa β (d*n) else 0
  have hs := proposition71_shifted_coprime_kappa_summable β hβ hd hm (s := (3/2 : ℂ)) (by norm_num)
  obtain ⟨hI,hS,he⟩ := proposition71_actual_delta_dirichlet_series hD hL a hq hs
  have hpoint (t : ℝ) : LSeries a ((3/2 : ℂ)+(t : ℂ)*I)*(q : ℂ)^((3/2 : ℂ)+(t : ℂ)*I)*
      lemma54PaperDeltaMellin D ((3/2 : ℂ)+(t : ℂ)*I)=
        proposition71PrincipalMellinIntegrand D β d m q ((3/2 : ℂ)+(t : ℂ)*I) := by
    unfold proposition71PrincipalMellinIntegrand
    rw [show LSeries a ((3/2 : ℂ)+(t : ℂ)*I)=_ from
      proposition71_shifted_coprime_kappa_LSeries β hβ hd hm (by norm_num)]
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

/-- Source (7.19) with the original paper β values and literal p*k/l₂ scale.
No support condition is needed for this identity; positivity is sufficient. -/
theorem proposition71_original_principal_mellin_source {D : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) (c : ℝ) {d₁ d₂ k p l₂ : ℕ}
    (hd₁ : 0<d₁) (hd₂ : 0<d₂) (hk : 0<k) (hp : 0<p) (hl₂ : 0<l₂) :
    Summable (fun n : Proposition71CoprimeIndex (d₂*k) =>
      lemma83Kappa (lemma83PaperBeta D c) (d₁*n.val)*
        lemma53PaperDelta D ((n.val : ℝ)*(l₂ : ℝ)/((p : ℝ)*(k : ℝ)))) ∧
    Integrable (fun t : ℝ => proposition71PrincipalMellinIntegrand D (lemma83PaperBeta D c)
      d₁ (d₂*k) ((p : ℝ)*(k : ℝ)/(l₂ : ℝ)) ((3/2 : ℂ)+(t : ℂ)*I)) ∧
    (∑' n : Proposition71CoprimeIndex (d₂*k),
      lemma83Kappa (lemma83PaperBeta D c) (d₁*n.val)*
        lemma53PaperDelta D ((n.val : ℝ)*(l₂ : ℝ)/((p : ℝ)*(k : ℝ))))=
      ((1/(2*Real.pi) : ℝ) : ℂ)*∫t : ℝ,
        proposition71PrincipalMellinIntegrand D (lemma83PaperBeta D c) d₁ (d₂*k)
          ((p : ℝ)*(k : ℝ)/(l₂ : ℝ)) ((3/2 : ℂ)+(t : ℂ)*I) := by
  have hq : 0<(p : ℝ)*(k : ℝ)/(l₂ : ℝ) := by positivity
  have hh := proposition71_actual_principal_mellin_source hD hL (lemma83PaperBeta D c)
    (lemma83_beta_re D c) hd₁.ne' (Nat.mul_pos hd₂ hk).ne' hq
  have ha (n : ℕ) : (n : ℝ)/((p : ℝ)*(k : ℝ)/(l₂ : ℝ))=
      (n : ℝ)*(l₂ : ℝ)/((p : ℝ)*(k : ℝ)) := by
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
    ring
  simpa only [ha] using hh

end ZhangLS.Spec
