import ZhangLS.Spec.Proposition71PrincipalShortRectangle
import ZhangLS.Spec.Proposition71PrincipalRightMellin
import ZhangLS.Spec.Lemma102UnshiftedInfiniteContourAlgebra
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Classical Topology
set_option maxHeartbeats 3000000

noncomputable def proposition71PrincipalDeltaSum (D : ℕ) (c : ℝ) (d m : ℕ) (q : ℝ) : ℂ :=
  ∑' n : Proposition71CoprimeIndex m,
    lemma83Kappa (lemma83PaperBeta D c) (d*n.val)*lemma53PaperDelta D ((n.val : ℝ)/q)

noncomputable def proposition71PrincipalResidueSum (D : ℕ) (c : ℝ) (d m : ℕ) (q : ℝ) : ℂ :=
  ∑j : Fin 3, proposition71ActualR D c j*
    lemma83ModifiedKappa (lemma83PaperBeta D c) d m (1-lemma83PaperBeta D c j)*
    lemma83Lambda (lemma83PaperBeta D c) (d*m) (1-lemma83PaperBeta D c j)*
    (q : ℂ)^(1-lemma83PaperBeta D c j)

/-- The infinite actual source sum is reduced to exactly the new left edge,
both horizontal edges, and both genuine infinite right-line tails. -/
theorem proposition71_principal_five_edge_error {c : ℝ} (hc : 0<c) :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D → 2000≤lemma23PaperL D →
      ∀ d m : ℕ, d≠0 → m≠0 → ∀ q : ℝ, 0<q →
      let F := proposition71PrincipalMellinIntegrand D (lemma83PaperBeta D c) d m q
      let a := 1-1/lemma23PaperL D
      let b := 1+lemma44PaperAlpha D
      let H := proposition71ZetaAuxHeight D/2
      ‖proposition71PrincipalDeltaSum D c d m q-proposition71PrincipalResidueSum D c d m q‖≤
        ‖∫t : ℝ in -H..H, F ((a : ℂ)+(t : ℂ)*I)‖+
        ‖∫σ : ℝ in a..b, F ((σ : ℂ)+((-H : ℝ) : ℂ)*I)‖+
        ‖∫σ : ℝ in a..b, F ((σ : ℂ)+(H : ℂ)*I)‖+
        ‖∫t : ℝ in Iic (-H), F ((b : ℂ)+(t : ℂ)*I)‖+
        ‖∫t : ℝ in Ioi H, F ((b : ℂ)+(t : ℂ)*I)‖ := by
  obtain ⟨D₀,hD₀,hrect⟩ := proposition71_actual_principal_short_rectangle hc
  refine ⟨D₀,hD₀,?_⟩
  intro D hDN hL d m hd hm q hq
  dsimp only
  let F := proposition71PrincipalMellinIntegrand D (lemma83PaperBeta D c) d m q
  let a := 1-1/lemma23PaperL D
  let b := 1+lemma44PaperAlpha D
  let H := proposition71ZetaAuxHeight D/2
  have hD : 1<D := by omega
  have hα := (proposition71_zeta_paper_alpha_budget (by linarith : 3≤lemma23PaperL D)).1
  have hb : 1<b := by dsimp [b]; linarith
  have hH : 0≤H := (div_pos (proposition71_zeta_aux_height_pos D) (by norm_num)).le
  have hM := proposition71_actual_general_principal_mellin_source hD hL (lemma83PaperBeta D c)
    (lemma83_beta_re D c) hb hd hm hq
  have hper : proposition71PrincipalDeltaSum D c d m q=(2*Real.pi : ℂ)⁻¹*
      ((∫t : ℝ in Iic (-H),F ((b : ℂ)+(t : ℂ)*I))+
        (∫t : ℝ in -H..H,F ((b : ℂ)+(t : ℂ)*I))+
          (∫t : ℝ in Ioi H,F ((b : ℂ)+(t : ℂ)*I))) := by
    have he := hM.2.2
    rw [lemma102_unshifted_integral_split_three _ hM.2.1 hH] at he
    simpa only [proposition71PrincipalDeltaSum,Complex.ofReal_div,Complex.ofReal_one,
      Complex.ofReal_mul,Complex.ofReal_ofNat,Complex.ofReal_inv,one_div,F] using he
  have hfin : proposition71PrincipalResidueSum D c d m q=
      (2*Real.pi : ℂ)⁻¹*((∫t : ℝ in -H..H,F ((b : ℂ)+(t : ℂ)*I))-
        (∫t : ℝ in -H..H,F ((a : ℂ)+(t : ℂ)*I)))+
      (2*Real.pi*I : ℂ)⁻¹*((∫σ : ℝ in a..b,F ((σ : ℂ)+((-H : ℝ) : ℂ)*I))-
        (∫σ : ℝ in a..b,F ((σ : ℂ)+(H : ℂ)*I))) := by
    have he : lemma81RectangleIntegral F a b (-H) H=
      2*(Real.pi : ℂ)*I*proposition71PrincipalResidueSum D c d m q := by
      simpa only [F,a,b,H,neg_div,proposition71PrincipalResidueSum] using hrect D hDN d m hd q hq
    calc
      _=(2*Real.pi*I : ℂ)⁻¹*(2*(Real.pi : ℂ)*I*proposition71PrincipalResidueSum D c d m q) := by
        field_simp
      _=(2*Real.pi*I : ℂ)⁻¹*lemma81RectangleIntegral F a b (-H) H := by rw [he]
      _=_ := by
        unfold lemma81RectangleIntegral
        field_simp
        ring
  exact lemma102_unshifted_normalized_boundary_error _ _ _ _ _ _ _ _ hper hfin

end ZhangLS.Spec
