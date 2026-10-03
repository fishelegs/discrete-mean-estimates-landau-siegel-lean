import ZhangLS.Spec.Proposition71PrincipalPointwise
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Filter Set Finset
open scoped Classical Topology

/-- The true regularized numerator is zero at 1, with no use of ζ(1). -/
example (D : ℕ) (β : Fin 3 → ℂ) (d m : ℕ) (q : ℝ) :
    proposition71PrincipalContourNumerator D β d m q 1=0 :=
  proposition71_principal_numerator_at_one D β d m q

/-- Every original pole appears once, because the original shifts are distinct. -/
example {D : ℕ} (hL : 3≤lemma23PaperL D) {c : ℝ} (hc : 0<c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10) :
    (proposition71PrincipalPoleSet (lemma83PaperBeta D c)).card=3 := by
  have hi : Function.Injective (fun j : Fin 3 => 1-lemma83PaperBeta D c j) := by
    intro j k he
    apply (section15_actual_shift_data hL hc hsmall).2
    linear_combination -he
  rw [proposition71PrincipalPoleSet,Finset.card_image_of_injective _ hi]
  simp

/-- The genuine Mellin identity is available on the actual 1+α line, and
not inferred by applying a theorem restricted to another real part. -/
example {D : ℕ} (hD : 1<D) (hL : 2000≤lemma23PaperL D) (c : ℝ)
    {d m : ℕ} (hd : d≠0) (hm : m≠0) {q : ℝ} (hq : 0<q) :
    Integrable (fun t : ℝ => proposition71PrincipalMellinIntegrand D (lemma83PaperBeta D c) d m q
      (((1+lemma44PaperAlpha D : ℝ) : ℂ)+(t : ℂ)*I)) ∧
    (∑' n : Proposition71CoprimeIndex m,
      lemma83Kappa (lemma83PaperBeta D c) (d*n.val)*lemma53PaperDelta D ((n.val : ℝ)/q))=
      ((1/(2*Real.pi) : ℝ) : ℂ)*(∫t : ℝ,
        proposition71PrincipalMellinIntegrand D (lemma83PaperBeta D c) d m q
          (((1+lemma44PaperAlpha D : ℝ) : ℂ)+(t : ℂ)*I)) := by
  have ha := (proposition71_zeta_paper_alpha_budget (by linarith : 3≤lemma23PaperL D)).1
  exact (proposition71_actual_general_principal_mellin_source hD hL (lemma83PaperBeta D c)
    (lemma83_beta_re D c) (by linarith : 1<1+lemma44PaperAlpha D) hd hm hq).2

/-- The complete four-edge operator, with the three original residues and
an H/2 height; no edge or principal pole has been omitted. -/
example {c : ℝ} (hc : 0<c) :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D → ∀ d m : ℕ, d≠0 → ∀ q : ℝ, 0<q →
      let F := proposition71PrincipalMellinIntegrand D (lemma83PaperBeta D c) d m q
      let a := 1-1/lemma23PaperL D
      let b := 1+lemma44PaperAlpha D
      let H := proposition71ZetaAuxHeight D/2
      (∫σ : ℝ in a..b,F ((σ : ℂ)+((-H : ℝ) : ℂ)*I))-
      (∫σ : ℝ in a..b,F ((σ : ℂ)+(H : ℂ)*I))+
      I*(∫t : ℝ in -H..H,F ((b : ℂ)+(t : ℂ)*I))-
      I*(∫t : ℝ in -H..H,F ((a : ℂ)+(t : ℂ)*I))=
      2*(Real.pi : ℂ)*I*(∑j : Fin 3,
        proposition71ActualR D c j*
          lemma83ModifiedKappa (lemma83PaperBeta D c) d m (1-lemma83PaperBeta D c j)*
          lemma83Lambda (lemma83PaperBeta D c) (d*m) (1-lemma83PaperBeta D c j)*
          (q : ℂ)^(1-lemma83PaperBeta D c j)) := by
  simpa only [lemma81RectangleIntegral,neg_div] using proposition71_actual_principal_short_rectangle hc

example : 0<proposition71PrincipalContourConstant := proposition71_principal_contour_constant_pos

/-- The endpoint uses original prime/support hypotheses and keeps the exact
finite Euler factors expanded, including the τ₅(d₁) loss. -/
example {c : ℝ} (hc : 0<c) :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D → ∀ p d₁ d₂ k l₂ : ℕ,
      p∈lemma56PaperPrimes D → 0<d₁ → 0<d₂ → 0<k → 0<l₂ →
      d₂*l₂∈lemma81PolynomialIndices D → d₁*d₂*k∈lemma81PolynomialIndices D →
      ‖(∑' n : Proposition71CoprimeIndex (d₂*k),
        lemma83Kappa (lemma83PaperBeta D c) (d₁*n.val)*
          lemma53PaperDelta D ((n.val : ℝ)*(l₂ : ℝ)/((p : ℝ)*(k : ℝ))))-
        (∑j : Fin 3, proposition71ActualR D c j*
          lemma83ModifiedKappa (lemma83PaperBeta D c) d₁ (d₂*k) (1-lemma83PaperBeta D c j)*
          lemma83Lambda (lemma83PaperBeta D c) (d₁*d₂*k) (1-lemma83PaperBeta D c j)*
          (((p : ℝ)*(k : ℝ)/(l₂ : ℝ) : ℝ) : ℂ)^(1-lemma83PaperBeta D c j))‖≤
        proposition71PrincipalContourConstant*(lemma34Tau 5 d₁ : ℝ)*
          (∏r∈d₁.primeFactors,1/(1-(r : ℝ)^(-(1-1/lemma23PaperL D)))^5)*
          (∏r∈(d₁*d₂*k).primeFactors,
            (1+(r : ℝ)^(-(1-1/lemma23PaperL D)))^3/(1-(r : ℝ)^(-(1-1/lemma23PaperL D))))*
          ((p : ℝ)*(k : ℝ)/(l₂ : ℝ))*lemma23PaperL D^3244*
          Real.exp (-(lemma23PaperL D)^(1/10 : ℝ)) := by
  exact proposition71_original_principal_contour hc

end ZhangLS.Spec
