import ZhangLS.Spec.Proposition71ResidueNormalization
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Filter
open scoped Topology

-- The source integrand has all three original zeta shifts and the actual delta.
example (D : ℕ) (c : ℝ) (s : ℂ) :
    proposition71ResidueIntegrand D (lemma83PaperBeta D c) s =
      riemannZeta (s+lemma52PaperBetaOne D c)*
      riemannZeta (s+lemma52PaperBetaTwo D c)*
      riemannZeta (s+lemma52PaperBetaThree D c)/riemannZeta s*
      lemma54PaperDeltaMellin D s := rfl

-- The residue is a genuine punctured-neighborhood limit, not a prescribed formula.
example (D : ℕ) (c : ℝ) (j : Fin 3) : proposition71ActualR D c j =
    limUnder (𝓝[≠] (1-lemma83PaperBeta D c j))
      (fun s => (s-(1-lemma83PaperBeta D c j))*
        proposition71ResidueIntegrand D (lemma83PaperBeta D c) s) := rfl

-- All three source leading constants, in the original order.
example : proposition71ResidueWeight 0=1/2 ∧ proposition71ResidueWeight 1=2 ∧
    proposition71ResidueWeight 2=3/2 := by
  norm_num [proposition71ResidueWeight,show (2:Fin 3)≠0 by decide,show (2:Fin 3)≠1 by decide]

-- The original perturbations remain coupled rather than independent.
example (D : ℕ) (c : ℝ) :
    lemma83PaperBeta D c 0+lemma83PaperBeta D c 1=lemma83PaperBeta D c 2 := by
  change lemma52PaperBetaOne D c+lemma52PaperBetaTwo D c=lemma52PaperBetaThree D c
  linear_combination -(lemma153_beta_gap_one D c)

-- Original beta nonzero/injectivity are actual proved facts.
example {D : ℕ} {c : ℝ} (hL : 3≤lemma23PaperL D) (hc : 0<c)
    (hs : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10) :
    (∀ j, lemma83PaperBeta D c j≠0) ∧ Function.Injective (lemma83PaperBeta D c) :=
  section15_actual_shift_data hL hc hs

-- No supplied zeta nonvanishing assumption is present.
example {D : ℕ} {c : ℝ} (hL : 3≤lemma23PaperL D) (hc : 0<c)
    (hs : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10) (j : Fin 3) :
    riemannZeta (1-lemma83PaperBeta D c j)≠0 :=
  (proposition71_actual_zeta_denominator_nonzero hL hc hs j).2

-- Original full 10 alpha disk, and the true alpha log L delta estimate.
example : ∃ D₀ : ℕ, ∀ D : ℕ, D₀≤D → ∀ c : ℝ, 0<c →
    3≤lemma23PaperL D → c*lemma44PaperAlpha D*lemma23PaperL D≤1/10 →
    ∀ j : Fin 3, ‖lemma54PaperDeltaMellin D (1-lemma83PaperBeta D c j)-1‖≤
      lemma54Constant*lemma44PaperAlpha D*Real.log (lemma23PaperL D) :=
  proposition71_actual_delta_log_error_threshold

-- Actual local analyticity and actual limit have no residue/result hypothesis.
example {D : ℕ} (hD : 1<D) (hL : 2000≤lemma23PaperL D) {c : ℝ} (hc : 0<c)
    (hs : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10) (j : Fin 3) :
    Tendsto (fun s => (s-(1-lemma83PaperBeta D c j))*
      proposition71ResidueIntegrand D (lemma83PaperBeta D c) s)
      (𝓝[≠] (1-lemma83PaperBeta D c j)) (𝓝 (proposition71ActualR D c j)) :=
  (proposition71_actual_residue_local_data hD hL hc hs j).2.2

-- Exact delta*zeta*zeta/zeta formula, still using actual shifts throughout.
example {D : ℕ} (hD : 1<D) (hL : 2000≤lemma23PaperL D) {c : ℝ} (hc : 0<c)
    (hs : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10) (j : Fin 3) :
    proposition71ActualR D c j =
      lemma54PaperDeltaMellin D (1-lemma83PaperBeta D c j)*
      riemannZeta (1+lemma83PaperBeta D c (j+1)-lemma83PaperBeta D c j)*
      riemannZeta (1+lemma83PaperBeta D c (j+2)-lemma83PaperBeta D c j)/
      riemannZeta (1-lemma83PaperBeta D c j) :=
  proposition71_actual_residue_formula hD hL hc hs j

-- Main semantic target: c is fixed before choosing the common constant and threshold.
-- There is no assumption (A), character, residue oracle, or target-valued premise.
example {c : ℝ} (hc : 0<c) :
    ∃ C : ℝ, 0<C ∧ ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      ∀ p∈lemma56PaperPrimes D, ∀ j : Fin 3,
        ‖I*proposition71ActualR D c j*(p:ℂ)^(-lemma83PaperBeta D c j)-
          proposition71ResidueWeight j/(lemma44PaperAlpha D:ℂ)‖≤C*Real.log (D:ℝ) :=
  proposition71_actual_residue_normalization hc

-- Nonzero residues also certify that the actual local singularities are not removable.
example {c : ℝ} (hc : 0<c) :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D → ∀ j : Fin 3,
      proposition71ActualR D c j≠0 := proposition71_actual_residue_nonzero hc

end ZhangLS.Spec
