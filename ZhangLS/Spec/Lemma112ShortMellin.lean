import ZhangLS.Spec.Lemma112SumExchange
import ZhangLS.Spec.Lemma112WideZBounds
/-! # Exact short Mellin inversion at the original P₁ cutoff -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Real Topology

noncomputable def lemma112ShortRightMellinIntegrand {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ) (B σ t : ℝ) : ℂ :=
  let w := (σ : ℂ) + (t : ℂ) * I
  lemma112ShortPolynomial χ ψ (s + w) * exp (w * (Real.log B : ℂ)) *
    lemma57OmegaOne D w / w

lemma lemma112_short_mellin_eq_finite_sum {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ) (B σ t : ℝ) :
    lemma112ShortRightMellinIntegrand χ ψ s B σ t * I =
      ∑ n ∈ (Finset.Icc 1 ⌈lemma112PaperP1 D⌉₊).filter
        (fun (n : ℕ) => (n : ℝ) < lemma112PaperP1 D),
        lemma44MellinSeriesTerm D (lemma112Coefficient χ ψ) s B σ n t := by
  unfold lemma112ShortRightMellinIntegrand lemma112ShortPolynomial
  simp only [Finset.sum_mul,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := by
    have h := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
    omega
  rw [lemma44MellinSeriesTerm,lemma44_LSeries_term_eq_exp _ _ hn0]

lemma lemma112_short_mellin_integrable {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ) (B : ℝ) (hD : 1 < D)
    {σ : ℝ} (hσ : σ ≠ 0) :
    Integrable (lemma112ShortRightMellinIntegrand χ ψ s B σ) := by
  have ht : Integrable (fun t : ℝ => lemma112ShortRightMellinIntegrand χ ψ s B σ t * I) := by
    simp_rw [lemma112_short_mellin_eq_finite_sum]
    apply integrable_finsetSum
    intro n hn
    exact lemma44MellinSeriesTerm_integrable hD _ s B hσ n
  simpa only [mul_assoc,I_mul_I,mul_neg,mul_one,neg_neg] using ht.mul_const (-I)

lemma lemma112_actual_short_gaussian_mellin {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ) (hD : 1 < D)
    {B σ : ℝ} (hB : 0 < B) (hσ : 0 < σ) :
    (2 * (Real.pi : ℂ) * I)⁻¹ *
      (∫ t : ℝ, lemma112ShortRightMellinIntegrand χ ψ s B σ t * I) =
      ∑ n ∈ (Finset.Icc 1 ⌈lemma112PaperP1 D⌉₊).filter
        (fun (n : ℕ) => (n : ℝ) < lemma112PaperP1 D),
        LSeries.term (lemma112Coefficient χ ψ) s n *
          (zhangGaussianWeight D (B / n) : ℂ) := by
  simp_rw [lemma112_short_mellin_eq_finite_sum]
  rw [integral_finsetSum _ (fun n _ =>
    lemma44MellinSeriesTerm_integrable hD _ s B hσ.ne' n),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  exact lemma44MellinSeriesTerm_normalized_integral hD _ s hB hσ n

end ZhangLS.Spec
