import ZhangLS.Spec.Lemma61OriginalLeftError
import ZhangLS.Spec.Lemma61GaussianCutoff
import ZhangLS.Spec.Lemma61ReciprocalTailTruncation

/-! # Faithful original Lemma 6.1

Finite short-polynomial Gaussian inversion, actual original-left integral
decomposition and N approximation, actual full horizontal L edges and
uniform constants/thresholds yield lemma61_proved : Lemma61Target.
Original Psi, strict region and actual L/K/N/E1 are retained.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Real Topology
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

noncomputable def lemma61ShortRightMellinIntegrand {p : ℕ} (D : ℕ)
    (ψ : DirichletCharacter ℂ p) (s : ℂ) (B σ t : ℝ) : ℂ :=
  let w := (σ : ℂ) + (t : ℂ) * I
  lemma61ShortPolynomial D ψ (s + w) * exp (w * (Real.log B : ℂ)) *
    lemma57OmegaOne D w / w

lemma lemma61_short_mellin_eq_finite_sum {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (s : ℂ) (B σ t : ℝ) :
    lemma61ShortRightMellinIntegrand D ψ s B σ t * I =
      ∑ n ∈ (Finset.Icc 1 ⌈lemma56PaperT D ^ 3⌉₊).filter
        (fun (n : ℕ) => (n : ℝ) < lemma56PaperT D ^ 3),
        lemma44MellinSeriesTerm D (fun n => ψ (n : ZMod p)) s B σ n t := by
  unfold lemma61ShortRightMellinIntegrand lemma61ShortPolynomial
  simp only [Finset.sum_mul,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := by
    have h := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
    omega
  rw [lemma44MellinSeriesTerm,lemma44_LSeries_term_eq_exp _ _ hn0]

lemma lemma61_short_mellin_integrable {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (s : ℂ) (B : ℝ) (hD : 1 < D)
    {σ : ℝ} (hσ : σ ≠ 0) :
    Integrable (lemma61ShortRightMellinIntegrand D ψ s B σ) := by
  have ht : Integrable (fun t : ℝ => lemma61ShortRightMellinIntegrand D ψ s B σ t * I) := by
    simp_rw [lemma61_short_mellin_eq_finite_sum]
    apply integrable_finsetSum
    intro n hn
    exact lemma44MellinSeriesTerm_integrable hD _ s B hσ n
  simpa only [mul_assoc,I_mul_I,mul_neg,mul_one,neg_neg] using ht.mul_const (-I)

lemma lemma61_actual_short_gaussian_mellin {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (s : ℂ) (hD : 1 < D)
    {B σ : ℝ} (hB : 0 < B) (hσ : 0 < σ) :
    (2 * (Real.pi : ℂ) * I)⁻¹ *
      (∫ t : ℝ, lemma61ShortRightMellinIntegrand D ψ s B σ t * I) =
      ∑ n ∈ (Finset.Icc 1 ⌈lemma56PaperT D ^ 3⌉₊).filter
        (fun (n : ℕ) => (n : ℝ) < lemma56PaperT D ^ 3),
        LSeries.term (fun n => ψ (n : ZMod p)) s n *
          (zhangGaussianWeight D (B / n) : ℂ) := by
  simp_rw [lemma61_short_mellin_eq_finite_sum]
  rw [integral_finsetSum _ (fun n _ =>
    lemma44MellinSeriesTerm_integrable hD _ s B hσ.ne' n),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  exact lemma44MellinSeriesTerm_normalized_integral hD _ s hB hσ n

end ZhangLS.Spec
