import ZhangLS.Spec.Lemma151Definitions
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace ZhangLS.Spec
open Finset
open scoped Classical

/-- A fully explicit finite arithmetic error preserving n₁ and all weights. -/
noncomputable def lemma151ArithmeticReplacementError {D : ℕ} (χ : RealPrimitiveCharacter D)
    (S : Finset ℕ) (w : ℕ → ℂ) : ℝ :=
  ∑ n ∈ S, ‖w n‖ / (n : ℝ) * ∑ a ∈ n.divisorsAntidiagonal,
    if a.2 = 1 then 0 else (a.1.divisors.card : ℝ) * ‖lemma23NuArithmeticFunction χ a.2‖

/-- Quantitative weighted form of the exact B.1 arithmetic bridge. No bound on
ν is postulated and no restriction is dropped from S. -/
theorem lemma151_weighted_rhostar_replacement {D : ℕ} (χ : RealPrimitiveCharacter D)
    {β : ℂ} (hβ : β.re = 0) (S : Finset ℕ) (w : ℕ → ℂ) :
    ‖(∑ n ∈ S, w n * lemma151RhoStar χ β n / n) -
      (∑ n ∈ S, w n * lemma151Rho β n / n)‖ ≤
        lemma151ArithmeticReplacementError χ S w := by
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  unfold lemma151ArithmeticReplacementError
  apply Finset.sum_le_sum
  intro n hn
  have he : w n * lemma151RhoStar χ β n / n - w n * lemma151Rho β n / n =
      w n / n * (lemma151RhoStar χ β n - lemma151Rho β n) := by ring
  rw [he, norm_mul, norm_div, norm_natCast]
  exact mul_le_mul_of_nonneg_left (lemma151_rhostar_sub_rho_bound χ hβ n) (by positivity)

/-- The same genuine bound on the precise rough, strictly cut off summation set.
The literal b and corrected ψ-basis b are both possible arguments, not identified. -/
theorem lemma151_rough_weighted_replacement {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (n₁ N : ℕ) (X : ℝ) (b : ℕ → ℂ) :
    let S := (Finset.range N).filter (fun (n : ℕ) => 0<n ∧ (n : ℝ)<X ∧ n.Coprime (lemma151Q D))
    let w := fun n => b (n₁*n) * χ.evalNat n
    ‖(∑ n ∈ S, w n * lemma151RhoStar χ (lemma83PaperBeta D c j) n / n) -
      (∑ n ∈ S, w n * lemma151Rho (lemma83PaperBeta D c j) n / n)‖ ≤
        lemma151ArithmeticReplacementError χ S w := by
  exact lemma151_weighted_rhostar_replacement χ (lemma83_beta_re D c j) _ _

end ZhangLS.Spec
