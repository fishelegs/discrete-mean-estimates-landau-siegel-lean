import ZhangLS.Spec.DivisorConductorBlockMomentsPrime

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec.DivisorConductorBlockMoments
open Complex Finset
open scoped Classical ComplexConjugate

noncomputable def mixedBlock (R : ℝ)
    (F G : (r : ℕ) → DirichletCharacter ℂ r → ℂ) : ℝ :=
  ∑ r ∈ blockModuli R, ((r : ℝ) / (r.totient : ℝ)) *
    ∑ θ ∈ univ.filter (fun θ : DirichletCharacter ℂ r => θ.IsPrimitive), ‖F r θ‖ * ‖G r θ‖

/-- Finite weighted Cauchy at the exact actual conductor set. -/
theorem finite_cauchy (R : ℝ) (F G : (r : ℕ) → DirichletCharacter ℂ r → ℂ) :
    mixedBlock R F G ^ 2 ≤ blockMoment R F * blockMoment R G := by
  exact proposition71_weighted_primitive_cauchy (blockModuli R)
    (fun r => (r : ℝ) / (r.totient : ℝ)) (fun r => by positivity) F G

theorem long_prime_cauchy {X R C_b P : ℝ} (hX : 1 ≤ X) (hR : 1 ≤ R)
    (hC : 0 ≤ C_b) {b : ℕ → ℂ} (hb : CoefficientBound C_b b) (hP : 1 ≤ P)
    (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime)
    (hupper : ∀ p ∈ S, (p : ℝ) ≤ 2 * P) (d h : ℕ) (hd : 0 < d) (t : ℝ) :
    mixedBlock R (fun r θ => longPolynomial d h X b r θ t)
        (fun r θ => primePolynomial S r θ t) ≤
      Real.sqrt (blockConstant * (1 + R ^ 2 / X) * longEnvelope C_b d X) *
        Real.sqrt (blockConstant * (R ^ 2 + P) * P ^ 3) := by
  have hK : 0 ≤ blockConstant := blockConstant_pos.le
  have hE := longEnvelope_nonneg C_b d hX
  apply proposition71_weighted_primitive_cauchy_bound (blockModuli R)
    (fun r => (r : ℝ) / (r.totient : ℝ)) (fun r => by positivity)
    (fun r θ => longPolynomial d h X b r θ t) (fun r θ => primePolynomial S r θ t)
  · positivity
  · positivity
  · exact long_block_strong hX hR hC hb d h hd t
  · exact prime_block_bound hR hP S hprime hupper t

/-- Both actual finite inputs combine, without a Mellin integral or D-saving claim. -/
theorem long_paper_prime_cauchy {D : ℕ} (hL : 2000 ≤ lemma23PaperL D)
    {X R C_b : ℝ} (hX : 1 ≤ X) (hR : 1 ≤ R) (hC : 0 ≤ C_b)
    {b : ℕ → ℂ} (hb : CoefficientBound C_b b) (d h : ℕ) (hd : 0 < d) (t : ℝ) :
    mixedBlock R (fun r θ => longPolynomial d h X b r θ t)
        (fun r θ => paperPrimePolynomial D r θ t) ≤
      Real.sqrt (blockConstant * (1 + R ^ 2 / X) * longEnvelope C_b d X) *
        Real.sqrt (blockConstant * (R ^ 2 + lemma23PaperP D) * (lemma23PaperP D) ^ 3) := by
  have hK : 0 ≤ blockConstant := blockConstant_pos.le
  have hE := longEnvelope_nonneg C_b d hX
  have hP : 0 < lemma23PaperP D := Real.exp_pos _
  apply proposition71_weighted_primitive_cauchy_bound (blockModuli R)
    (fun r => (r : ℝ) / (r.totient : ℝ)) (fun r => by positivity)
    (fun r θ => longPolynomial d h X b r θ t) (fun r θ => paperPrimePolynomial D r θ t)
  · positivity
  · positivity
  · exact long_block_strong hX hR hC hb d h hd t
  · exact paper_prime_block_bound hL hR t

end ZhangLS.Spec.DivisorConductorBlockMoments
