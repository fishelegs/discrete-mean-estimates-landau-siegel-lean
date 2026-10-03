import ZhangLS.Spec.Proposition71PrincipalContourWeights
import ZhangLS.Spec.FiniteFourSumNorm

/-! The actual finite principal error before the logarithmic budget. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 700000

theorem proposition71_principal_prime_finite_error {c : ℝ} (hc : 0<c) :
    ∃D₀ : ℕ,2≤D₀ ∧ ∀D : ℕ,D₀≤D → ∀p : ℕ,p∈lemma56PaperPrimes D →
      ∀B₁ B₂ : ℝ,0≤B₁ → 0≤B₂ → ∀a₁ a₂ : ℕ → ℂ,
        Lemma81AdmissibleSequence D B₁ a₁ → Lemma81AdmissibleSequence D B₂ a₂ →
        ‖proposition71PrimePrincipalMean D p c a₁ a₂-
          (∑j : Fin 3,proposition71ActualR D c j*(p : ℂ)^(1-lemma83PaperBeta D c j)*
            proposition71ArithmeticSum D c j a₁ a₂)‖≤
          (proposition71PrincipalContourConstant*B₁*B₂*(p : ℝ)*lemma23PaperL D^3244*
            Real.exp (-(lemma23PaperL D)^(1/10 : ℝ)))*
          (∑d₁∈lemma81PolynomialIndices D,∑d₂∈lemma81PolynomialIndices D,
            ∑k∈lemma81PolynomialIndices D,∑l₂∈lemma81PolynomialIndices D,
              proposition71PrincipalExteriorWeight D d₁ d₂ k l₂) := by
  obtain ⟨N,hN,hterm⟩ := proposition71_principal_quad_contour_bound hc
  refine ⟨max N ⌈Real.exp 2000⌉₊,hN.trans (le_max_left _ _),?_⟩
  intro D hD p hp B₁ B₂ hB₁ hB₂ a₁ a₂ ha₁ ha₂
  have hND := (le_max_left _ _).trans hD
  have hD2 : 2≤D := hN.trans hND
  have he : Real.exp 2000≤(D : ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_right _ _).trans hD)
  have hL : 2000≤lemma23PaperL D := by
    simpa only [lemma23PaperL,Real.log_exp] using Real.log_le_log (Real.exp_pos 2000) he
  have hp0 := ((lemma56_mem_paper_primes D p).mp hp).1.pos
  rw [proposition71_prime_principal_eq_quad (by omega) hL c hp0 a₁ a₂ ha₁,
    ←proposition71_principal_quad_residue_sum hp0 c a₁ a₂ ha₁ ha₂]
  exact finiteFourSum_norm_sub_le (lemma81PolynomialIndices D)
    (proposition71PrincipalQuadTerm D p c a₁ a₂) (proposition71PrincipalQuadResidue D p c a₁ a₂)
    (proposition71PrincipalExteriorWeight D)
    (proposition71PrincipalContourConstant*B₁*B₂*(p : ℝ)*lemma23PaperL D^3244*
      Real.exp (-(lemma23PaperL D)^(1/10 : ℝ)))
    (fun d₁ hd₁ d₂ hd₂ k hk l₂ hl₂ =>
      hterm D hND p hp B₁ B₂ hB₁ hB₂ a₁ a₂ ha₁ ha₂ d₁ d₂ k l₂
        ((proposition71_mem_indices D d₁).mp hd₁).1 ((proposition71_mem_indices D d₂).mp hd₂).1
        ((proposition71_mem_indices D k).mp hk).1 ((proposition71_mem_indices D l₂).mp hl₂).1)

end ZhangLS.Spec
