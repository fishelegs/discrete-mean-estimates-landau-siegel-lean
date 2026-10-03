import ZhangLS.Spec.Proposition71PrincipalPointwise
import ZhangLS.Spec.Proposition71PrincipalResidueRearrangement
import ZhangLS.Spec.Proposition71PrincipalEnvelopeWeights

/-! The proved genuine local contour bound is multiplied by the actual
source coefficients, retaining q, tau5 and every finite-prime factor until
its exact exterior arithmetic weight is exposed. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 4500000

noncomputable def proposition71PrincipalExteriorWeight (D d₁ d₂ k l₂ : ℕ) : ℝ :=
  (lemma34Tau 5 d₁ : ℝ)*proposition71KappaEulerEnvelope d₁ (1-1/lemma23PaperL D)*
    proposition71LambdaEulerEnvelope (d₁*d₂*k) (1-1/lemma23PaperL D)/
      ((d₁ : ℝ)*(d₂ : ℝ)*(k.totient : ℝ)*(l₂ : ℝ))

lemma proposition71_principal_left_re_lower {D : ℕ} (hL : 2≤lemma23PaperL D) :
    1/2≤1-1/lemma23PaperL D := by
  have hLp : 0<lemma23PaperL D := by linarith
  have hi : 1/lemma23PaperL D≤(1/2 : ℝ) := (div_le_iff₀ hLp).mpr (by linarith)
  linarith

lemma proposition71_principal_exterior_weight_nonneg {D : ℕ}
    (hL : 2≤lemma23PaperL D) (d₁ d₂ k l₂ : ℕ) :
    0≤proposition71PrincipalExteriorWeight D d₁ d₂ k l₂ := by
  have hK := proposition71_kappa_half_strip_envelope_nonneg d₁ (proposition71_principal_left_re_lower hL)
  have hLam := proposition71_lambda_half_strip_envelope_nonneg (d₁*d₂*k) (proposition71_principal_left_re_lower hL)
  unfold proposition71PrincipalExteriorWeight
  positivity

/-- A real, proved local contour bound at every original supported source
term. No desired analytic estimate is supplied as a hypothesis. -/
theorem proposition71_principal_quad_contour_bound {c : ℝ} (hc : 0<c) :
    ∃D₀ : ℕ,2≤D₀ ∧ ∀D : ℕ,D₀≤D → ∀p : ℕ,p∈lemma56PaperPrimes D →
      ∀B₁ B₂ : ℝ,0≤B₁ → 0≤B₂ → ∀a₁ a₂ : ℕ → ℂ,
        Lemma81AdmissibleSequence D B₁ a₁ → Lemma81AdmissibleSequence D B₂ a₂ →
        ∀d₁ d₂ k l₂ : ℕ,0<d₁ → 0<d₂ → 0<k → 0<l₂ →
          ‖proposition71PrincipalQuadTerm D p c a₁ a₂ d₁ d₂ k l₂-
            proposition71PrincipalQuadResidue D p c a₁ a₂ d₁ d₂ k l₂‖≤
            (proposition71PrincipalContourConstant*B₁*B₂*(p : ℝ)*lemma23PaperL D^3244*
              Real.exp (-(lemma23PaperL D)^(1/10 : ℝ)))*
                proposition71PrincipalExteriorWeight D d₁ d₂ k l₂ := by
  obtain ⟨N,hN,hcontour⟩ := proposition71_original_principal_contour hc
  refine ⟨max N ⌈Real.exp 2000⌉₊,hN.trans (le_max_left _ _),?_⟩
  intro D hD p hp B₁ B₂ hB₁ hB₂ a₁ a₂ ha₁ ha₂ d₁ d₂ k l₂ hd₁ hd₂ hk hl₂
  have hND := (le_max_left _ _).trans hD
  have he : Real.exp 2000≤(D : ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_right _ _).trans hD)
  have hL : 2000≤lemma23PaperL D := by
    simpa only [lemma23PaperL,Real.log_exp] using Real.log_le_log (Real.exp_pos 2000) he
  have hW0 := proposition71_principal_exterior_weight_nonneg (by linarith : 2≤lemma23PaperL D) d₁ d₂ k l₂
  have hC := proposition71_principal_contour_constant_pos
  by_cases hs : d₁*d₂*k∈lemma81PolynomialIndices D ∧ l₂.Coprime k
  · by_cases ha0 : a₁ (d₂*l₂)=0
    · simp only [proposition71PrincipalQuadTerm,proposition71PrincipalQuadResidue,if_pos hs,ha0,
        mul_zero,zero_div,zero_mul,sub_self,norm_zero]
      positivity
    · have hsupport : d₂*l₂∈lemma81PolynomialIndices D := by
        apply (proposition71_mem_indices D _).mpr
        exact ⟨Nat.mul_pos hd₂ hl₂,lt_of_not_ge (fun hh => ha0 (ha₁.2 _ hh))⟩
      have hb := hcontour D hND p d₁ d₂ k l₂ hp hd₁ hd₂ hk hl₂ hsupport hs.1
      let K : ℂ := a₂ (d₁*d₂*k)*(ArithmeticFunction.moebius k : ℂ)*a₁ (d₂*l₂)/
        ((d₁ : ℂ)*(d₂ : ℂ)*(k : ℂ)*(k.totient : ℂ))
      have hK : ‖K‖≤B₂*B₁/((d₁ : ℝ)*(d₂ : ℝ)*(k : ℝ)*(k.totient : ℝ)) := by
        dsimp [K]
        simp only [norm_div,norm_mul,Complex.norm_natCast]
        apply div_le_div_of_nonneg_right _ (by positivity)
        have hmu := inducedGauss_mobius_norm_le_one k
        have hh := mul_le_mul (mul_le_mul (ha₂.1 (d₁*d₂*k)) hmu
          (norm_nonneg (ArithmeticFunction.moebius k : ℂ)) hB₂)
          (ha₁.1 (d₂*l₂)) (norm_nonneg (a₁ (d₂*l₂))) (mul_nonneg hB₂ zero_le_one)
        simpa only [mul_one] using hh
      unfold proposition71PrincipalQuadTerm proposition71PrincipalQuadResidue
      rw [if_pos hs,if_pos hs,←mul_sub,norm_mul]
      have hh := mul_le_mul hK hb (norm_nonneg _) (by positivity)
      apply hh.trans_eq
      unfold proposition71PrincipalExteriorWeight
      have hd₁R : (d₁ : ℝ)≠0 := by exact_mod_cast hd₁.ne'
      have hd₂R : (d₂ : ℝ)≠0 := by exact_mod_cast hd₂.ne'
      have hkR : (k : ℝ)≠0 := by exact_mod_cast hk.ne'
      have hl₂R : (l₂ : ℝ)≠0 := by exact_mod_cast hl₂.ne'
      have hφR : (k.totient : ℝ)≠0 := by exact_mod_cast (Nat.totient_pos.mpr hk).ne'
      field_simp
  · simp only [proposition71PrincipalQuadTerm,proposition71PrincipalQuadResidue,if_neg hs,sub_self,norm_zero]
    positivity

end ZhangLS.Spec
