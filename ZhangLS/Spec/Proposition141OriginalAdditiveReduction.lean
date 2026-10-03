import ZhangLS.Spec.Proposition141GaussFrontArithmetic

/-! The original Θ₂ is now attached to the actual additive source of (14.4),
including all signed prime-Gauss corrections and the full complex shift. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

/-- Faithful Θ₂-to-additive reduction with the original quantifier order.
The two Gauss corrections and the actual front are independently proved. -/
theorem proposition141_original_additive_reduction (Bκ Ba:ℝ) (hBκ:0<Bκ) (hBa:0<Ba)
    (ε:ℝ) (hε:0<ε) :
    ∃D₀:ℕ,2≤D₀ ∧ ∀D:ℕ,D₀≤D → ∀χ:RealPrimitiveCharacter D,NormalizedAssumptionA χ →
      ∀κ a:ℕ→ℂ,Proposition141KappaBound Bκ κ → Proposition141AdmissibleSequence D Ba a →
        ∀β:ℂ,‖β‖<5*lemma44PaperAlpha D →
          ‖proposition141ThetaTwo χ β κ a-proposition141AdditiveSourceMean χ β κ a‖≤
            ε*lemma33ActualPrimeMass D := by
  have hhalf:0<ε/2 := by positivity
  obtain ⟨Nf,hNf,hfront⟩ := proposition141_original_gauss_delta_reduction Bκ Ba hBκ hBa (ε/2) hhalf
  obtain ⟨Nc,hNc,hcor⟩ := proposition141_uniform_prime_front_saving Bκ Ba hBκ hBa (ε/2) hhalf
  obtain ⟨Ns,hNs,hmod⟩ := proposition141_uniform_support_modulus_bound
  let D₀ := max Nf (max Nc (max Ns ⌈Real.exp 2000⌉₊))
  refine ⟨D₀,hNf.trans (le_max_left _ _),?_⟩
  intro D hlarge χ hA κ a hκ ha β hβ
  have hf:Nf≤D := by dsimp [D₀] at hlarge; omega
  have hc:Nc≤D := by dsimp [D₀] at hlarge; omega
  have hs:Ns≤D := by dsimp [D₀] at hlarge; omega
  have he:⌈Real.exp 2000⌉₊≤D := by dsimp [D₀] at hlarge; omega
  have hD:1<D := by have := hNf.trans hf; omega
  have hL:2000≤lemma23PaperL D := by
    have hex:Real.exp 2000≤(D:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast he)
    simpa only [lemma23PaperL,Real.log_exp] using Real.log_le_log (Real.exp_pos _) hex
  have h1 := hfront D hf χ hA κ a hκ ha β hβ
  have h2 := hcor χ hc β hβ κ a hκ ha
  have hid := proposition141_gauss_front_additive_difference χ hD hL (hmod D hs) hBκ.le hκ a β
  have hsplit : proposition141ThetaTwo χ β κ a-proposition141AdditiveSourceMean χ β κ a=
      (proposition141ThetaTwo χ β κ a-proposition141GaussDeltaOneMean χ β κ a)+
        proposition141PrimeFrontCorrectionTotal χ β κ a := by rw [←hid]; ring
  rw [hsplit]
  exact (norm_add_le _ _).trans ((add_le_add h1 h2).trans_eq (by ring))

end ZhangLS.Spec
