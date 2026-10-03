import ZhangLS.Spec.Proposition141RemainingMeanBound
import ZhangLS.Spec.Proposition141ResidualBound
import ZhangLS.Spec.QuotientSourceRate

/-! The actual remaining character mean inherits the proved full conductor
saving only after all exact original-source and coefficient attachments. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace ZhangLS.Spec
open Complex

/-- Uniform negligibility of the literal remaining original character mean. -/
theorem proposition141_actual_remaining_little_o (Bκ Ba:ℝ) (hBκ:0<Bκ) (hBa:0<Ba)
    (ε:ℝ) (hε:0<ε) :
    ∃D₀:ℕ,2≤D₀ ∧ ∀D:ℕ,D₀≤D → ∀χ:RealPrimitiveCharacter D,NormalizedAssumptionA χ →
      ∀κ a:ℕ→ℂ,Proposition141KappaBound Bκ κ → Proposition141AdmissibleSequence D Ba a →
        ∀β:ℂ,‖β‖<5*lemma44PaperAlpha D →
          ‖proposition141RemainingMean χ β κ a‖≤ε*lemma33ActualPrimeMass D := by
  obtain ⟨N,hN,hsource⟩ := quotientSource_normalized_little_o Bκ Ba hBκ hBa ε hε
  obtain ⟨Ns,hNs,hmod⟩ := proposition141_uniform_support_modulus_bound
  let D₀ := max N (max Ns ⌈Real.exp 2000⌉₊)
  refine ⟨D₀,hN.trans (le_max_left _ _),?_⟩
  intro D hlarge χ hA κ a hκ ha β hβ
  have hND:N≤D := by dsimp [D₀] at hlarge; omega
  have hNsD:Ns≤D := by dsimp [D₀] at hlarge; omega
  have hNe:⌈Real.exp 2000⌉₊≤D := by dsimp [D₀] at hlarge; omega
  have hD:1<D := by have := hN.trans hND; omega
  have hL:2000≤lemma23PaperL D := by
    have he:Real.exp 2000≤(D:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hNe)
    simpa only [lemma23PaperL,Real.log_exp] using Real.log_le_log (Real.exp_pos _) he
  have hfinite : ‖proposition141RemainingMean χ β κ a‖≤proposition141FiniteResidualMajorant χ β κ a :=
    proposition141_remaining_mean_norm_le χ β κ a
  exact (hfinite.trans (proposition141_finite_residual_majorant_le_quotient χ β hD hL
    (hmod D hNsD) hBκ.le hκ ha)).trans (hsource D hND χ hA κ a hκ ha β hβ)

end ZhangLS.Spec
