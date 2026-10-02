import ZhangLS.Spec.Proposition71FullConductorAggregate
import ZhangLS.Spec.Proposition71OriginalSmallConductor

/-! # Original β₃, strict sequences, and the full (7.13) positive majorant

The exact Gauss/induction derivation of the inequality (7.13) remains a
separate bridge. Its complete actual right-hand sum is proved negligible here.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Filter
open scoped Classical Topology
set_option maxHeartbeats 2000000

noncomputable def proposition71OriginalSigmaSeries {r : ℕ} (D : ℕ) (c : ℝ)
    (a : ℕ → ℂ) (h d : ℕ) (θ : DirichletCharacter ℂ r) : ℂ :=
  proposition71SigmaSeries D c (lemma23PaperOffsetThree D c) a h d θ

lemma proposition71_original_sigma_series_expanded {r : ℕ} (D : ℕ) (c : ℝ)
    (a : ℕ → ℂ) (h d : ℕ) (θ : DirichletCharacter ℂ r) :
    proposition71OriginalSigmaSeries D c a h d θ=
      ∑' l : ℕ, if 0<l ∧ l.Coprime h then
        (lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a) (d*l)*θ (l : ZMod r)*
          ∑ p∈lemma56PaperPrimes D, (p : ℂ)^lemma52PaperBetaThree D c*θ⁻¹ (p : ZMod r)*
            lemma53PaperDelta D ((l : ℝ)/((p : ℝ)*(h : ℝ)*(r : ℝ))) else 0 := rfl

noncomputable def proposition71OriginalConductorAggregate (D : ℕ) (c : ℝ) (a : ℕ → ℂ) : ℝ :=
  proposition71ActualConductorAggregate D c (lemma23PaperOffsetThree D c) a

/-- Uniform little-o for the entire genuine right-hand majorant of (7.13),
with all original phases, infinite coefficients, and strict support. -/
theorem proposition71_original_seven_thirteen_majorant_little_o :
    ∀ c : ℝ, 0<c → ∀ B : ℝ, 0<B → ∀ ε : ℝ, 0<ε →
      ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
        ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
          ∀ a : ℕ → ℂ, Lemma81AdmissibleSequence D B a →
            proposition71OriginalConductorAggregate D c a≤ε*lemma56PrimeMass D := by
  obtain ⟨C,hC,Dg,hDg,hbound⟩ := proposition71_actual_conductor_power_saving
  intro c hc B hB ε hε
  obtain ⟨Db,hbeta⟩ := proposition71_beta_three_height_margin hc
  have ht : Tendsto (fun D : ℕ => (D : ℝ)^(-1/32 : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,neg_div] using
      (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/32)).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨Da,hDa⟩ := eventually_atTop.mp ((tendsto_order.1 ht).2 (ε/(C*B)) (by positivity))
  refine ⟨max Dg (max Db Da),hDg.trans (le_max_left _ _),?_⟩
  intro D hDN χ hA a ha
  have hg := (le_max_left _ _).trans hDN
  have hb := (le_max_left _ _).trans ((le_max_right _ _).trans hDN)
  have hd := (le_max_right _ _).trans ((le_max_right _ _).trans hDN)
  have hs := hbound D hg χ hA c (lemma23PaperOffsetThree D c) B hB.le (hbeta D hb).2 a ha.1
  have hsmall : C*B*(D : ℝ)^(-1/32 : ℝ)≤ε := by
    simpa only [mul_comm] using le_of_lt ((lt_div_iff₀ (mul_pos hC hB)).mp (hDa D hd))
  apply hs.trans
  have hh := mul_le_mul_of_nonneg_right hsmall (lemma56_prime_mass_nonneg D)
  convert hh using 1 <;> ring

end ZhangLS.Spec
