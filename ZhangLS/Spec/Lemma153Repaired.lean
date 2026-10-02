import ZhangLS.Spec.Lemma153PaperCenterComparison
import ZhangLS.Spec.Lemma153RamifiedStrip
import ZhangLS.Spec.Lemma153OriginalNormalization
/-!
# Lemma15.3: explicit, source-audited shifted-L repair

Original arXiv:2211.02515v1 p.87 defines U₁ⱼ but prints U₂ⱼ(1), and uses
undefined α₁. The exact arithmetic prime term forces L(s−βⱼ,χ)² rather than
L(s,χ)² in the extraction. We retain the genuine varpi from (15.19), the
actual M₁(d,l) continuation and all three original shared-c′ shifts. We prove
all denominator nonvanishing, all Dirichlet/Euler bridges, an O(α) center
error, and the original ramification-restricted main term.

The old normalization is related to this one only in Re s>1 by the separately
proved exact factor (L(s−βⱼ,χ)/L(s,χ))². No unshifted analytic continuation or
unconditional counterexample to the original printed claim is asserted.

Boundedness on the entire Re s≥9/10 keeps its explicit D-dependence. For the
thin contour strip Re s≥1−1/log D we additionally prove a uniform absolute
constant times (1+log log D)^18. The downstream shifted-L Mellin residue
calculation is a separate task and is not assumed here.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex
set_option maxHeartbeats 1500000

noncomputable def lemma153StripConstant : ℝ :=
  lemma153UnramifiedProductBound*(Real.exp (3/Real.log 2))^2

lemma lemma153_strip_constant_pos : 0 < lemma153StripConstant := by
  unfold lemma153StripConstant lemma153UnramifiedProductBound
  positivity

/-- A concrete repaired version of the original lemma, with no assumed main
estimate and no α₁ convention. Every M and U is the actual constructed
continuation of its original arithmetic series. -/
def Lemma153RepairedAt (c : ℝ) : Prop :=
  ∃ C : ℝ, 0<C ∧ ∃ D₀ : ℕ, 3≤D₀ ∧
    ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D,
      (∀ d l : ℕ, d ≠ 0 → l ≠ 0 →
        Lemma152Continuation χ (lemma152PaperBeta D c) d l
          (lemma153GeneralMEulerProduct χ (lemma152PaperBeta D c) d l)) ∧
      ∀ j : Fin 3,
        lemma153GeneralMEulerProduct χ (lemma152PaperBeta D c) 1 1
          (1-lemma83PaperBeta D c j) ≠ 0 ∧
        Lemma153ShiftedContinuation χ (lemma152PaperBeta D c) (lemma83PaperBeta D c j)
          (lemma153GeneralMEulerProduct χ (lemma152PaperBeta D c))
          (lemma153EulerProduct χ (lemma152PaperBeta D c) (lemma83PaperBeta D c j)) ∧
        AnalyticOnNhd ℂ (lemma153EulerProduct χ (lemma152PaperBeta D c) (lemma83PaperBeta D c j))
          {s : ℂ | 9/10 ≤ s.re} ∧
        (∀ s : ℂ, 9/10 ≤ s.re →
          ‖lemma153EulerProduct χ (lemma152PaperBeta D c) (lemma83PaperBeta D c j) s‖ ≤ lemma153DBound D) ∧
        ‖lemma153EulerProduct χ (lemma152PaperBeta D c) (lemma83PaperBeta D c j) 1 -
          (Nat.totient D:ℂ)^2/(D:ℂ)^2 *
            ∏' q : {q : Nat.Primes // ¬q.val ∣ D},
              (1-(q.val.val:ℂ)^(-2:ℤ))^2/(1-χ.evalNat q.val.val*(q.val.val:ℂ)^(-2:ℤ))‖ ≤
                C*lemma44PaperAlpha D ∧
        (∀ s : ℂ, 9/10 ≤ s.re → 1-(Real.log D)⁻¹ ≤ s.re →
          ‖lemma153EulerProduct χ (lemma152PaperBeta D c) (lemma83PaperBeta D c j) s‖ ≤
            lemma153StripConstant*(1+Real.log (Real.log D))^18)

def Lemma153RepairedTarget : Prop := ∀ c : ℝ, 0<c → Lemma153RepairedAt c

/-- The full explicit repaired15.3, with shared-shift and uniformity checks. -/
theorem lemma153_repaired_proved : Lemma153RepairedTarget := by
  intro c hc
  obtain ⟨D₁,hD1,hbridge⟩ := lemma153_paper_shifted_analytic_bridge hc
  obtain ⟨D₂,hD2,hpar⟩ := lemma153_small_parameters_threshold hc
  obtain ⟨D₃,hD3,hcenter⟩ := lemma153_paper_repaired_center_explicit hc
  obtain ⟨D₄,hD4,hnonzero⟩ := lemma153_normalization_nonzero_threshold hc
  refine ⟨lemma153PaperCenterConstant,lemma153_paper_center_constant_pos,
    max 3 (max D₁ (max D₂ (max D₃ D₄))),le_max_left _ _,?_⟩
  intro D hD χ
  have hDthree : 3≤D := (le_max_left _ _).trans hD
  have hD1' : D₁≤D := (le_max_left _ _).trans ((le_max_right _ _).trans hD)
  have hD2' : D₂≤D := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hD))
  have hD3' : D₃≤D := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hD)))
  have hD4' : D₄≤D := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hD)))
  refine ⟨fun d l hd hl => lemma153_general_m_actual_continuation χ _ (lemma152_beta_re D c) hd hl,?_⟩
  intro j
  have hb := hbridge D hD1' χ j
  refine ⟨by simpa using hnonzero D hD4' χ j,hb.1,hb.2.1,hb.2.2,hcenter D hD3' χ j,?_⟩
  intro s hs hstrip
  exact lemma153_euler_product_strip_bound hDthree χ _ _ (hpar D hD2' j) s (by linarith) hstrip

/-- Specialization to exactly the earlier compatible c′, rather than silently
selecting a new shift convention for this lemma. -/
theorem lemma153_with_shared_shift_constant :
    ∃ c : ℝ, 0<c ∧ Lemma52CompatibleConstant c ∧ Lemma153RepairedAt c := by
  obtain ⟨c,hc,hcompatible,C,hC,D₀,hrest⟩ := lemma52_proved
  exact ⟨c,hc,hcompatible,lemma153_repaired_proved c hc⟩

end ZhangLS.Spec
