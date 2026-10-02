import ZhangLS.Spec.Proposition71QuarterConductorSaving

/-! # The original β₃ specialization of the proved small-conductor component

The paper's three shifts and strict coefficient support are retained. The
quarter-power split is an explicit proof repair. The l>P² tail and passage
from the Gauss-averaged θ₁₂ expression remain unproved here.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex
set_option maxHeartbeats 2000000

noncomputable def proposition71OriginalSigmaTruncated {r : ℕ}
    (D : ℕ) (c : ℝ) (a : ℕ → ℂ) (h d : ℕ) (θ : DirichletCharacter ℂ r) : ℂ :=
  proposition71SigmaTruncated D c (lemma23PaperOffsetThree D c) a h d θ

lemma proposition71_original_sigma_expanded {r : ℕ}
    (D : ℕ) (c : ℝ) (a : ℕ → ℂ) (h d : ℕ) (θ : DirichletCharacter ℂ r) :
    proposition71OriginalSigmaTruncated D c a h d θ=
      ∑ l∈(Finset.Icc 1 ⌊lemma23PaperP D^2⌋₊).filter (fun l => l.Coprime h),
        (lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a) (d*l)*θ (l : ZMod r)*
          ∑ p∈lemma56PaperPrimes D, (p : ℂ)^lemma52PaperBetaThree D c*θ⁻¹ (p : ZMod r)*
            lemma53PaperDelta D ((l : ℝ)/((p : ℝ)*(h : ℝ)*(r : ℝ))) := rfl

noncomputable def proposition71OriginalQuarterAggregate (D : ℕ) (c : ℝ) (a : ℕ → ℂ) : ℝ :=
  proposition71SmallConductorAggregate D c (lemma23PaperOffsetThree D c) a
    ⌊lemma23PaperP D⌋₊ ⌊(D : ℝ)^(1/4 : ℝ)⌋₊

/-- The actual β₃ is inside the allowed translated-height margin. -/
theorem proposition71_beta_three_height_margin {c : ℝ} (hc : 0<c) :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀≤D →
      3≤lemma23PaperL D ∧ |lemma23PaperOffsetThree D c|≤(D : ℝ)/2 := by
  obtain ⟨Ds,hDs,hsmall⟩ := lemma52_exists_shift_threshold hc
  refine ⟨max Ds 6,?_⟩
  intro D hD
  have hDsD := (le_max_left _ _).trans hD
  have hD6 : (6:ℝ)≤D := by exact_mod_cast (le_max_right _ _).trans hD
  have hL := (lemma44_parameters_at_explicit_threshold (hDs.trans hDsD)).1
  have hβ := (lemma52_offset_bounds hL hc (hsmall D hDsD)).2.2
  have ha := (lemma44_alpha_pos_le_one hL).2
  refine ⟨hL,?_⟩
  rw [abs_of_nonneg hβ.1]
  nlinarith only [hβ.2,ha,hD6]

/-- The complete original β₃/κ/a specialization, with strict (7.2) support.
This is a proved truncated small-conductor component, not a claim of (7.11). -/
theorem proposition71_original_quarter_aggregate_power_saving :
    ∃ C : ℝ, 0<C ∧ ∀ c : ℝ, 0<c → ∃ D₀ : ℕ, 2≤D₀ ∧
      ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
        ∀ B : ℝ, 0≤B → ∀ a : ℕ → ℂ, Lemma81AdmissibleSequence D B a →
          proposition71OriginalQuarterAggregate D c a≤
            C*B*lemma56PrimeMass D*(D : ℝ)^(-1/2 : ℝ) := by
  obtain ⟨C,hC,Dk,hDk,hkernel⟩ := proposition71_quarter_small_conductor_power_saving
  refine ⟨C,hC,?_⟩
  intro c hc
  obtain ⟨Db,hbeta⟩ := proposition71_beta_three_height_margin hc
  refine ⟨max Dk Db,hDk.trans (le_max_left _ _),?_⟩
  intro D hD χ hA B hB a ha
  have hdk := (le_max_left _ _).trans hD
  have hdb := (le_max_right _ _).trans hD
  have hb := hbeta D hdb
  have hP : 1≤lemma23PaperP D := by
    apply Real.one_le_exp_iff.mpr
    exact pow_nonneg (by linarith : 0≤lemma23PaperL D) 9
  exact hkernel D hdk χ hA c (lemma23PaperOffsetThree D c) B hB hb.2 a ha.1
    ⌊lemma23PaperP D⌋₊ ⌊(D : ℝ)^(1/4 : ℝ)⌋₊
    (Nat.le_floor (by simpa only [Nat.cast_one] using hP))
    (Nat.floor_le (by positivity)) (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg D) _))

end ZhangLS.Spec
