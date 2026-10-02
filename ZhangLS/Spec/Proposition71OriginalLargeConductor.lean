import ZhangLS.Spec.Proposition71LargeConductorSaving

/-! # The original β₃ specialization and uniform localized large-conductor error

These are the exact original coefficients, prime phase and strict (7.2)
support. The theorem still concerns the genuinely defined localized sum; the
σ−σ* localization error is not hidden in its definition or conclusion.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Filter
open scoped Classical Topology
set_option maxHeartbeats 2000000

noncomputable def proposition71OriginalSigmaStar {r : ℕ} (D : ℕ) (c : ℝ)
    (a : ℕ → ℂ) (R : ℝ) (h d : ℕ) (θ : DirichletCharacter ℂ r) : ℂ :=
  proposition71SigmaStar D c (lemma23PaperOffsetThree D c) a R h d θ

lemma proposition71_original_sigma_star_expanded {r : ℕ} (D : ℕ) (c : ℝ)
    (a : ℕ → ℂ) (R : ℝ) (h d : ℕ) (θ : DirichletCharacter ℂ r) :
    proposition71OriginalSigmaStar D c a R h d θ=
      ∑ l∈proposition71LocalizedIndices D R h,
        (lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a) (d*l)*θ (l : ZMod r)*
          ∑ p∈lemma56PaperPrimes D, (p : ℂ)^lemma52PaperBetaThree D c*θ⁻¹ (p : ZMod r)*
            lemma53PaperDelta D ((l : ℝ)/((p : ℝ)*(h : ℝ)*(r : ℝ))) := rfl

noncomputable def proposition71OriginalLocalizedLargeAggregate (D : ℕ) (c : ℝ)
    (a : ℕ → ℂ) : ℝ :=
  proposition71LocalizedLargeAggregate D c (lemma23PaperOffsetThree D c) a ⌊lemma23PaperP D⌋₊

theorem proposition71_original_localized_large_power_saving :
    ∃ C : ℝ, 0<C ∧ ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ → ∀ c B : ℝ, 0≤B →
        ∀ a : ℕ → ℂ, Lemma81AdmissibleSequence D B a →
          proposition71OriginalLocalizedLargeAggregate D c a≤
            C*B*lemma56PrimeMass D*(D : ℝ)^(-1/32 : ℝ) := by
  obtain ⟨C,hC,D₀,hD₀,hlarge⟩ := proposition71_localized_large_aggregate_power_saving
  refine ⟨C,hC,max D₀ 2,hD₀.trans (le_max_left _ _),?_⟩
  intro D hD χ hA c B hB a ha
  have hD2 : 2≤D := (le_max_right _ _).trans hD
  have hL : 0≤lemma23PaperL D := Real.log_natCast_nonneg D
  have hP : 1≤lemma23PaperP D := Real.one_le_exp_iff.mpr (pow_nonneg hL 9)
  exact hlarge D ((le_max_left _ _).trans hD) χ hA c (lemma23PaperOffsetThree D c) B hB a ha.1
    ⌊lemma23PaperP D⌋₊ (Nat.le_floor (by simpa only [Nat.cast_one] using hP))
    (Nat.floor_le (by positivity))

/-- Genuine uniform little-o for the original localized positive majorant.
The threshold is independent of c and of the chosen admissible sequence. -/
theorem proposition71_original_localized_large_little_o :
    ∀ B : ℝ, 0<B → ∀ ε : ℝ, 0<ε → ∃ D₀ : ℕ, 2≤D₀ ∧
      ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
        ∀ c : ℝ, ∀ a : ℕ → ℂ, Lemma81AdmissibleSequence D B a →
          proposition71OriginalLocalizedLargeAggregate D c a≤ε*lemma56PrimeMass D := by
  obtain ⟨C,hC,Dg,hDg,hbound⟩ := proposition71_original_localized_large_power_saving
  intro B hB ε hε
  have ht : Tendsto (fun D : ℕ => (D : ℝ)^(-1/32 : ℝ)) atTop (𝓝 0) :=
    by simpa only [Function.comp_def,neg_div] using
      (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/32)).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hevent := (tendsto_order.1 ht).2 (ε/(C*B)) (by positivity)
  obtain ⟨Da,hDa⟩ := eventually_atTop.mp hevent
  refine ⟨max Dg Da,hDg.trans (le_max_left _ _),?_⟩
  intro D hD χ hA c a ha
  have hs := hbound D ((le_max_left _ _).trans hD) χ hA c B hB.le a ha
  have hd := hDa D ((le_max_right _ _).trans hD)
  have hscalar : C*B*(D : ℝ)^(-1/32 : ℝ)≤ε :=
    by simpa only [mul_comm] using (le_of_lt ((lt_div_iff₀ (mul_pos hC hB)).mp hd))
  apply hs.trans
  have he := mul_le_mul_of_nonneg_right hscalar (lemma56_prime_mass_nonneg D)
  convert he using 1 <;> ring

end ZhangLS.Spec
