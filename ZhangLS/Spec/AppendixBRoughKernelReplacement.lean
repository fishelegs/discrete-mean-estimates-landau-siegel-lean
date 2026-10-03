import ZhangLS.Spec.AppendixBRoughWeightedReplacement

/-! Actual infinite-notation one-kernel replacement. The full rho sum on the
right is definitionally the frozen full-kernel packet's appendixBFullKernelSum;
that packet is not modified or recompiled here. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical

/-- Strict kernel support makes the genuine infinite notation a finite sum.
The floor endpoint is kept and the kernel itself vanishes at equality. -/
lemma appendixB_kernel_tsum_finite (X P : ℝ) (γ : ℂ) (n₁ : ℕ)
    (hn₁ : 0<n₁) (hXP : X≤P) (f : ℕ→ℂ) (q : ℕ→Prop) [DecidablePred q] :
    (∑' n : ℕ,if q n then lemma151Kernel X γ (n₁*n)*f n/n else 0)=
      ∑ n∈(Icc 1 ⌊P⌋₊).filter q,lemma151Kernel X γ (n₁*n)*f n/n := by
  have he : (∑' n : ℕ,if q n then lemma151Kernel X γ (n₁*n)*f n/n else 0)=
      ∑ n∈(Icc 1 ⌊P⌋₊).filter q,
        if q n then lemma151Kernel X γ (n₁*n)*f n/n else 0 := by
    apply tsum_eq_sum
    intro n hn
    by_cases hq : q n
    · rw [if_pos hq]
      by_cases hn0 : n=0
      · simp [hn0]
      have hlarge : ⌊P⌋₊<n := by
        by_contra h
        exact hn (mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_ne_zero hn0,by omega⟩,hq⟩)
      have hPn : P<(n : ℝ) := Nat.lt_of_floor_lt hlarge
      have hmul : (n : ℝ)≤((n₁*n : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_mul_of_pos_left n hn₁
      have hcut : ¬((n₁*n : ℕ) : ℝ)<X := not_lt_of_ge (hXP.trans (hPn.le.trans hmul))
      have hz : lemma151Kernel X γ (n₁*n)=0 := by
        unfold lemma151Kernel
        rw [if_neg (fun h => hcut h.2)]
      rw [hz]
      simp
    · simp [hq]
  rw [he]
  exact sum_congr rfl (fun n hn => if_pos (mem_filter.mp hn).2)

/-- The genuine one-kernel source replacement, ready to combine with the frozen
unconditional full-kernel asymptotics. It preserves n1 and the actual c,j shifts. -/
theorem appendixB_actual_kernel_rhostar_to_full_uniform (c : ℝ) (hc : 0<c) :
    ∃ D₀ : ℕ,∀ D : ℕ,D₀≤D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ → ∀ j : Fin 3, ∀ X : ℝ,X≤lemma23PaperP D →
      ∀ γ : ℂ,γ.re=0 → ∀ n₁ : ℕ,0<n₁ →
      ‖(∑' n : ℕ,if n.Coprime (lemma151Q D) then
          lemma151Kernel X γ (n₁*n)*lemma151RhoStar χ (lemma83PaperBeta D c j) n/n else 0)-
        (∑' n : ℕ,lemma151Kernel X γ (n₁*n)*lemma151Rho (lemma83PaperBeta D c j) n/n)‖≤
        appendixBReplacementConstant*lemma23PaperL D^(-8 : ℤ) := by
  obtain ⟨D₀,hD₀⟩ := appendixB_kernel_replacement_uniform c hc
  refine ⟨D₀,?_⟩
  intro D hD χ hA j X hXP γ hγ n₁ hn₁
  have hP1 : 1≤lemma23PaperP D := by
    unfold lemma23PaperP lemma23PaperL
    exact Real.one_le_exp_iff.mpr (pow_nonneg (Real.log_natCast_nonneg D) 9)
  have hN : 1≤⌊lemma23PaperP D⌋₊ := (Nat.one_le_floor_iff _).mpr hP1
  have hNP : (⌊lemma23PaperP D⌋₊ : ℝ)≤lemma23PaperP D := Nat.floor_le (by linarith)
  rw [appendixB_kernel_tsum_finite X (lemma23PaperP D) γ n₁ hn₁ hXP
    (lemma151RhoStar χ (lemma83PaperBeta D c j)) (fun n => n.Coprime (lemma151Q D))]
  have hfull := appendixB_kernel_tsum_finite X (lemma23PaperP D) γ n₁ hn₁ hXP
    (lemma151Rho (lemma83PaperBeta D c j)) (fun _ => True)
  simp only [ite_true,filter_true] at hfull
  rw [hfull]
  exact hD₀ D hD χ hA j ⌊lemma23PaperP D⌋₊ hN hNP _ (by intro n hn; exact hn) X γ hγ n₁

end ZhangLS.Spec
