import ZhangLS.Spec.Lemma56PrimeWeightParameters

/-! # Actual finite Abel conversion for original Lemma 5.6

Actual prime-mass normalization and the faithful principal boundary remain separate obligations.
-/

namespace ZhangLS.Spec
open Complex MeasureTheory Finset
open scoped Real
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

lemma lemma56_actual_paper_prime_weight_budget {D q : ℕ} (θ : DirichletCharacter ℂ q)
    (hL : 2000 ≤ lemma23PaperL D) (τ : ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hc : ∀ {x : ℝ}, 1 ≤ x → x ≤ 2 * lemma23PaperP D →
      ‖lemma56SharpPrimeLogSum θ x τ‖ ≤ A) :
    ‖lemma56PrimeSum D θ τ‖ ≤ 4 * A * lemma23PaperP D := by
  have hp := lemma56_paper_prime_weight_parameters hL
  have hP0 : 0 ≤ lemma23PaperP D := (by norm_num : (0 : ℝ) ≤ 4).trans hp.2.1
  let m := ⌊lemma23PaperP D⌋₊ + 1
  let n := ⌈lemma56PrimeUpper D⌉₊
  let w : ℕ → ℝ := fun k => (k : ℝ) / Real.log (k : ℝ)
  let c : ℕ → ℂ := fun k => if k.Prime then
    (k : ℂ) ^ ((τ : ℂ) * I) * (θ (k : ZMod q) * (Real.log (k : ℝ) : ℂ)) else 0
  have hmP : lemma23PaperP D < (m : ℝ) := by
    dsimp [m]
    rw [Nat.cast_add, Nat.cast_one]
    exact Nat.lt_floor_add_one _
  have hm1 : 1 ≤ m := by dsimp [m]; omega
  have hnmax : (n : ℝ) ≤ 2 * lemma23PaperP D := hp.2.2.2.2
  have hmLog : 1 ≤ Real.log (m : ℝ) := hp.1.trans
    (Real.log_le_log (by linarith only [hp.2.1] : 0 < lemma23PaperP D) hmP.le)
  have hmw : 0 ≤ w m := by dsimp [w]; positivity
  have hc_range : ∀ k : ℕ, m ≤ k → k ≤ n → ‖∑ j ∈ range k, c j‖ ≤ A := by
    intro k hmk hkn
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hm1.trans hmk
    have hkmax : (k : ℝ) ≤ 2 * lemma23PaperP D :=
      (by exact_mod_cast hkn : (k : ℝ) ≤ n).trans hnmax
    simpa only [lemma56SharpPrimeLogSum, Nat.ceil_natCast] using hc hk1 hkmax
  rw [lemma56_actual_paper_prime_interval θ hP0]
  change ‖∑ k ∈ Ico m n, if k.Prime then θ (k : ZMod q) *
    (k : ℂ) ^ (1 + I * (τ : ℂ)) else 0‖ ≤ _
  have heq : (∑ k ∈ Ico m n, if k.Prime then θ (k : ZMod q) *
      (k : ℂ) ^ (1 + I * (τ : ℂ)) else 0) = ∑ k ∈ Ico m n, w k • c k := by
    apply sum_congr rfl
    intro k hk
    by_cases hkp : k.Prime
    · simp only [hkp, if_true, c, w]
      exact lemma56_actual_prime_weight_identity θ hkp τ
    · simp [hkp, c]
  rw [heq]
  by_cases hmn : m < n
  · have hmono : MonotoneOn w (Set.Icc m (n - 1)) := by
      intro a ha b hb hab
      have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast hm1.trans ha.1
      have hma : (m : ℝ) ≤ a := by exact_mod_cast ha.1
      apply lemma56_prime_weight_mono (by linarith only [ha1]) (by exact_mod_cast hab)
      exact hmLog.trans (Real.log_le_log (by exact_mod_cast (Nat.zero_lt_of_lt hm1)) hma)
    have hb := lemma56_finite_abel_positive_budget hmn w c hmono hmw hc_range
    have htopm : m ≤ n - 1 := Nat.le_sub_one_of_lt hmn
    have htop1 : 1 ≤ Real.log ((n - 1 : ℕ) : ℝ) := hmLog.trans
      (Real.log_le_log (by exact_mod_cast (Nat.zero_lt_of_lt hm1)) (by exact_mod_cast htopm))
    have htop0 : (0 : ℝ) ≤ (n - 1 : ℕ) := Nat.cast_nonneg _
    have htop : w (n - 1) ≤ 2 * lemma23PaperP D := by
      calc
        _ ≤ ((n - 1 : ℕ) : ℝ) := by
          dsimp [w]
          apply (div_le_iff₀ (by linarith only [htop1] : 0 < Real.log ((n - 1 : ℕ) : ℝ))).mpr
          have hh := mul_le_mul_of_nonneg_left htop1 htop0
          simpa only [mul_one] using hh
        _ ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n 1
        _ ≤ _ := hnmax
    exact hb.trans (by nlinarith only [mul_le_mul_of_nonneg_left htop (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hA)])
  · rw [Ico_eq_empty_of_le (by omega), sum_empty, norm_zero]
    positivity

end ZhangLS.Spec
