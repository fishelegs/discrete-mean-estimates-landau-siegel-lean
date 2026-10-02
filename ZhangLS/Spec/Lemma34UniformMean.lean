import ZhangLS.Spec.Lemma34ShortMean
set_option autoImplicit false
namespace ZhangLS.Spec
set_option maxHeartbeats 2000000

lemma lemma34_cutoff_le_P {D : ℕ} (hL : 3 ≤ lemma23PaperL D) :
    (D : ℝ)^80 ≤ lemma23PaperP D := by
  have hD : 0 < (D : ℝ) := by
    by_cases h : D = 0
    · simp [h,lemma23PaperL] at hL
      linarith
    · exact_mod_cast Nat.pos_of_ne_zero h
  have hpow : (3 : ℝ)^8 ≤ lemma23PaperL D^8 :=
    pow_le_pow_left₀ (by norm_num) hL 8
  have hc : 80 ≤ lemma23PaperL D^8 := by norm_num at hpow ⊢; linarith
  have ha : 80 * lemma23PaperL D ≤ lemma23PaperL D^9 := by
    calc
      _ ≤ lemma23PaperL D^8 * lemma23PaperL D :=
        mul_le_mul_of_nonneg_right hc (by linarith)
      _ = _ := (pow_succ _ _).symm
  calc
    _ = Real.exp (80 * lemma23PaperL D) := by
      have ht := Real.exp_nat_mul (lemma23PaperL D) 80
      norm_num at ht
      rw [lemma23PaperL,Real.exp_log hD] at ht
      exact ht.symm
    _ ≤ _ := Real.exp_le_exp.mpr ha

lemma lemma34_cutoff_nat_le_floor_P {D : ℕ} (hL : 3 ≤ lemma23PaperL D) :
    D^80 ≤ ⌊lemma23PaperP D⌋₊ := by
  apply (Nat.le_floor_iff (Real.exp_pos _).le).mpr
  simpa only [Nat.cast_pow] using lemma34_cutoff_le_P hL

lemma lemma34_coefficient_log_bound {D X : ℕ} (hL : 3 ≤ lemma23PaperL D)
    (hX : 1 ≤ X) (hXD : X ≤ D^80) :
    (1+Real.log (X : ℝ))^1600 ≤ 81^1600 * lemma23PaperL D^1600 := by
  have hlog : Real.log (X : ℝ) ≤ 80 * lemma23PaperL D := by
    have h := Real.log_le_log (show 0 < (X : ℝ) by exact_mod_cast hX)
      (show (X : ℝ) ≤ (D : ℝ)^80 by exact_mod_cast hXD)
    simpa only [Real.log_pow,lemma23PaperL] using h
  have hbase : 1+Real.log (X : ℝ) ≤ 81*lemma23PaperL D := by linarith
  have hnonneg : 0 ≤ 1+Real.log (X : ℝ) := by
    have h := Real.log_nonneg (show 1 ≤ (X : ℝ) by exact_mod_cast hX)
    linarith
  simpa only [mul_pow] using pow_le_pow_left₀ hnonneg hbase 1600

lemma lemma34_uniform_centered_mean_square {D : ℕ} (hL : 3 ≤ lemma23PaperL D)
    (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ lemma23Tau40 n) (x : ℝ)
    (hx : 1 ≤ x) (hxD : x ≤ (D : ℝ)^80) :
    (∑ ψ ∈ lemma33ActualFamily D,
      ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, c n * ψ.2 (n : ZMod ψ.1.val) *
        Complex.exp (-lemma23PaperCenter D * (Real.log (n : ℝ) : ℂ))‖^2) ≤
      lemma33ActualPrimeMass D * (81^1600 * lemma23PaperL D^1600) := by
  have hX : 1 ≤ ⌊x⌋₊ := (Nat.one_le_floor_iff x).mpr hx
  have hXD : ⌊x⌋₊ ≤ D^80 := by
    exact_mod_cast (Nat.floor_le (show 0 ≤ x by linarith)).trans hxD
  calc
    _ ≤ lemma33ActualPrimeMass D * (1+Real.log (⌊x⌋₊ : ℝ))^1600 :=
      lemma34_centered_partial_sum_mean_square D ⌊x⌋₊ hX
        (hXD.trans (lemma34_cutoff_nat_le_floor_P hL)) c hc _ rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left (lemma34_coefficient_log_bound hL hX hXD)
      (Finset.sum_nonneg (fun _ _ => by positivity))

lemma lemma34_actual_x1_mean_square {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hL : 3 ≤ lemma23PaperL D) (x : ℝ) (hx : 1 ≤ x) (hxD : x ≤ (D : ℝ)^80) :
    (∑ ψ ∈ lemma33ActualFamily D,
      ‖lemma23ActualX1 χ ψ.2 (lemma23PaperCenter D) x‖^2) ≤
      lemma33ActualPrimeMass D * (81^1600 * lemma23PaperL D^1600) := by
  simpa only [lemma23ActualX1] using
    lemma34_uniform_centered_mean_square hL (lemma23Nu20Coefficient χ)
      (lemma23Nu20Coefficient_norm_le_tau40 χ) x hx hxD

lemma lemma34_actual_x2_mean_square {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hL : 3 ≤ lemma23PaperL D) (x : ℝ) (hx : 1 ≤ x) (hxD : x ≤ (D : ℝ)^80) :
    (∑ ψ ∈ lemma33ActualFamily D,
      ‖lemma23ActualX2 χ ψ.2 (lemma23PaperCenter D) x‖^2) ≤
      lemma33ActualPrimeMass D * (81^1600 * lemma23PaperL D^1600) := by
  simpa only [lemma23ActualX2] using
    lemma34_uniform_centered_mean_square hL (lemma23Upsilon20Coefficient χ)
      (lemma23Upsilon20Coefficient_norm_le_tau40 χ) x hx hxD

end ZhangLS.Spec
