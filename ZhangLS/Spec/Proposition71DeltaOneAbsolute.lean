import ZhangLS.Spec.TauWeightedDeltaCoefficients
import ZhangLS.Spec.Proposition71FrontLargeTail

/-! # Actual Δ₁ absolute bounds with all dilation and weight factors

This transports the independently proved absolute Δ sum through the exact
unit-modulus real phase. No principal or nonunit branch is removed.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex
set_option maxHeartbeats 2500000

noncomputable def proposition71DeltaOneDilatedTerm (D : ℕ) (κ w : ℕ → ℂ)
    (d : ℕ) (q : ℝ) (n : ℕ) : ℂ :=
  if 0<n then κ (d*n)*w n*lemma53PaperDeltaOne D ((n : ℝ)/q) else 0

lemma proposition71_delta_one_dilated_norm_bound (D : ℕ) (κ w : ℕ → ℂ)
    {W : ℝ} (hW : 0≤W) (hw : ∀n : ℕ, 0<n → ‖w n‖≤W) (d : ℕ) (q : ℝ) (n : ℕ) :
    ‖proposition71DeltaOneDilatedTerm D κ w d q n‖≤W*tauDeltaDilatedAbsolute D κ d q n := by
  unfold proposition71DeltaOneDilatedTerm tauDeltaDilatedAbsolute
  by_cases hn : 0<n
  · rw [if_pos hn,if_pos hn,norm_mul,norm_mul,proposition71_delta_one_norm_eq_delta]
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hw n hn) (norm_nonneg _))
      (norm_nonneg _)).trans_eq (by ring)
  · simp [hn]

/-- Absolute convergence and the actual q·L^575 bound, retaining τ₅(d) and W. -/
theorem proposition71_delta_one_dilated_absolute_bound {D : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) (κ w : ℕ → ℂ) {B W : ℝ} (hB : 0≤B) (hW : 0≤W)
    (hκ : ∀n : ℕ, 0<n → ‖κ n‖≤B*(lemma34Tau 5 n : ℝ))
    (hw : ∀n : ℕ, 0<n → ‖w n‖≤W) {d : ℕ} (hd : 0<d)
    {q : ℝ} (hq : 1≤q) (hqP : q≤lemma23PaperP D^10) :
    Summable (proposition71DeltaOneDilatedTerm D κ w d q) ∧
      (∑'n, ‖proposition71DeltaOneDilatedTerm D κ w d q n‖)≤
        W*tauDeltaAbsoluteConstant*B*(lemma34Tau 5 d : ℝ)*q*lemma23PaperL D^575 := by
  have ht := tauDelta_actual_dilated_absolute_sum hD hL κ hB hκ hd hq hqP
  have hmaj := ht.1.mul_left W
  have hnorm := Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (proposition71_delta_one_dilated_norm_bound D κ w hW hw d q) hmaj
  refine ⟨summable_norm_iff.mp hnorm,?_⟩
  have hb := hnorm.tsum_le_tsum (proposition71_delta_one_dilated_norm_bound D κ w hW hw d q) hmaj
  rw [tsum_mul_left] at hb
  exact hb.trans ((mul_le_mul_of_nonneg_left ht.2 hW).trans_eq (by ring))

end ZhangLS.Spec
