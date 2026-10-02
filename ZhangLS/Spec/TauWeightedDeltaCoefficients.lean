import ZhangLS.Spec.TauWeightedDeltaSum

/-! # Arbitrary τ₅-bounded coefficients in the actual absolute Δ sum

The positive-index convention leaves κ(0) unconstrained, as in the source.
All dilation divisor factors are retained. A bounded complex weight can
therefore include a genuine Dirichlet character without changing the bound.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex

noncomputable def tauDeltaDilatedAbsolute (D:ℕ) (κ:ℕ→ℂ) (d:ℕ) (q:ℝ) (n:ℕ) : ℝ :=
  if 0<n then ‖κ (d*n)‖*‖lemma53PaperDelta D ((n:ℝ)/q)‖ else 0

noncomputable def tauDeltaDilatedTerm (D:ℕ) (κ w:ℕ→ℂ) (d:ℕ) (q:ℝ) (n:ℕ) : ℂ :=
  if 0<n then κ (d*n)*w n*lemma53PaperDelta D ((n:ℝ)/q) else 0

lemma tauDelta_dilated_absolute_majorant (D:ℕ) (κ:ℕ→ℂ) {B:ℝ} (hB:0≤B)
    (hκ:∀n:ℕ,0<n→‖κ n‖≤B*(lemma34Tau 5 n:ℝ)) {d:ℕ} (hd:0<d) (q:ℝ) (n:ℕ) :
    tauDeltaDilatedAbsolute D κ d q n≤
      (B*(lemma34Tau 5 d:ℝ))*((lemma34Tau 5 n:ℝ)*‖lemma53PaperDelta D ((n:ℝ)/q)‖) := by
  unfold tauDeltaDilatedAbsolute
  split_ifs with hn
  · have hs : (lemma34Tau 5 (d*n):ℝ)≤(lemma34Tau 5 d:ℝ)*(lemma34Tau 5 n:ℝ) := by
      exact_mod_cast proposition71_tau_submultiplicative 5 d n
    have hb := (hκ (d*n) (Nat.mul_pos hd hn)).trans (mul_le_mul_of_nonneg_left hs hB)
    have hz := mul_le_mul_of_nonneg_right hb (norm_nonneg (lemma53PaperDelta D ((n:ℝ)/q)))
    simpa only [mul_assoc] using hz
  · positivity

theorem tauDelta_actual_dilated_absolute_sum {D:ℕ} (hD:1<D) (hL:2000≤lemma23PaperL D)
    (κ:ℕ→ℂ) {B:ℝ} (hB:0≤B) (hκ:∀n:ℕ,0<n→‖κ n‖≤B*(lemma34Tau 5 n:ℝ))
    {d:ℕ} (hd:0<d) {q:ℝ} (hq:1≤q) (hqP:q≤lemma23PaperP D^10) :
    Summable (tauDeltaDilatedAbsolute D κ d q) ∧
      (∑'n:ℕ,tauDeltaDilatedAbsolute D κ d q n)≤
        tauDeltaAbsoluteConstant*B*(lemma34Tau 5 d:ℝ)*q*lemma23PaperL D^575 := by
  have ht := tauDelta_actual_absolute_sum hD hL hq hqP
  have hsT := ht.1.mul_left (B*(lemma34Tau 5 d:ℝ))
  have hs : Summable (tauDeltaDilatedAbsolute D κ d q) := hsT.of_nonneg_of_le
    (fun n=>by unfold tauDeltaDilatedAbsolute; split_ifs <;> positivity)
    (tauDelta_dilated_absolute_majorant D κ hB hκ hd q)
  refine ⟨hs,?_⟩
  have hb := hs.tsum_le_tsum (tauDelta_dilated_absolute_majorant D κ hB hκ hd q) hsT
  rw [tsum_mul_left] at hb
  apply hb.trans
  have hh := mul_le_mul_of_nonneg_left ht.2 (show 0≤B*(lemma34Tau 5 d:ℝ) by positivity)
  convert hh using 1; ring

lemma tauDelta_dilated_term_norm_le (D:ℕ) (κ w:ℕ→ℂ)
    (hw:∀n:ℕ,0<n→‖w n‖≤1) (d:ℕ) (q:ℝ) (n:ℕ) :
    ‖tauDeltaDilatedTerm D κ w d q n‖≤tauDeltaDilatedAbsolute D κ d q n := by
  unfold tauDeltaDilatedTerm tauDeltaDilatedAbsolute
  split_ifs with hn
  · rw [norm_mul,norm_mul]
    have hh := mul_le_mul_of_nonneg_left (hw n hn) (norm_nonneg (κ (d*n)))
    exact mul_le_mul_of_nonneg_right (by simpa only [mul_one] using hh) (norm_nonneg _)
  · simp only [norm_zero,le_refl]

theorem tauDelta_actual_dilated_character_sum {D:ℕ} (hD:1<D) (hL:2000≤lemma23PaperL D)
    (κ w:ℕ→ℂ) {B:ℝ} (hB:0≤B) (hκ:∀n:ℕ,0<n→‖κ n‖≤B*(lemma34Tau 5 n:ℝ))
    (hw:∀n:ℕ,0<n→‖w n‖≤1) {d:ℕ} (hd:0<d) {q:ℝ} (hq:1≤q) (hqP:q≤lemma23PaperP D^10) :
    Summable (tauDeltaDilatedTerm D κ w d q) ∧
      ‖∑'n:ℕ,tauDeltaDilatedTerm D κ w d q n‖≤
        tauDeltaAbsoluteConstant*B*(lemma34Tau 5 d:ℝ)*q*lemma23PaperL D^575 := by
  have ht := tauDelta_actual_dilated_absolute_sum hD hL κ hB hκ hd hq hqP
  have hs : Summable (tauDeltaDilatedTerm D κ w d q) :=
    Summable.of_norm_bounded ht.1 (tauDelta_dilated_term_norm_le D κ w hw d q)
  refine ⟨hs,?_⟩
  exact (norm_tsum_le_tsum_norm hs.norm).trans
    ((hs.norm.tsum_le_tsum (tauDelta_dilated_term_norm_le D κ w hw d q) ht.1).trans ht.2)

end ZhangLS.Spec
