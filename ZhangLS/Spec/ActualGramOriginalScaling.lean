import ZhangLS.Spec.ActualGramLogKernelBridge

/-! Exact original log scales and moving T bands. The fixed smoothing density
for mu=6 is genuinely independent of D, and every intermediate real cutoff
is tracked through its actual logarithmic endpoint. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace ZhangLS.Spec
open Complex
open scoped Classical

lemma actualGram_original_log_scale (D : ℕ) :
    Real.log (lemma23PaperP D)=lemma23PaperL D^9 := by
  simp [lemma23PaperP]

lemma actualGram_original_log_scale_pos {D : ℕ} (hD : 1<D) :
    0<Real.log (lemma23PaperP D) := by
  rw [actualGram_original_log_scale]
  apply pow_pos
  exact Real.log_pos (by exact_mod_cast hD)

/-- Exact ell=3*pi*i/2, without an asymptotic replacement of the shift. -/
theorem actualGram_original_mu6_scaled {D : ℕ} (hD : 1<D) :
    (Real.log (lemma23PaperP D) : ℂ)*lemma82SmoothingBeta D 6 =
      3*I*(Real.pi : ℂ)/2 := by
  have hB : (Real.log (lemma23PaperP D) : ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (actualGram_original_log_scale_pos hD).ne'
  simp only [lemma82SmoothingBeta,if_pos rfl,lemma44PaperAlpha]
  push_cast
  field_simp [hB] <;> ring

/-- The opposite shift in the actual xi kernel gives the conjugate density. -/
theorem actualGram_original_mu6_negative_scaled {D : ℕ} (hD : 1<D) :
    (Real.log (lemma23PaperP D) : ℂ)*(-lemma84SmoothingBeta D 6) =
      -(3*I*(Real.pi : ℂ)/2) := by
  have he : lemma84SmoothingBeta D 6=lemma82SmoothingBeta D 6 := rfl
  rw [he,mul_neg,actualGram_original_mu6_scaled hD]

lemma actualGram_original_exp_power (D : ℕ) (v : ℝ) :
    Real.exp (Real.log (lemma23PaperP D)*v)=(lemma23PaperP D)^v := by
  rw [Real.rpow_def_of_pos (show 0 < lemma23PaperP D from Real.exp_pos _)]

/-- Exact closed moving boundary band for arbitrary positive real q and T.
This identity pays all intermediate cutoffs introduced by superposition. -/
theorem actualGram_log_moving_band {B q T : ℝ} (hB : 0<B) (hq : 0<q) (hT : 0<T)
    (v : ℝ) :
    (1≤Real.exp (B*v)/q ∧ Real.exp (B*v)/q≤T) ↔
      (Real.log q/B≤v ∧ v≤Real.log q/B+Real.log T/B) := by
  have hx : 0<Real.exp (B*v)/q := by positivity
  have hlog : Real.log (Real.exp (B*v)/q)=B*v-Real.log q := by
    rw [Real.log_div (Real.exp_ne_zero _) hq.ne',Real.log_exp]
  have hlo : 1≤Real.exp (B*v)/q ↔ Real.log q/B≤v := by
    rw [← Real.log_le_log_iff zero_lt_one hx,Real.log_one,hlog,div_le_iff₀ hB]
    constructor <;> intro h <;> nlinarith
  have hhi : Real.exp (B*v)/q≤T ↔ v≤Real.log q/B+Real.log T/B := by
    rw [← Real.log_le_log_iff hx hT,hlog,← add_div,le_div_iff₀ hB]
    constructor <;> intro h <;> nlinarith
  exact and_congr hlo hhi

/-- The actual T layer has width L^(11/10)/log P, including both endpoints. -/
theorem actualGram_original_moving_T_band {D : ℕ} (hD : 1<D) {q : ℝ} (hq : 0<q)
    (v : ℝ) :
    (1≤(lemma23PaperP D)^v/q ∧ (lemma23PaperP D)^v/q≤lemma56PaperT D) ↔
      (Real.log q/Real.log (lemma23PaperP D)≤v ∧
       v≤Real.log q/Real.log (lemma23PaperP D)+
         lemma23PaperL D^(11/10 : ℝ)/Real.log (lemma23PaperP D)) := by
  have h := actualGram_log_moving_band (actualGram_original_log_scale_pos hD) hq
    (show 0<lemma56PaperT D from Real.exp_pos _) v
  rw [actualGram_original_exp_power,lemma56PaperT,Real.log_exp] at h
  exact h

end ZhangLS.Spec
