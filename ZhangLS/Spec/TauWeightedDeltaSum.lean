import ZhangLS.Spec.TauWeightedDeltaGeometry

/-! # The actual absolutely convergent τ₅-weighted Δ sum

The proof separates the literal finite head at qℒ^530 from the genuine
large-x Δ envelope. The q² tail factor is retained until its explicit
exponential absorption; no cancellation or mean-value estimate is assumed.
-/
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

lemma tauDelta_tau_five_square_summable :
    Summable (fun n:ℕ=>(lemma34Tau 5 n:ℝ)/(n:ℝ)^2) := by
  have ht := (lemma32_tau_lseries_summable 4 (2:ℂ) (by norm_num)).norm
  apply ht.congr
  intro n
  rw [LSeries.norm_term_eq]
  by_cases hn:n=0
  · subst n; simp
  · simp [hn]

lemma tauDelta_scaled_large_tail {D:ℕ} (hD:1<D) (hL:2000≤lemma23PaperL D)
    {q l:ℝ} (hq:0<q) (hl:q*lemma51PaperT0 D^(51/50:ℝ)<l) :
    ‖lemma53PaperDelta D (l/q)‖≤
      proposition71LargeDeltaTailConstant*Real.exp (-lemma23PaperL D^10/2)*q^2/l^2 := by
  have ht:0<lemma51PaperT0 D^(51/50:ℝ) := Real.rpow_pos_of_pos
    (pow_pos (by linarith : 0<lemma23PaperL D) _) _
  have hlp:0<l := (mul_pos hq ht).trans hl
  have hx : lemma51PaperT0 D^(51/50:ℝ)<l/q := (lt_div_iff₀ hq).mpr (by simpa only [mul_comm] using hl)
  apply (proposition71_actual_large_delta_tail hD hL hx).trans_eq
  rw [show (-2:ℝ)=-(2:ℝ) by norm_num,Real.rpow_neg (div_pos hlp hq).le,Real.rpow_two]
  field_simp

noncomputable def tauDeltaHead (D:ℕ) (q:ℝ) (n:ℕ) : ℝ :=
  if n∈Icc 1 ⌊q*lemma23PaperL D^530⌋₊ then tauDeltaUniformConstant*(lemma34Tau 5 n:ℝ) else 0

lemma tauDelta_head_hasSum (D:ℕ) (q:ℝ) :
    HasSum (tauDeltaHead D q)
      (tauDeltaUniformConstant*∑n∈Icc 1 ⌊q*lemma23PaperL D^530⌋₊,(lemma34Tau 5 n:ℝ)) := by
  have hh : HasSum (tauDeltaHead D q) (∑n∈Icc 1 ⌊q*lemma23PaperL D^530⌋₊,tauDeltaHead D q n) :=
    hasSum_sum_of_ne_finset_zero (s:=Icc 1 ⌊q*lemma23PaperL D^530⌋₊)
    (f:=tauDeltaHead D q) (fun n hn=>by simp only [tauDeltaHead,if_neg hn])
  simpa only [tauDeltaHead,sum_ite_mem,inter_self,mul_sum] using hh

lemma tauDelta_term_majorant {D:ℕ} (hD:1<D) (hL:2000≤lemma23PaperL D)
    {q:ℝ} (hq:1≤q) (n:ℕ) :
    (lemma34Tau 5 n:ℝ)*‖lemma53PaperDelta D ((n:ℝ)/q)‖ ≤
      tauDeltaHead D q n+
        (proposition71LargeDeltaTailConstant*Real.exp (-lemma23PaperL D^10/2)*q^2)*
          ((lemma34Tau 5 n:ℝ)/(n:ℝ)^2) := by
  have hqp:0<q := lt_of_lt_of_le zero_lt_one hq
  have hC := proposition71_large_delta_tail_constant_pos.le
  by_cases hn:n=0
  · subst n
    simp [lemma34Tau,tauDeltaHead]
  have hnp:0<(n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  by_cases hm:n∈Icc 1 ⌊q*lemma23PaperL D^530⌋₊
  · have hb := mul_le_mul_of_nonneg_left (tauDelta_actual_uniform_bound hD (by linarith) (div_pos hnp hqp))
      (Nat.cast_nonneg (lemma34Tau 5 n))
    rw [tauDeltaHead,if_pos hm]
    have hb' : (lemma34Tau 5 n:ℝ)*‖lemma53PaperDelta D ((n:ℝ)/q)‖≤tauDeltaUniformConstant*(lemma34Tau 5 n:ℝ) := by
      simpa only [mul_comm] using hb
    exact hb'.trans (le_add_of_nonneg_right (by positivity))
  · have hcut : q*lemma23PaperL D^530<(n:ℝ) := Nat.lt_of_floor_lt (by
      have hnpos : 1≤n := by omega
      have hh : ¬n≤⌊q*lemma23PaperL D^530⌋₊ := fun he=>hm (mem_Icc.mpr ⟨hnpos,he⟩)
      omega)
    have ht : q*lemma51PaperT0 D^(51/50:ℝ)<(n:ℝ) :=
      (mul_le_mul_of_nonneg_left (tauDelta_t0_cutoff (by linarith)) hqp.le).trans_lt hcut
    have hb := mul_le_mul_of_nonneg_left (tauDelta_scaled_large_tail hD hL hqp ht)
      (Nat.cast_nonneg (lemma34Tau 5 n))
    rw [tauDeltaHead,if_neg hm,zero_add]
    convert hb using 1; ring

/-- A complete literal sum bound before q² is simplified. -/
theorem tauDelta_actual_absolute_head_tail {D:ℕ} (hD:1<D) (hL:2000≤lemma23PaperL D)
    {q:ℝ} (hq:1≤q) :
    Summable (fun n:ℕ=>(lemma34Tau 5 n:ℝ)*‖lemma53PaperDelta D ((n:ℝ)/q)‖) ∧
      (∑'n:ℕ,(lemma34Tau 5 n:ℝ)*‖lemma53PaperDelta D ((n:ℝ)/q)‖) ≤
        tauDeltaUniformConstant*(⌊q*lemma23PaperL D^530⌋₊:ℝ)*
          (1+Real.log (⌊q*lemma23PaperL D^530⌋₊:ℝ))^5+
          243*proposition71LargeDeltaTailConstant*Real.exp (-lemma23PaperL D^10/2)*q^2 := by
  have hC := proposition71_large_delta_tail_constant_pos.le
  have hC0 := tauDelta_uniform_constant_pos.le
  let K := proposition71LargeDeltaTailConstant*Real.exp (-lemma23PaperL D^10/2)*q^2
  have hK : 0≤K := by dsimp [K]; positivity
  have hsH := (tauDelta_head_hasSum D q).summable
  have hsT := tauDelta_tau_five_square_summable.mul_left K
  have hs : Summable (fun n:ℕ=>(lemma34Tau 5 n:ℝ)*‖lemma53PaperDelta D ((n:ℝ)/q)‖) :=
    (hsH.add hsT).of_nonneg_of_le (fun _=>by positivity) (tauDelta_term_majorant hD hL hq)
  refine ⟨hs,?_⟩
  have hb := hs.tsum_le_tsum (tauDelta_term_majorant hD hL hq) (hsH.add hsT)
  rw [hsH.tsum_add hsT,(tauDelta_head_hasSum D q).tsum_eq,tsum_mul_left] at hb
  have hL1 : 1≤lemma23PaperL D := by linarith
  have hU : 1≤q*lemma23PaperL D^530 := by
    have hh : 1≤lemma23PaperL D^530 := one_le_pow₀ hL1
    have hm := mul_le_mul_of_nonneg_right hq (pow_nonneg (by linarith : 0≤lemma23PaperL D) 530)
    simp only [one_mul] at hm
    exact hh.trans hm
  have hX : 1≤⌊q*lemma23PaperL D^530⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using hU)
  apply hb.trans
  have hh := mul_le_mul_of_nonneg_left (tauDelta_tau_five_partial_sum _ hX) hC0
  have ht := mul_le_mul_of_nonneg_left tauDirichlet_five_square_mass_le hK
  have hz := add_le_add hh ht
  convert hz using 1; dsimp [K]; ring

noncomputable def tauDeltaAbsoluteConstant : ℝ :=
  12^5*tauDeltaUniformConstant+243*proposition71LargeDeltaTailConstant

lemma tauDelta_absolute_constant_pos : 0<tauDeltaAbsoluteConstant := by
  unfold tauDeltaAbsoluteConstant
  have := tauDelta_uniform_constant_pos
  have := proposition71_large_delta_tail_constant_pos
  positivity

/-- Shared genuine absolute Δ bound at the full useful range of scales. -/
theorem tauDelta_actual_absolute_sum {D:ℕ} (hD:1<D) (hL:2000≤lemma23PaperL D)
    {q:ℝ} (hq:1≤q) (hqP:q≤lemma23PaperP D^10) :
    Summable (fun n:ℕ=>(lemma34Tau 5 n:ℝ)*‖lemma53PaperDelta D ((n:ℝ)/q)‖) ∧
      (∑'n:ℕ,(lemma34Tau 5 n:ℝ)*‖lemma53PaperDelta D ((n:ℝ)/q)‖) ≤
        tauDeltaAbsoluteConstant*q*lemma23PaperL D^575 := by
  have hb := tauDelta_actual_absolute_head_tail hD hL hq
  refine ⟨hb.1,hb.2.trans ?_⟩
  have hh := mul_le_mul_of_nonneg_left (tauDelta_head_geometry hL hq hqP).2 tauDelta_uniform_constant_pos.le
  have ht := mul_le_mul_of_nonneg_left (tauDelta_tail_scale hL (by linarith) hqP)
    (show 0≤243*proposition71LargeDeltaTailConstant by have := proposition71_large_delta_tail_constant_pos; positivity)
  have hL575 : 1≤lemma23PaperL D^575 := one_le_pow₀ (by linarith : 1≤lemma23PaperL D)
  have htail : 243*proposition71LargeDeltaTailConstant*Real.exp (-lemma23PaperL D^10/2)*q^2≤
      243*proposition71LargeDeltaTailConstant*q*lemma23PaperL D^575 := by
    have ht' : 243*proposition71LargeDeltaTailConstant*Real.exp (-lemma23PaperL D^10/2)*q^2≤243*proposition71LargeDeltaTailConstant*q := by
      convert ht using 1; ring
    apply ht'.trans
    exact le_mul_of_one_le_right (by have := proposition71_large_delta_tail_constant_pos; positivity) hL575
  have hs := add_le_add hh htail
  unfold tauDeltaAbsoluteConstant
  convert hs using 1 <;> ring

end ZhangLS.Spec
