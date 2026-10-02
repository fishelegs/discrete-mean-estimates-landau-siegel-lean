import ZhangLS.Spec.Proposition71FrontUniformRate
import ZhangLS.Spec.Proposition71DeltaLargeTail
import ZhangLS.Spec.Proposition71TauDirichlet

/-! # The literal large-long-index Δ₁ tail for the common front end

The geometric condition on qn is explicit. It is a support/scale inequality,
not a cancellation or averaged hypothesis. Both Section7 and Section14 must
prove it for their own original strict/closed short support.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Finset
open scoped Classical
set_option maxHeartbeats 3500000

lemma proposition71_delta_one_norm_eq_delta (D : ℕ) (x : ℝ) :
    ‖lemma53PaperDeltaOne D x‖=‖lemma53PaperDelta D x‖ := by
  unfold lemma53PaperDelta
  rw [norm_mul,Complex.norm_exp]
  have he : ((2*Real.pi : ℂ)*I*(x : ℂ)).re=0 := by simp
  rw [he,Real.exp_zero,mul_one]

noncomputable def proposition71ShortLinearMass (S : Finset ℕ) (a : ℕ → ℂ) : ℝ :=
  ∑n∈S, ‖a n‖*(n : ℝ)

lemma proposition71_short_linear_mass_nonneg (S : Finset ℕ) (a : ℕ → ℂ) :
    0≤proposition71ShortLinearMass S a := sum_nonneg (fun n hn => by positivity)

lemma proposition71_delta_one_scaled_tail {D : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) {q : ℝ} (hq : 0<q) {m n : ℕ}
    (hm : 0<m) (hn : 0<n) (a : ℂ)
    (hgap : (q*(n : ℝ))*lemma51PaperT0 D^(51/50 : ℝ)<(m : ℝ)) :
    ‖(a/(n : ℂ))*lemma53PaperDeltaOne D ((m : ℝ)/(q*(n : ℝ)))‖≤
      (proposition71LargeDeltaTailConstant*Real.exp (-lemma23PaperL D^10/2)*q^2/(m : ℝ)^2)*
        (‖a‖*(n : ℝ)) := by
  have hmp : 0<(m : ℝ) := by exact_mod_cast hm
  have hnp : 0<(n : ℝ) := by exact_mod_cast hn
  have hx : lemma51PaperT0 D^(51/50 : ℝ)<(m : ℝ)/(q*(n : ℝ)) :=
    (lt_div_iff₀ (mul_pos hq hnp)).mpr (by simpa only [mul_comm] using hgap)
  have hb := proposition71_actual_large_delta_tail hD hL hx
  rw [norm_mul,norm_div,Complex.norm_natCast,proposition71_delta_one_norm_eq_delta]
  apply (mul_le_mul_of_nonneg_left hb (div_nonneg (norm_nonneg _) hnp.le)).trans_eq
  rw [Real.rpow_neg (div_nonneg hmp.le (mul_nonneg hq.le hnp.le)),Real.rpow_two,div_pow,inv_div]
  field_simp

/-- Pointwise actual tail majorant, with the full q² and short linear mass. -/
lemma proposition71_front_large_tail_term_bound {D : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) {q B : ℝ} (hq : 0<q) (hB : 0≤B)
    (c : ℕ → ℂ) (hc : ∀m, 0<m → ‖c m‖≤B*(lemma34Tau 5 m : ℝ))
    (htail : ∀m : ℕ, (m : ℝ)<lemma23PaperP D^2 → c m=0)
    (S : Finset ℕ) (hS : ∀n∈S, 0<n) (a : ℕ → ℂ)
    (hgap : ∀n∈S, (q*(n : ℝ))*lemma51PaperT0 D^(51/50 : ℝ)<lemma23PaperP D^2)
    (m : ℕ) :
    ‖proposition71DeltaOneDoubleTerm D c S a q m‖≤
      (proposition71LargeDeltaTailConstant*Real.exp (-lemma23PaperL D^10/2)*q^2*B*
        proposition71ShortLinearMass S a)*((lemma34Tau 5 m : ℝ)/(m : ℝ)^2) := by
  have hC := proposition71_large_delta_tail_constant_pos.le
  have hM := proposition71_short_linear_mass_nonneg S a
  by_cases hm : m=0
  · subst m; simp [proposition71DeltaOneDoubleTerm]
  by_cases hmP : (m : ℝ)<lemma23PaperP D^2
  · simp only [proposition71DeltaOneDoubleTerm,if_neg hm,htail m hmP,zero_mul,norm_zero]
    positivity
  have hmp : 0<m := Nat.pos_of_ne_zero hm
  have hmr : 0<(m : ℝ) := by exact_mod_cast hmp
  have hP : lemma23PaperP D^2≤(m : ℝ) := le_of_not_gt hmP
  have hinner : ‖∑n∈S, (a n/(n : ℂ))*lemma53PaperDeltaOne D ((m : ℝ)/(q*(n : ℝ)))‖≤
      (proposition71LargeDeltaTailConstant*Real.exp (-lemma23PaperL D^10/2)*q^2/(m : ℝ)^2)*
        proposition71ShortLinearMass S a := by
    apply (norm_sum_le _ _).trans
    rw [proposition71ShortLinearMass,mul_sum]
    apply sum_le_sum
    intro n hn
    exact proposition71_delta_one_scaled_tail hD hL hq hmp (hS n hn) (a n)
      ((hgap n hn).trans_le hP)
  rw [proposition71DeltaOneDoubleTerm,if_neg hm,norm_mul]
  exact (mul_le_mul (hc m hmp) hinner (norm_nonneg _) (by positivity)).trans_eq (by ring)

/-- Absolute convergence and a norm bound for the literal infinite long tail.
The factor q² is not discarded; the next scalar budget pays for it. -/
theorem proposition71_front_large_tail_tsum_bound {D : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) {q B : ℝ} (hq : 0<q) (hB : 0≤B)
    (c : ℕ → ℂ) (hc : ∀m, 0<m → ‖c m‖≤B*(lemma34Tau 5 m : ℝ))
    (htail : ∀m : ℕ, (m : ℝ)<lemma23PaperP D^2 → c m=0)
    (S : Finset ℕ) (hS : ∀n∈S, 0<n) (a : ℕ → ℂ)
    (hgap : ∀n∈S, (q*(n : ℝ))*lemma51PaperT0 D^(51/50 : ℝ)<lemma23PaperP D^2) :
    Summable (proposition71DeltaOneDoubleTerm D c S a q) ∧
      ‖∑' m, proposition71DeltaOneDoubleTerm D c S a q m‖≤
        (proposition71LargeDeltaTailConstant*Real.exp (-lemma23PaperL D^10/2)*q^2*B*
          proposition71ShortLinearMass S a)*proposition71TauFiveQuadraticMass := by
  have hC := proposition71_large_delta_tail_constant_pos.le
  have hM := proposition71_short_linear_mass_nonneg S a
  have hK : 0≤proposition71LargeDeltaTailConstant*Real.exp (-lemma23PaperL D^10/2)*q^2*B*
      proposition71ShortLinearMass S a := by positivity
  have hb := proposition71_front_large_tail_term_bound hD hL hq hB c hc htail S hS a hgap
  exact ⟨proposition71_tau_dominated_series_summable hK hb,proposition71_tau_dominated_tsum_bound hK hb⟩

end ZhangLS.Spec
