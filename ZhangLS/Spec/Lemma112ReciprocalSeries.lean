import ZhangLS.Spec.Lemma112WideZBounds
/-! # Genuine short-polynomial / reciprocal-tail decomposition at P₁ -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Real Topology

noncomputable def lemma112ReciprocalTailTerm {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ) (n : ℕ) : ℂ :=
  if lemma112PaperP1 D ≤ (n : ℝ) then LSeries.term (lemma112Coefficient χ ψ) s n else 0

lemma lemma112_reciprocal_tail_summable {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) {s : ℂ} (hs : 1 < s.re) :
    Summable (lemma112ReciprocalTailTerm χ ψ s) := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  have hb := summable_norm_iff.mpr
    (DirichletCharacter.LSeriesSummable_of_one_lt_re (lemma44CharacterTwist χ ψ) hs)
  rw [← lemma112_coefficient_eq_twist] at hb
  apply summable_norm_iff.mp
  exact hb.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => by
    unfold lemma112ReciprocalTailTerm
    split_ifs <;> simp)

lemma lemma112_actual_reciprocal_series_split {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) {s : ℂ} (hs : 1 < s.re) :
    letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) s =
      lemma112ShortPolynomial χ ψ s + ∑' n : ℕ, lemma112ReciprocalTailTerm χ ψ s n := by
  classical
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  let c := lemma112Coefficient χ ψ
  let f : ℕ → ℂ := LSeries.term c s
  let S := (Finset.Icc 1 ⌈lemma112PaperP1 D⌉₊).filter
    (fun n : ℕ => (n : ℝ) < lemma112PaperP1 D)
  let short : ℕ → ℂ := fun n => if n ∈ S then f n else 0
  have hshort : Summable short := summable_of_ne_finset_zero (s := S)
    (fun n hn => by simp [short, hn])
  have htail := lemma112_reciprocal_tail_summable χ ψ hs
  have hmem (n : ℕ) (hn : n ≠ 0) : n ∈ S ↔ (n : ℝ) < lemma112PaperP1 D := by
    dsimp [S]
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · exact fun h => h.2
    · intro h
      have hc : n ≤ ⌈lemma112PaperP1 D⌉₊ := by
        exact_mod_cast h.le.trans (Nat.le_ceil (lemma112PaperP1 D))
      exact ⟨⟨Nat.one_le_iff_ne_zero.mpr hn, hc⟩, h⟩
  have hp (n : ℕ) : f n = short n + lemma112ReciprocalTailTerm χ ψ s n := by
    by_cases hn : n = 0
    · simp [f, short, hn, lemma112ReciprocalTailTerm]
    · by_cases hlt : (n : ℝ) < lemma112PaperP1 D
      · simp [short, (hmem n hn).mpr hlt, lemma112ReciprocalTailTerm, not_le.mpr hlt, f, c]
      · simp [short, show n ∉ S from fun h => hlt ((hmem n hn).mp h),
          lemma112ReciprocalTailTerm, le_of_not_gt hlt, f, c]
  have he : (∑' n : ℕ, short n) = lemma112ShortPolynomial χ ψ s := by
    rw [tsum_eq_sum (s := S) (fun n hn => by simp [short, hn])]
    unfold lemma112ShortPolynomial
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : n ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (by norm_num)
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1)
    simp only [short, if_pos hn, f, c]
    exact lemma44_LSeries_term_eq_exp _ _ hn0
  rw [DirichletCharacter.LFunction_eq_LSeries _ hs]
  change (∑' n : ℕ, LSeries.term _ s n) = _
  rw [← lemma112_coefficient_eq_twist]
  change (∑' n : ℕ, f n) = _
  simp_rw [hp]
  rw [hshort.tsum_add htail, he]

lemma lemma112_P1_log (D : ℕ) :
    Real.log (lemma112PaperP1 D) = (63 / 125 : ℝ) * lemma23PaperL D ^ 9 := by
  rw [lemma112PaperP1, lemma23PaperP, Real.log_rpow (Real.exp_pos _), Real.log_exp]

lemma lemma112_reciprocal_horizontal_term_bound {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : 1 < D) (hL : 64 ≤ lemma23PaperL D) {s w : ℂ}
    (hs : s.re = 1 / 2) (hw : w.re ≤ -1) {z : ℝ} (hz : 1 / 2 ≤ z) (n : ℕ) :
    ‖lemma112ReciprocalTailTerm χ ψ (1 - s - w) n‖ *
      Real.exp (-w.re * Real.log (lemma112DualScale D z)) ≤
        (n : ℝ) ^ (-5 / 4 : ℝ) * Real.exp (lemma23PaperL D ^ 9) := by
  by_cases hn0 : n = 0
  · simp [hn0, lemma112ReciprocalTailTerm]
  by_cases hcut : lemma112PaperP1 D ≤ (n : ℝ)
  swap
  · simp only [lemma112ReciprocalTailTerm, if_neg hcut, norm_zero, zero_mul]
    positivity
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hlog : Real.log (lemma112PaperP1 D) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (Real.rpow_pos_of_pos (Real.exp_pos _) _) hcut
  have hgap := (lemma112_dual_scale_cutoff_gap hD hL hz).2
  have hpow : 0 ≤ lemma23PaperL D ^ 9 := by positivity
  have hQpos : 0 ≤ Real.log (lemma112PaperP1 D) := by rw [lemma112_P1_log]; positivity
  have hgap0 : 0 ≤ Real.log (lemma112PaperP1 D) - Real.log (lemma112DualScale D z) := by
    linarith only [hgap, hpow]
  have ha := mul_le_mul_of_nonpos_left hlog (by linarith only [hw] : w.re + 3 / 4 ≤ 0)
  have hb := mul_nonpos_of_nonpos_of_nonneg (show w.re ≤ 0 by linarith only [hw]) hgap0
  have hpe : (w.re - 1 / 2) * Real.log (n : ℝ) - w.re * Real.log (lemma112DualScale D z) ≤
      (-5 / 4 : ℝ) * Real.log (n : ℝ) + lemma23PaperL D ^ 9 := by
    rw [lemma112_P1_log] at ha hb
    nlinarith only [ha, hb, hpow]
  unfold lemma112ReciprocalTailTerm
  rw [if_pos hcut, lemma44_norm_LSeries_term_eq_real_exp _ _ hn0,
    show -(1 - s - w).re = w.re - 1 / 2 by simp only [sub_re, one_re, hs]; ring,
    Real.rpow_def_of_pos hn]
  calc
    _ ≤ Real.exp ((w.re - 1 / 2) * Real.log (n : ℝ)) *
        Real.exp (-w.re * Real.log (lemma112DualScale D z)) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (lemma112_coefficient_norm_le_one χ ψ n) (Real.exp_nonneg _))
        (Real.exp_nonneg _)
    _ ≤ _ := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith only [hpe]

lemma lemma112_reciprocal_horizontal_sum_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : 1 < D) (hL : 64 ≤ lemma23PaperL D) {s w : ℂ}
    (hs : s.re = 1 / 2) (hw : w.re ≤ -1) {z : ℝ} (hz : 1 / 2 ≤ z) :
    ‖∑' n : ℕ, lemma112ReciprocalTailTerm χ ψ (1 - s - w) n‖ *
      Real.exp (-w.re * Real.log (lemma112DualScale D z)) ≤
        lemma61QuarterSeriesMass * Real.exp (lemma23PaperL D ^ 9) := by
  have ht : 1 < (1 - s - w).re := by simp only [sub_re, one_re, hs]; linarith only [hw]
  have hnorm := summable_norm_iff.mpr (lemma112_reciprocal_tail_summable χ ψ ht)
  have hscaled := hnorm.mul_right (Real.exp (-w.re * Real.log (lemma112DualScale D z)))
  have hmajor := lemma61_quarter_series_summable.mul_right (Real.exp (lemma23PaperL D ^ 9))
  calc
    _ ≤ (∑' n : ℕ, ‖lemma112ReciprocalTailTerm χ ψ (1 - s - w) n‖) *
        Real.exp (-w.re * Real.log (lemma112DualScale D z)) :=
      mul_le_mul_of_nonneg_right (norm_tsum_le_tsum_norm hnorm) (Real.exp_nonneg _)
    _ = ∑' n : ℕ, ‖lemma112ReciprocalTailTerm χ ψ (1 - s - w) n‖ *
        Real.exp (-w.re * Real.log (lemma112DualScale D z)) := (tsum_mul_right).symm
    _ ≤ ∑' n : ℕ, (n : ℝ) ^ (-5 / 4 : ℝ) * Real.exp (lemma23PaperL D ^ 9) :=
      hscaled.tsum_le_tsum (lemma112_reciprocal_horizontal_term_bound χ ψ hD hL hs hw hz) hmajor
    _ = _ := by rw [tsum_mul_right]; rfl

lemma lemma112_reciprocal_far_left_term_bound {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : 1 < D) (hL : 64 ≤ lemma23PaperL D) {s w : ℂ}
    (hs : s.re = 1 / 2) (hw : w.re = -(lemma23PaperL D ^ 9))
    {z : ℝ} (hz : 1 / 2 ≤ z) (n : ℕ) :
    ‖lemma112ReciprocalTailTerm χ ψ (1 - s - w) n‖ *
      Real.exp (-w.re * Real.log (lemma112DualScale D z)) ≤
        ((n : ℝ) ^ 2)⁻¹ * Real.exp (-(lemma23PaperL D ^ 10) / 2) := by
  by_cases hn0 : n = 0
  · simp [hn0, lemma112ReciprocalTailTerm]
  by_cases hcut : lemma112PaperP1 D ≤ (n : ℝ)
  swap
  · simp only [lemma112ReciprocalTailTerm, if_neg hcut, norm_zero, zero_mul]
    positivity
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hlog : Real.log (lemma112PaperP1 D) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (Real.rpow_pos_of_pos (Real.exp_pos _) _) hcut
  have h0 : 0 < lemma23PaperL D := by linarith
  have h1 : 1 ≤ lemma23PaperL D := by linarith
  have h9 : 64 ≤ lemma23PaperL D ^ 9 := hL.trans (le_self_pow₀ h1 (by norm_num))
  have h8 : (2000 : ℝ) ≤ lemma23PaperL D ^ 8 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 64) hL 8
    norm_num at h
    linarith only [h]
  have h18 : 2000 * lemma23PaperL D ^ 10 ≤ lemma23PaperL D ^ 18 := by
    convert mul_le_mul_of_nonneg_right h8 (pow_nonneg h0.le 10) using 1 <;> ring
  have h910 : lemma23PaperL D ^ 9 ≤ lemma23PaperL D ^ 10 := pow_le_pow_right₀ h1 (by norm_num)
  have hgap := (lemma112_dual_scale_cutoff_gap hD hL hz).2
  have ha := mul_le_mul_of_nonpos_left hlog (show w.re + 3 / 2 ≤ 0 by rw [hw]; linarith only [h9])
  have hb := mul_le_mul_of_nonpos_left hgap (show w.re ≤ 0 by rw [hw]; linarith only [h9])
  have hpe : (w.re - 1 / 2) * Real.log (n : ℝ) - w.re * Real.log (lemma112DualScale D z) ≤
      -2 * Real.log (n : ℝ) - lemma23PaperL D ^ 10 / 2 := by
    simp only [hw, lemma112_P1_log] at ha hb ⊢
    have hid : lemma23PaperL D ^ 9 * lemma23PaperL D ^ 9 = lemma23PaperL D ^ 18 := by ring
    nlinarith only [ha, hb, h18, h910, hid, pow_nonneg h0.le 10]
  have hnexp : ((n : ℝ) ^ 2)⁻¹ = Real.exp (-2 * Real.log (n : ℝ)) := by
    rw [show -2 * Real.log (n : ℝ) = -(2 * Real.log (n : ℝ)) by ring, Real.exp_neg,
      show 2 * Real.log (n : ℝ) = Real.log ((n : ℝ) ^ 2) by rw [Real.log_pow]; norm_num,
      Real.exp_log (pow_pos hn 2)]
  unfold lemma112ReciprocalTailTerm
  rw [if_pos hcut, lemma44_norm_LSeries_term_eq_real_exp _ _ hn0,
    show -(1 - s - w).re = w.re - 1 / 2 by simp only [sub_re, one_re, hs]; ring]
  calc
    _ ≤ Real.exp ((w.re - 1 / 2) * Real.log (n : ℝ)) *
        Real.exp (-w.re * Real.log (lemma112DualScale D z)) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (lemma112_coefficient_norm_le_one χ ψ n) (Real.exp_nonneg _))
        (Real.exp_nonneg _)
    _ ≤ _ := by
      rw [hnexp, ← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith only [hpe]

lemma lemma112_reciprocal_far_left_sum_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : 1 < D) (hL : 64 ≤ lemma23PaperL D) {s w : ℂ}
    (hs : s.re = 1 / 2) (hw : w.re = -(lemma23PaperL D ^ 9))
    {z : ℝ} (hz : 1 / 2 ≤ z) :
    ‖∑' n : ℕ, lemma112ReciprocalTailTerm χ ψ (1 - s - w) n‖ *
      Real.exp (-w.re * Real.log (lemma112DualScale D z)) ≤
        lemma44InverseSquareMass * Real.exp (-(lemma23PaperL D ^ 10) / 2) := by
  have h9 : 64 ≤ lemma23PaperL D ^ 9 := hL.trans (le_self_pow₀ (by linarith) (by norm_num))
  have ht : 1 < (1 - s - w).re := by
    simp only [sub_re, one_re, hs, hw]
    linarith only [h9]
  have hnorm := summable_norm_iff.mpr (lemma112_reciprocal_tail_summable χ ψ ht)
  have hscaled := hnorm.mul_right (Real.exp (-w.re * Real.log (lemma112DualScale D z)))
  have hmajor := lemma44_inverse_square_summable.mul_right (Real.exp (-(lemma23PaperL D ^ 10) / 2))
  calc
    _ ≤ (∑' n : ℕ, ‖lemma112ReciprocalTailTerm χ ψ (1 - s - w) n‖) *
        Real.exp (-w.re * Real.log (lemma112DualScale D z)) :=
      mul_le_mul_of_nonneg_right (norm_tsum_le_tsum_norm hnorm) (Real.exp_nonneg _)
    _ = ∑' n : ℕ, ‖lemma112ReciprocalTailTerm χ ψ (1 - s - w) n‖ *
        Real.exp (-w.re * Real.log (lemma112DualScale D z)) := (tsum_mul_right).symm
    _ ≤ ∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹ * Real.exp (-(lemma23PaperL D ^ 10) / 2) :=
      hscaled.tsum_le_tsum (lemma112_reciprocal_far_left_term_bound χ ψ hD hL hs hw hz) hmajor
    _ = _ := by rw [tsum_mul_right]; rfl

noncomputable def lemma112ActualReciprocalTailIntegrand {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ) (z : ℝ) (w : ℂ) : ℂ :=
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  lemma23DirichletZ (lemma44CharacterTwist χ ψ) (s + w) *
    (∑' n : ℕ, lemma112ReciprocalTailTerm χ ψ⁻¹ (1 - s - w) n) *
      exp (w * (Real.log (lemma23PaperP D ^ z) : ℂ)) * lemma57OmegaOne D w / w

end ZhangLS.Spec
