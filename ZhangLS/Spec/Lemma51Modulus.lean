import ZhangLS.Spec.Lemma51Parameters

/-! # Uniform absolute modulus of each actual Z in the thin strip -/

namespace ZhangLS.Spec

open Complex Set

set_option maxHeartbeats 1000000

theorem lemma51_DirichletZ_logDeriv_norm {D N : ℕ} [NeZero N]
    (θ : DirichletCharacter ℂ N) (hθ : θ.IsPrimitive) (hN : N ≠ 1)
    (hlogN : Real.log (N : ℝ) ≤ 2 * lemma23PaperL D ^ 9)
    {s : ℂ} (hL : 3 ≤ lemma23PaperL D) (hs : Lemma51InExtendedRegion D s) :
    ‖logDeriv (lemma23DirichletZ θ) s‖ ≤ 600 * lemma23PaperL D ^ 9 := by
  have hL1 : 1 ≤ lemma23PaperL D := by linarith
  have hLpos : 0 < lemma23PaperL D := by linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hT1 : 1 ≤ lemma51PaperT0 D := one_le_pow₀ hL1
  have hzpow : lemma23PaperL D ^ (-114 : ℤ) ≤ 1 :=
    zpow_le_one_of_nonpos₀ hL1 (by norm_num)
  have hpow : lemma23PaperL D ≤ lemma23PaperL D ^ 9 := le_self_pow₀ hL1 (by norm_num)
  have hTlog : Real.log (lemma51PaperT0 D) ≤ 519 * lemma23PaperL D ^ 9 := by
    rw [lemma51PaperT0, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    nlinarith [Real.log_le_self hLpos.le]
  have hc : ‖Complex.log (N : ℂ) + (Real.log (lemma51PaperT0 D) : ℂ)‖ ≤
      521 * lemma23PaperL D ^ 9 := by
    rw [← Complex.natCast_log, ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (add_nonneg (Real.log_nonneg hN1) (Real.log_nonneg hT1))]
    linarith
  have hb := lemma51_DirichletZ_logDeriv_at_T0 θ hθ hN hL hs
  have he : logDeriv (lemma23DirichletZ θ) s =
      (logDeriv (lemma23DirichletZ θ) s + Complex.log (N : ℂ) +
        (Real.log (lemma51PaperT0 D) : ℂ)) -
      (Complex.log (N : ℂ) + (Real.log (lemma51PaperT0 D) : ℂ)) := by ring
  rw [he]
  apply (norm_sub_le _ _).trans
  nlinarith [one_le_pow₀ (n := 9) hL1]

theorem lemma51_DirichletZ_norm_bound {D N : ℕ} [NeZero N]
    (θ : DirichletCharacter ℂ N) (hθ : θ.IsPrimitive) (hN : N ≠ 1)
    (hlogN : Real.log (N : ℝ) ≤ 2 * lemma23PaperL D ^ 9)
    {s : ℂ} (hL : 3 ≤ lemma23PaperL D) (hs : Lemma51InExtendedRegion D s) :
    ‖lemma23DirichletZ θ s‖ ≤ Real.exp (600 * Real.pi) := by
  have hh := lemma51_extended_region_data hL hs
  have hT : 0 < lemma51PaperT0 D := by unfold lemma51PaperT0; positivity
  have ht : 0 < s.im := hT.trans_le hh.2.2.1
  obtain ⟨H, hHnorm, hHd⟩ := lemma44_exists_horizontal_log_modulus
    (f := lemma23DirichletZ θ)
    (fun z hz => lemma23DirichletZ_differentiableAt_of_im_ne_zero θ (ne_of_gt hz))
    (fun z hz => lemma23DirichletZ_ne_zero_of_im_pos θ hθ hN hz) ht
  have hzero : H (1 / 2) = 0 := by
    have hn := lemma23DirichletZ_norm_eq_one_on_critical_line θ hθ hN
      (s := ((1 / 2 : ℝ) : ℂ) + I * (s.im : ℂ)) (by simp)
    apply Real.exp_injective
    rw [hHnorm, hn, Real.exp_zero]
  have hregion (x : ℝ) (hx : x ∈ uIcc (1 / 2) s.re) :
      Lemma51InExtendedRegion D ((x : ℂ) + I * (s.im : ℂ)) := by
    have ha := (lemma44_alpha_pos_le_one hL).1.le
    have hr := abs_le.mp hs.1
    have hlo : 1 / 2 - lemma44PaperAlpha D ≤ min (1 / 2) s.re :=
      le_min (by linarith) (by linarith)
    have hhi : max (1 / 2) s.re ≤ 1 / 2 + lemma44PaperAlpha D :=
      max_le (by linarith) (by linarith)
    have hxlo := hlo.trans hx.1
    have hxhi := hx.2.trans hhi
    simp only [Lemma51InExtendedRegion, add_re, ofReal_re, mul_re, I_re,
      ofReal_im, mul_zero, I_im, zero_mul, sub_zero, add_zero, add_im, mul_im, one_mul, zero_add]
    exact ⟨abs_le.mpr ⟨by linarith, by linarith⟩, hs.2⟩
  have hn (x : ℝ) (hx : x ∈ uIcc (1 / 2) s.re) :
      ‖(logDeriv (lemma23DirichletZ θ) ((x : ℂ) + I * (s.im : ℂ))).re‖ ≤
        600 * lemma23PaperL D ^ 9 := by
    rw [Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm _).trans
      (lemma51_DirichletZ_logDeriv_norm θ hθ hN hlogN hL (hregion x hx))
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (hHd x).hasDerivWithinAt) hn (convex_uIcc (1 / 2) s.re)
    left_mem_uIcc right_mem_uIcc
  rw [hzero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at hb
  have hmul := mul_le_mul_of_nonneg_left hs.1
    (by positivity : 0 ≤ 600 * lemma23PaperL D ^ 9)
  have he : lemma23PaperL D ^ 9 * lemma44PaperAlpha D = Real.pi := by
    simp only [lemma44PaperAlpha, lemma23PaperP, Real.log_exp]
    field_simp
  have hupper : H s.re ≤ 600 * Real.pi := by
    have ha := le_abs_self (H s.re)
    have hmul' : 600 * lemma23PaperL D ^ 9 * lemma44PaperAlpha D = 600 * Real.pi := by
      rw [mul_assoc, he]
    rw [hmul'] at hmul
    linarith
  have hsEq : (s.re : ℂ) + I * (s.im : ℂ) = s := by apply Complex.ext <;> simp
  have hhNorm := hHnorm s.re
  rw [hsEq] at hhNorm
  rw [← hhNorm]
  exact Real.exp_le_exp.mpr hupper

end ZhangLS.Spec
