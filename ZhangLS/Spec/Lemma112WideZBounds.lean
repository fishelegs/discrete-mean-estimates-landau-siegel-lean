import ZhangLS.Spec.Lemma112ErrorKernel
/-! # Actual conductor-Dp Gamma model on the wide finite contour -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Real Topology

lemma lemma112_twist_Z_logDeriv_normalized_wide {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hψ : Lemma23InPsi (D := D) ψ) {s : ℂ} (hL : 3 ≤ lemma23PaperL D)
    (hre : |s.re| ≤ 2 * lemma23PaperL D ^ 9)
    (him : |s.im - (lemma23PaperCenter D).im| ≤ 2 * lemma23PaperL D ^ 405 + 3) :
    letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    ‖logDeriv (lemma23DirichletZ (lemma44CharacterTwist χ ψ)) s +
      (Real.log (lemma112ConductorScale D) : ℂ)‖ ≤ 35 * lemma23PaperL D ^ (-68 : ℤ) := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  have htw := lemma112_twist_family_data χ ψ hL hψ
  have hg := lemma61_DirichletZ_logDeriv_at_T0_wide (lemma44CharacterTwist χ ψ)
    htw.1 htw.2.2.1 hL hre him
  have hq := lemma51_family_log_error ψ hψ
  have hP : 0 < lemma23PaperP D := Real.exp_pos _
  have hD : (0 : ℝ) < D := by exact_mod_cast χ.modulus_pos
  have hp : (0 : ℝ) < p := by exact_mod_cast hψ.1.pos
  have hT : 0 < lemma51PaperT0 D := pow_pos (by linarith : 0 < lemma23PaperL D) 519
  have hn : ‖((Real.log (lemma23PaperP D) - Real.log (p : ℝ) : ℝ) : ℂ)‖ ≤
      lemma23PaperL D ^ (-68 : ℤ) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg hq.1]
    exact hq.2
  have he : logDeriv (lemma23DirichletZ (lemma44CharacterTwist χ ψ)) s +
      (Real.log (lemma112ConductorScale D) : ℂ) =
      (logDeriv (lemma23DirichletZ (lemma44CharacterTwist χ ψ)) s + Complex.log ((D * p : ℕ) : ℂ) +
        (Real.log (lemma51PaperT0 D) : ℂ)) +
      ((Real.log (lemma23PaperP D) - Real.log (p : ℝ) : ℝ) : ℂ) := by
    rw [lemma112ConductorScale, Real.log_mul (mul_pos hD hP).ne' hT.ne',
      Real.log_mul hD.ne' hP.ne', ← Complex.natCast_log, Nat.cast_mul, Real.log_mul hD.ne' hp.ne']
    push_cast
    ring
  rw [he]
  apply (norm_add_le _ _).trans
  have hpow : lemma23PaperL D ^ (-114 : ℤ) ≤ lemma23PaperL D ^ (-68 : ℤ) :=
    zpow_le_zpow_right₀ (by linarith : 1 ≤ lemma23PaperL D) (by norm_num)
  linarith only [hg, hn, hpow]

lemma lemma112_twist_Z_log_modulus_wide {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hL : 3 ≤ lemma23PaperL D)
    (hre : |s.re| ≤ 2 * lemma23PaperL D ^ 9)
    (him : |s.im - (lemma23PaperCenter D).im| ≤ 2 * lemma23PaperL D ^ 405 + 3) :
    letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    |Real.log ‖lemma23DirichletZ (lemma44CharacterTwist χ ψ) s‖ +
      Real.log (lemma112ConductorScale D) * (s.re - 1 / 2)| ≤
        35 * lemma23PaperL D ^ (-68 : ℤ) * |s.re - 1 / 2| := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  have htw := lemma112_twist_family_data χ ψ hL hψ
  have hh := lemma61_wide_height_data hL him
  have ht : 0 < s.im := by linarith only [hh.2.1]
  let c : ℝ := Real.log (lemma112ConductorScale D)
  obtain ⟨H,hHnorm,hHd⟩ := lemma44_exists_horizontal_log_modulus
    (f := lemma23DirichletZ (lemma44CharacterTwist χ ψ))
    (fun z hz => lemma23DirichletZ_differentiableAt_of_im_ne_zero (lemma44CharacterTwist χ ψ) (ne_of_gt hz))
    (fun z hz => lemma23DirichletZ_ne_zero_of_im_pos (lemma44CharacterTwist χ ψ) htw.1 htw.2.2.1 hz) ht
  have hzero : H (1 / 2) = 0 := by
    have hn := lemma23DirichletZ_norm_eq_one_on_critical_line (lemma44CharacterTwist χ ψ) htw.1 htw.2.2.1
      (s := ((1 / 2 : ℝ) : ℂ) + I * (s.im : ℂ)) (by simp)
    apply Real.exp_injective
    rw [hHnorm,hn,Real.exp_zero]
  let J : ℝ → ℝ := fun x => H x + c * (x - 1 / 2)
  have hJd (x : ℝ) : HasDerivAt J
      ((logDeriv (lemma23DirichletZ (lemma44CharacterTwist χ ψ)) ((x : ℂ) + I * (s.im : ℂ))).re + c) x := by
    have hd : HasDerivAt (fun x : ℝ => c * (x - 1 / 2)) c x := by
      simpa using ((hasDerivAt_id x).sub_const (1 / 2 : ℝ)).const_mul c
    exact (hHd x).add hd
  have hwide (x : ℝ) (hx : x ∈ uIcc (1 / 2) s.re) : |x| ≤ 2 * lemma23PaperL D ^ 9 := by
    have hB : 1 ≤ lemma23PaperL D ^ 9 := one_le_pow₀ (by linarith : 1 ≤ lemma23PaperL D)
    have hr := abs_le.mp hre
    have hlo : -(2 * lemma23PaperL D ^ 9) ≤ min (1 / 2) s.re := le_min (by linarith) hr.1
    have hhi : max (1 / 2) s.re ≤ 2 * lemma23PaperL D ^ 9 := max_le (by linarith) hr.2
    exact abs_le.mpr ⟨hlo.trans hx.1,hx.2.trans hhi⟩
  have hdn (x : ℝ) (hx : x ∈ uIcc (1 / 2) s.re) :
      ‖(logDeriv (lemma23DirichletZ (lemma44CharacterTwist χ ψ)) ((x : ℂ) + I * (s.im : ℂ))).re + c‖ ≤
        35 * lemma23PaperL D ^ (-68 : ℤ) := by
    have hz := lemma112_twist_Z_logDeriv_normalized_wide χ ψ hψ hL
      (s := (x : ℂ) + I * (s.im : ℂ)) (by simpa using hwide x hx) (by simpa using him)
    have hr := Complex.abs_re_le_norm
      (logDeriv (lemma23DirichletZ (lemma44CharacterTwist χ ψ)) ((x : ℂ) + I * (s.im : ℂ)) + (c : ℂ))
    simpa [Real.norm_eq_abs,c] using hr.trans hz
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (hJd x).hasDerivWithinAt) hdn (convex_uIcc (1 / 2) s.re)
    left_mem_uIcc right_mem_uIcc
  have hsEq : (s.re : ℂ) + I * (s.im : ℂ) = s := by apply Complex.ext <;> simp
  have hn := hHnorm s.re
  rw [hsEq] at hn
  have he : Real.log ‖lemma23DirichletZ (lemma44CharacterTwist χ ψ) s‖ = H s.re := by rw [← hn,Real.log_exp]
  dsimp [J] at hb
  rw [hzero,sub_self,mul_zero,add_zero,sub_zero] at hb
  rw [he]
  simpa only [Real.norm_eq_abs] using hb

lemma lemma112_twist_Z_norm_model_wide {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hL : 3 ≤ lemma23PaperL D)
    (hre : |s.re| ≤ 2 * lemma23PaperL D ^ 9)
    (him : |s.im - (lemma23PaperCenter D).im| ≤ 2 * lemma23PaperL D ^ 405 + 3) :
    letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    ‖lemma23DirichletZ (lemma44CharacterTwist χ ψ) s‖ ≤ Real.exp
      (-Real.log (lemma112ConductorScale D) * (s.re - 1 / 2) +
        35 * lemma23PaperL D ^ (-68 : ℤ) * |s.re - 1 / 2|) := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  have htw := lemma112_twist_family_data χ ψ hL hψ
  have hlog := lemma112_twist_Z_log_modulus_wide χ ψ hψ hL hre him
  have ht : 0 < s.im := by linarith [(lemma61_wide_height_data hL him).2.1]
  have hn : 0 < ‖lemma23DirichletZ (lemma44CharacterTwist χ ψ) s‖ := norm_pos_iff.mpr
    (lemma23DirichletZ_ne_zero_of_im_pos (lemma44CharacterTwist χ ψ) htw.1 htw.2.2.1 ht)
  rw [← Real.exp_log hn]
  apply Real.exp_le_exp.mpr
  have hb := (abs_le.mp hlog).2
  linarith only [hb]

noncomputable def lemma112DualScale (D : ℕ) (z : ℝ) : ℝ :=
  lemma23PaperP D ^ (1 - z) * (D : ℝ) * lemma51PaperT0 D

lemma lemma112_dual_scale_pos {D : ℕ} (hD : 1 < D) (z : ℝ) :
    0 < lemma112DualScale D z := by
  unfold lemma112DualScale lemma51PaperT0
  exact mul_pos (mul_pos (Real.rpow_pos_of_pos (Real.exp_pos _) _)
    (by exact_mod_cast lt_trans Nat.zero_lt_one hD))
    (pow_pos (Real.log_pos (by exact_mod_cast hD)) _)

lemma lemma112_dual_scale_log {D : ℕ} (hD : 1 < D) (z : ℝ) :
    Real.log (lemma112DualScale D z) =
      Real.log (lemma112ConductorScale D) - Real.log (lemma23PaperP D ^ z) := by
  have hP : 0 < lemma23PaperP D := Real.exp_pos _
  have hDr : (0 : ℝ) < D := by exact_mod_cast lt_trans Nat.zero_lt_one hD
  have hT : 0 < lemma51PaperT0 D := pow_pos (Real.log_pos (by exact_mod_cast hD)) _
  unfold lemma112DualScale lemma112ConductorScale
  rw [Real.log_mul (mul_pos (Real.rpow_pos_of_pos hP _) hDr).ne' hT.ne',
    Real.log_mul (Real.rpow_pos_of_pos hP _).ne' hDr.ne',
    Real.log_mul (mul_pos hDr hP).ne' hT.ne', Real.log_mul hDr.ne' hP.ne',
    Real.log_rpow hP, Real.log_rpow hP]
  ring

/-- Exact product-conductor normalization leaves precisely the dual D*t₀ scale. -/
lemma lemma112_twist_Z_scale_cancellation {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hψ : Lemma23InPsi (D := D) ψ) {s w : ℂ}
    (hD : 1 < D) (hL : 3 ≤ lemma23PaperL D) (hs : Lemma112InRegion D s)
    (hwre : -(lemma23PaperL D ^ 9) ≤ w.re ∧ w.re ≤ 2)
    (hwim : |w.im| ≤ lemma23PaperL D ^ 20) (z : ℝ) :
    letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    ‖lemma23DirichletZ (lemma44CharacterTwist χ ψ) (s + w) *
      exp (w * (Real.log (lemma23PaperP D ^ z) : ℂ))‖ ≤
        Real.exp 1 * Real.exp (-w.re * Real.log (lemma112DualScale D z)) := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  have hd := lemma61_large_shift_rectangle_bounds hL
    (lemma112_region_subset_lemma61 hL hs) hwre hwim
  have hz := lemma112_twist_Z_norm_model_wide χ ψ hψ hL hd.1 hd.2.1
  have he := lemma61_wide_log_modulus_error_le_one hL hd.2.2
  have hr : (s + w).re - 1 / 2 = w.re := by simp only [add_re, hs.1]; ring
  rw [hr] at hz he
  rw [norm_mul, norm_exp]
  simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  calc
    _ ≤ Real.exp (-Real.log (lemma112ConductorScale D) * w.re +
        35 * lemma23PaperL D ^ (-68 : ℤ) * |w.re|) *
          Real.exp (w.re * Real.log (lemma23PaperP D ^ z)) :=
      mul_le_mul_of_nonneg_right hz (Real.exp_nonneg _)
    _ ≤ Real.exp (-Real.log (lemma112ConductorScale D) * w.re + 1) *
          Real.exp (w.re * Real.log (lemma23PaperP D ^ z)) := by
      gcongr
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add, lemma112_dual_scale_log hD z]
      congr 1
      ring

lemma lemma112_Dt0_log_budget {D : ℕ} (hD : 1 < D) (hL : 64 ≤ lemma23PaperL D) :
    Real.log ((D : ℝ) * lemma51PaperT0 D) ≤ lemma23PaperL D ^ 9 / 1000 := by
  have h0 : 0 < lemma23PaperL D := by linarith
  have h8 : (520000 : ℝ) ≤ lemma23PaperL D ^ 8 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 64) hL 8
    norm_num at h
    linarith only [h]
  have hp : 520000 * lemma23PaperL D ≤ lemma23PaperL D ^ 9 := by
    convert mul_le_mul_of_nonneg_right h8 h0.le using 1 <;> ring
  have hlog := Real.log_le_sub_one_of_pos h0
  rw [lemma51PaperT0, Real.log_mul (by exact_mod_cast (Nat.ne_of_gt (lt_trans Nat.zero_lt_one hD)))
    (pow_ne_zero _ h0.ne'), Real.log_pow]
  change lemma23PaperL D + (519 : ℝ) * Real.log (lemma23PaperL D) ≤ _
  linarith only [hp, hlog, h0]

lemma lemma112_dual_scale_cutoff_gap {D : ℕ} (hD : 1 < D) (hL : 64 ≤ lemma23PaperL D)
    {z : ℝ} (hz : (1 / 2 : ℝ) ≤ z) :
    Real.log (lemma112DualScale D z) ≤ (501 / 1000 : ℝ) * lemma23PaperL D ^ 9 ∧
    lemma23PaperL D ^ 9 / 1000 ≤
      Real.log (lemma112PaperP1 D) - Real.log (lemma112DualScale D z) := by
  have hP : 0 < lemma23PaperP D := Real.exp_pos _
  have hDr : (0 : ℝ) < D := by exact_mod_cast lt_trans Nat.zero_lt_one hD
  have hT : 0 < lemma51PaperT0 D := pow_pos (Real.log_pos (by exact_mod_cast hD)) _
  have he : Real.log (lemma112DualScale D z) =
      (1 - z) * lemma23PaperL D ^ 9 + Real.log ((D : ℝ) * lemma51PaperT0 D) := by
    unfold lemma112DualScale
    rw [mul_assoc, Real.log_mul (Real.rpow_pos_of_pos hP _).ne' (mul_pos hDr hT).ne',
      Real.log_rpow hP, lemma23PaperP, Real.log_exp]
  have hp : Real.log (lemma112PaperP1 D) = (63 / 125 : ℝ) * lemma23PaperL D ^ 9 := by
    rw [lemma112PaperP1, Real.log_rpow hP, lemma23PaperP, Real.log_exp]
  have hb := lemma112_Dt0_log_budget hD hL
  have hpow : 0 ≤ lemma23PaperL D ^ 9 := by positivity
  have hm := mul_le_mul_of_nonneg_right (show 1 - z ≤ 1 / 2 by linarith only [hz]) hpow
  rw [he]
  constructor
  · linarith only [hb, hm]
  · rw [hp]
    linarith only [hb, hm, hpow]

end ZhangLS.Spec
