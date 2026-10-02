import ZhangLS.Spec.Lemma61GammaApproximation

/-! # Actual wide Gamma and original E1 error estimates for Lemma 6.1

Actual Gamma recurrence gives sharp all-real-part logarithmic derivatives.
Original Psi implies actual wide normalized Z bounds and small complex shifts.
The shifted contour gives the original short sum and its original E1 bound.
The full Lemma61Target remains unproved: contour and truncation relations remain.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Set MeasureTheory
open scoped Real Topology ComplexConjugate
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

lemma lemma61_wide_height_data {D : ℕ} (hL : 3 ≤ lemma23PaperL D) {s : ℂ}
    (hs : |s.im - (lemma23PaperCenter D).im| ≤ 2 * lemma23PaperL D ^ 405 + 3) :
    lemma51PaperT0 D ≤ s.im ∧ 2 ≤ s.im ∧
      |Real.log (s.im / (2 * Real.pi)) - Real.log (lemma51PaperT0 D)| ≤
        3 * lemma23PaperL D ^ (-114 : ℤ) := by
  let z : ℂ := ((1 / 2 : ℝ) : ℂ) + I * (s.im : ℂ)
  have hz : Lemma51InExtendedRegion D z := by
    dsimp [Lemma51InExtendedRegion,z]
    simp only [add_re,ofReal_re,mul_re,I_re,ofReal_im,mul_zero,I_im,zero_mul,
      sub_zero,add_zero,sub_self,abs_zero,add_im,mul_im,one_mul,zero_add]
    exact ⟨(lemma44_alpha_pos_le_one hL).1.le,hs⟩
  have hh := lemma51_extended_region_data hL hz
  have hb : lemma51PaperT0 D ≤ s.im := by simpa [z] using hh.2.2.1
  have hT : 3 ≤ lemma51PaperT0 D :=
    hL.trans (le_self_pow₀ (by linarith : 1 ≤ lemma23PaperL D) (by norm_num))
  exact ⟨hb,by linarith only [hb,hT],by simpa [z] using lemma51_height_log_error hL hz⟩

lemma lemma61_DirichletZ_logDeriv_at_T0_wide {D N : ℕ} [NeZero N]
    (θ : DirichletCharacter ℂ N) (hθ : θ.IsPrimitive) (hN : N ≠ 1)
    {s : ℂ} (hL : 3 ≤ lemma23PaperL D)
    (hre : |s.re| ≤ 2 * lemma23PaperL D ^ 9)
    (him : |s.im - (lemma23PaperCenter D).im| ≤ 2 * lemma23PaperL D ^ 405 + 3) :
    ‖logDeriv (lemma23DirichletZ θ) s + Complex.log (N : ℂ) +
      (Real.log (lemma51PaperT0 D) : ℂ)‖ ≤ 34 * lemma23PaperL D ^ (-114 : ℤ) := by
  have hh := lemma61_wide_height_data hL him
  have hL1 : 1 ≤ lemma23PaperL D := by linarith
  have hL0 : 0 < lemma23PaperL D := by linarith
  have hT : 0 < lemma51PaperT0 D := pow_pos hL0 519
  have ht : 0 < s.im := by linarith only [hh.2.1]
  have hg := lemma61_DirichletZ_logDeriv_all_real θ hθ hN hh.2.1
  have hnum : (27 + 2 * |s.re|) / s.im ≤ 31 * lemma23PaperL D ^ (-114 : ℤ) := by
    calc
      _ ≤ 31 * lemma23PaperL D ^ 9 / s.im :=
        div_le_div_of_nonneg_right (by nlinarith only [hre,one_le_pow₀ (n := 9) hL1]) ht.le
      _ ≤ 31 * lemma23PaperL D ^ 9 / lemma51PaperT0 D :=
        div_le_div_of_nonneg_left (by positivity) hT hh.1
      _ = 31 * lemma23PaperL D ^ (-510 : ℤ) := by
        unfold lemma51PaperT0
        rw [div_eq_mul_inv,mul_assoc,← zpow_natCast (lemma23PaperL D) 9,
          ← zpow_natCast (lemma23PaperL D) 519,← zpow_neg,← zpow_add₀ hL0.ne']
        norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ hL1 (by norm_num)) (by norm_num)
  have hn : ‖((Real.log (lemma51PaperT0 D) - Real.log (s.im / (2 * Real.pi)) : ℝ) : ℂ)‖ ≤
      3 * lemma23PaperL D ^ (-114 : ℤ) := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_sub_comm] using hh.2.2
  have he : logDeriv (lemma23DirichletZ θ) s + Complex.log (N : ℂ) +
      (Real.log (lemma51PaperT0 D) : ℂ) =
      (logDeriv (lemma23DirichletZ θ) s + Complex.log (N : ℂ) +
        (Real.log (s.im / (2 * Real.pi)) : ℂ)) +
      ((Real.log (lemma51PaperT0 D) - Real.log (s.im / (2 * Real.pi)) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add (hg.trans hnum) hn).trans_eq (by ring))

lemma lemma61_family_Z_logDeriv_normalized_wide {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hL : 3 ≤ lemma23PaperL D)
    (hre : |s.re| ≤ 2 * lemma23PaperL D ^ 9)
    (him : |s.im - (lemma23PaperCenter D).im| ≤ 2 * lemma23PaperL D ^ 405 + 3) :
    ‖logDeriv (lemma23DirichletZ ψ) s +
      (Real.log (lemma23PaperP D * lemma51PaperT0 D) : ℂ)‖ ≤
        35 * lemma23PaperL D ^ (-68 : ℤ) := by
  have hg := lemma61_DirichletZ_logDeriv_at_T0_wide ψ hψ.2.1 hψ.1.ne_one hL hre him
  have hq := lemma51_family_log_error ψ hψ
  have hP : 0 < lemma23PaperP D := Real.exp_pos _
  have hT : 0 < lemma51PaperT0 D := pow_pos (by linarith : 0 < lemma23PaperL D) 519
  have hn : ‖((Real.log (lemma23PaperP D) - Real.log (p : ℝ) : ℝ) : ℂ)‖ ≤
      lemma23PaperL D ^ (-68 : ℤ) := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_sub_comm,abs_of_nonneg hq.1]
    exact hq.2
  have he : logDeriv (lemma23DirichletZ ψ) s +
      (Real.log (lemma23PaperP D * lemma51PaperT0 D) : ℂ) =
      (logDeriv (lemma23DirichletZ ψ) s + Complex.log (p : ℂ) +
        (Real.log (lemma51PaperT0 D) : ℂ)) +
      ((Real.log (lemma23PaperP D) - Real.log (p : ℝ) : ℝ) : ℂ) := by
    rw [Real.log_mul hP.ne' hT.ne',← Complex.natCast_log]
    push_cast
    ring
  rw [he]
  apply (norm_add_le _ _).trans
  have hp : lemma23PaperL D ^ (-114 : ℤ) ≤ lemma23PaperL D ^ (-68 : ℤ) :=
    zpow_le_zpow_right₀ (by linarith : 1 ≤ lemma23PaperL D) (by norm_num)
  linarith only [hg,hn,hp]

lemma lemma61_family_Z_log_modulus_wide {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hL : 3 ≤ lemma23PaperL D)
    (hre : |s.re| ≤ 2 * lemma23PaperL D ^ 9)
    (him : |s.im - (lemma23PaperCenter D).im| ≤ 2 * lemma23PaperL D ^ 405 + 3) :
    |Real.log ‖lemma23DirichletZ ψ s‖ +
      Real.log (lemma23PaperP D * lemma51PaperT0 D) * (s.re - 1 / 2)| ≤
        35 * lemma23PaperL D ^ (-68 : ℤ) * |s.re - 1 / 2| := by
  have hh := lemma61_wide_height_data hL him
  have ht : 0 < s.im := by linarith only [hh.2.1]
  let c : ℝ := Real.log (lemma23PaperP D * lemma51PaperT0 D)
  obtain ⟨H,hHnorm,hHd⟩ := lemma44_exists_horizontal_log_modulus
    (f := lemma23DirichletZ ψ)
    (fun z hz => lemma23DirichletZ_differentiableAt_of_im_ne_zero ψ (ne_of_gt hz))
    (fun z hz => lemma23DirichletZ_ne_zero_of_im_pos ψ hψ.2.1 hψ.1.ne_one hz) ht
  have hzero : H (1 / 2) = 0 := by
    have hn := lemma23DirichletZ_norm_eq_one_on_critical_line ψ hψ.2.1 hψ.1.ne_one
      (s := ((1 / 2 : ℝ) : ℂ) + I * (s.im : ℂ)) (by simp)
    apply Real.exp_injective
    rw [hHnorm,hn,Real.exp_zero]
  let J : ℝ → ℝ := fun x => H x + c * (x - 1 / 2)
  have hJd (x : ℝ) : HasDerivAt J
      ((logDeriv (lemma23DirichletZ ψ) ((x : ℂ) + I * (s.im : ℂ))).re + c) x := by
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
      ‖(logDeriv (lemma23DirichletZ ψ) ((x : ℂ) + I * (s.im : ℂ))).re + c‖ ≤
        35 * lemma23PaperL D ^ (-68 : ℤ) := by
    have hz := lemma61_family_Z_logDeriv_normalized_wide ψ hψ hL
      (s := (x : ℂ) + I * (s.im : ℂ)) (by simpa using hwide x hx) (by simpa using him)
    have hr := Complex.abs_re_le_norm
      (logDeriv (lemma23DirichletZ ψ) ((x : ℂ) + I * (s.im : ℂ)) + (c : ℂ))
    simpa [Real.norm_eq_abs,c] using hr.trans hz
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (hJd x).hasDerivWithinAt) hdn (convex_uIcc (1 / 2) s.re)
    left_mem_uIcc right_mem_uIcc
  have hsEq : (s.re : ℂ) + I * (s.im : ℂ) = s := by apply Complex.ext <;> simp
  have hn := hHnorm s.re
  rw [hsEq] at hn
  have he : Real.log ‖lemma23DirichletZ ψ s‖ = H s.re := by rw [← hn,Real.log_exp]
  dsimp [J] at hb
  rw [hzero,sub_self,mul_zero,add_zero,sub_zero] at hb
  rw [he]
  simpa only [Real.norm_eq_abs] using hb

lemma lemma61_family_Z_norm_model_wide {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hL : 3 ≤ lemma23PaperL D)
    (hre : |s.re| ≤ 2 * lemma23PaperL D ^ 9)
    (him : |s.im - (lemma23PaperCenter D).im| ≤ 2 * lemma23PaperL D ^ 405 + 3) :
    ‖lemma23DirichletZ ψ s‖ ≤ Real.exp
      (-Real.log (lemma23PaperP D * lemma51PaperT0 D) * (s.re - 1 / 2) +
        35 * lemma23PaperL D ^ (-68 : ℤ) * |s.re - 1 / 2|) := by
  have hlog := lemma61_family_Z_log_modulus_wide ψ hψ hL hre him
  have ht : 0 < s.im := by linarith [(lemma61_wide_height_data hL him).2.1]
  have hn : 0 < ‖lemma23DirichletZ ψ s‖ := norm_pos_iff.mpr
    (lemma23DirichletZ_ne_zero_of_im_pos ψ hψ.2.1 hψ.1.ne_one ht)
  rw [← Real.exp_log hn]
  apply Real.exp_le_exp.mpr
  have hb := (abs_le.mp hlog).2
  linarith only [hb]

lemma lemma61_six_alpha_le_quarter {D : ℕ} (hL : 3 ≤ lemma23PaperL D) :
    6 * lemma44PaperAlpha D ≤ 1 / 4 := by
  have hL0 : 0 < lemma23PaperL D := by linarith
  have hp : (3 : ℝ) ^ 9 ≤ lemma23PaperL D ^ 9 := pow_le_pow_left₀ (by norm_num) hL 9
  unfold lemma44PaperAlpha lemma23PaperP
  rw [Real.log_exp,← mul_div_assoc]
  apply (div_le_iff₀ (pow_pos hL0 9)).mpr
  norm_num at hp
  nlinarith only [hp,Real.pi_le_four]

lemma lemma61_PT0_log_bounds {D : ℕ} (hL : 3 ≤ lemma23PaperL D) :
    0 ≤ Real.log (lemma23PaperP D * lemma51PaperT0 D) ∧
      Real.log (lemma23PaperP D * lemma51PaperT0 D) ≤ 2 * lemma23PaperL D ^ 9 := by
  let L := lemma23PaperL D
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have h8 : (3 : ℝ) ^ 8 ≤ L ^ 8 := pow_le_pow_left₀ (by norm_num) hL 8
  have h519 : 519 * L ≤ L ^ 9 := by
    calc
      519 * L ≤ L ^ 8 * L := by norm_num at h8; nlinarith only [h8,hL0]
      _ = L ^ 9 := by ring
  have hlog : 519 * Real.log L ≤ L ^ 9 := by
    linarith only [Real.log_le_sub_one_of_pos hL0,h519]
  have hP : 0 < lemma23PaperP D := Real.exp_pos _
  have hT : 0 < lemma51PaperT0 D := pow_pos hL0 519
  have he : Real.log (lemma23PaperP D * lemma51PaperT0 D) = L ^ 9 + 519 * Real.log L := by
    rw [Real.log_mul hP.ne' hT.ne',
      lemma23PaperP,Real.log_exp,lemma51PaperT0,Real.log_pow]
    rfl
  rw [he]
  constructor
  · exact add_nonneg (pow_nonneg hL0.le _) (mul_nonneg (by norm_num) (Real.log_nonneg hL1))
  · change _ ≤ 2 * L ^ 9
    linarith only [hlog]

lemma lemma61_family_Z_norm_thin {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hL : 3 ≤ lemma23PaperL D)
    (hre : |s.re - 1 / 2| ≤ 6 * lemma44PaperAlpha D)
    (him : |s.im - (lemma23PaperCenter D).im| ≤ 2 * lemma23PaperL D ^ 405 + 3) :
    ‖lemma23DirichletZ ψ s‖ ≤ Real.exp (222 * Real.pi) := by
  have hL1 : 1 ≤ lemma23PaperL D := by linarith
  have hL0 : 0 < lemma23PaperL D := by linarith
  have ha := lemma61_six_alpha_le_quarter hL
  have halpha := lemma44_alpha_pos_le_one hL
  have hr : |s.re| ≤ 1 := by
    have ht := abs_add_le (s.re - 1 / 2) (1 / 2 : ℝ)
    norm_num at ht
    linarith only [ht,hre,ha]
  have hwide : |s.re| ≤ 2 * lemma23PaperL D ^ 9 :=
    hr.trans (by nlinarith only [one_le_pow₀ (n := 9) hL1])
  have hb := lemma61_family_Z_norm_model_wide ψ hψ hL hwide him
  have hc := lemma61_PT0_log_bounds hL
  have he : lemma23PaperL D ^ 9 * lemma44PaperAlpha D = Real.pi := by
    simp only [lemma44PaperAlpha,lemma23PaperP,Real.log_exp]
    field_simp
  have hm : -Real.log (lemma23PaperP D * lemma51PaperT0 D) * (s.re - 1 / 2) ≤ 12 * Real.pi := by
    calc
      _ ≤ Real.log (lemma23PaperP D * lemma51PaperT0 D) * |s.re - 1 / 2| := by
        convert mul_le_mul_of_nonneg_left (neg_le_abs (s.re - (1 / 2 : ℝ))) hc.1 using 1 <;> ring
      _ ≤ (2 * lemma23PaperL D ^ 9) * (6 * lemma44PaperAlpha D) :=
        mul_le_mul hc.2 hre (abs_nonneg _) (by positivity)
      _ = _ := by nlinarith only [he]
  have hz : lemma23PaperL D ^ (-68 : ℤ) ≤ 1 := zpow_le_one_of_nonpos₀ hL1 (by norm_num)
  have hs6 : |s.re - 1 / 2| ≤ 6 := hre.trans (by linarith only [halpha.2])
  have hcorr : 35 * lemma23PaperL D ^ (-68 : ℤ) * |s.re - 1 / 2| ≤ 210 * Real.pi := by
    have hh := mul_le_mul hz hs6 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith only [hh,Real.one_le_pi_div_two]
  apply hb.trans
  exact Real.exp_le_exp.mpr (by linarith only [hm,hcorr])

lemma lemma61_thin_real_in_wide {D : ℕ} (hL : 3 ≤ lemma23PaperL D) {s : ℂ}
    (hre : |s.re - 1 / 2| ≤ 6 * lemma44PaperAlpha D) : |s.re| ≤ 2 * lemma23PaperL D ^ 9 := by
  have ha := lemma61_six_alpha_le_quarter hL
  have ht := abs_add_le (s.re - 1 / 2) (1 / 2 : ℝ)
  norm_num at ht
  have hB : 1 ≤ lemma23PaperL D ^ 9 := one_le_pow₀ (by linarith : 1 ≤ lemma23PaperL D)
  linarith only [ha,hre,ht,hB]

end ZhangLS.Spec
