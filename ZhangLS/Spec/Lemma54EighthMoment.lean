import ZhangLS.Spec.Lemma54EighthIntegrals
import ZhangLS.Spec.Lemma54LargeSecondMoment

/-! # Uniform eighth derivative moment on the actual Mellin line Re(s)=1

The exact moment ∫₀∞ x⁸ |I₈(x)| dx is finite and bounded by C(log D)^7200.
The small-x interval and both actual large-x tails are separately integrated.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex MeasureTheory Set Filter

noncomputable def lemma54EighthMoment (D : ℕ) : ℝ :=
  ∫ x : ℝ in Ioi 0, x^8*‖lemma54EighthIntegral D 8 x‖

noncomputable def lemma54EighthGlobalConstant : ℝ :=
  2*lemma54EighthConstant*Real.sqrt Real.pi*Real.exp 19

noncomputable def lemma54EighthLogConstant : ℝ :=
  lemma54EighthConstant*(4+2*Real.exp 1)

noncomputable def lemma54EighthExpConstant : ℝ :=
  2*lemma54EighthConstant*Real.sqrt Real.pi*Real.exp 20

noncomputable def lemma54EighthMomentConstant : ℝ :=
  lemma54EighthGlobalConstant + lemma54EighthLogConstant*(100*Real.sqrt Real.pi*Real.exp 6) +
    lemma54EighthExpConstant*(2*(Nat.factorial 17:ℝ))

theorem lemma54_eighth_constants_pos :
    0<lemma54EighthGlobalConstant ∧ 0<lemma54EighthLogConstant ∧
      0<lemma54EighthExpConstant ∧ 0<lemma54EighthMomentConstant := by
  have hC := lemma54_eighth_weighted_constant_pos
  have hs := Real.sqrt_pos.mpr Real.pi_pos
  unfold lemma54EighthMomentConstant lemma54EighthGlobalConstant lemma54EighthLogConstant lemma54EighthExpConstant
  exact ⟨by positivity,by positivity,by positivity,by positivity⟩

theorem lemma54_eighth_moment_integrable {D : ℕ} (hD : 1<D) (hL : 2000≤lemma23PaperL D) :
    IntegrableOn (fun x : ℝ => x^8*‖lemma54EighthIntegral D 8 x‖) (Ioi 0) := by
  have hc := lemma54_eighth_integral_mellin_convergent hD hL (by norm_num : 8≤8)
    (s := (9:ℂ)) (by norm_num)
  change IntegrableOn (fun x : ℝ => (x:ℂ)^((9:ℂ)-1)*lemma54EighthIntegral D 8 x) (Ioi 0) at hc
  apply hc.norm.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [norm_mul,norm_cpow_eq_rpow_re_of_pos hx]
  norm_num

theorem lemma54_eighth_global_norm_bound {D n : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) (hn : n≤8) (x : ℝ) :
    ‖lemma54EighthIntegral D n x‖ ≤ lemma54EighthGlobalConstant := by
  exact (lemma54_eighth_integral_norm_bound hD hn (lemma54_scale_ge_one hL) x).trans
    (div_le_self lemma54_eighth_constants_pos.1.le (lemma54_scale_ge_one hL))

theorem lemma54_eighth_small_moment_bound {D : ℕ} (hD : 1<D) (hL : 2000≤lemma23PaperL D) :
    (∫ x : ℝ in Ioc 0 (lemma51PaperT0 D^(51/50:ℝ)),
      x^8*‖lemma54EighthIntegral D 8 x‖) ≤
        lemma54EighthGlobalConstant*lemma23PaperL D^4770 := by
  let T := lemma51PaperT0 D^(51/50:ℝ)
  have ht := lemma54_small_endpoint_polynomial hL
  have hi := (lemma54_eighth_moment_integrable hD hL).mono_set
    (show Ioc 0 T⊆Ioi 0 from Ioc_subset_Ioi_self)
  have hc : IntegrableOn (fun _ : ℝ => T^8*lemma54EighthGlobalConstant) (Ioc 0 T) :=
    integrableOn_const (hs := measure_Ioc_lt_top.ne)
  have hm := integral_mono_ae hi hc (by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hw := pow_le_pow_left₀ hx.1.le hx.2 8
    exact mul_le_mul hw (lemma54_eighth_global_norm_bound hD hL (by norm_num) x)
      (norm_nonneg _) (pow_nonneg (by linarith : 0≤T) 8))
  rw [setIntegral_const,Real.volume_real_Ioc_of_le (by linarith : 0≤T),sub_zero,smul_eq_mul] at hm
  have hpow : T^9≤lemma23PaperL D^4770 := by
    have hh := pow_le_pow_left₀ (by linarith : 0≤T) ht.2 9
    simpa only [← pow_mul,show 530*9=4770 by norm_num] using hh
  have hh := mul_le_mul_of_nonneg_left hpow lemma54_eighth_constants_pos.1.le
  dsimp only [T] at hm hh
  nlinarith only [hm,hh]

noncomputable def lemma54EighthMomentEnvelope (D : ℕ) (x : ℝ) : ℝ :=
  lemma54EighthLogConstant*(x^8*Real.exp (-((lemma53PaperScale D*Real.log x/100)^2))) +
    lemma54EighthExpConstant*(x^8*Real.exp (-(x^(1/2:ℝ))/lemma53PaperScale D))

theorem lemma54_eighth_envelope_integrable {D : ℕ} (hD : 1<D) :
    IntegrableOn (lemma54EighthMomentEnvelope D) (Ioi 0) := by
  have hlog := lemma54_log_tail_moment_integrable (lemma53_scale_pos hD) 8
  have hexp := lemma54_half_power_moment_integrable (lemma53_scale_pos hD) (q := 8) (by norm_num)
  simp only [Real.rpow_ofNat] at hlog hexp
  exact (hlog.const_mul lemma54EighthLogConstant).add (hexp.const_mul lemma54EighthExpConstant)

theorem lemma54_eighth_envelope_nonneg (D : ℕ) (x : ℝ) : 0≤lemma54EighthMomentEnvelope D x := by
  obtain ⟨hglobal,hlog,hexp,hfull⟩ := lemma54_eighth_constants_pos
  unfold lemma54EighthMomentEnvelope
  positivity

theorem lemma54_eighth_envelope_bound {D : ℕ} (hD : 1<D) (hL : 2000≤lemma23PaperL D)
    {x : ℝ} (hx : lemma51PaperT0 D^(51/50:ℝ)<x) :
    x^8*‖lemma54EighthIntegral D 8 x‖ ≤ lemma54EighthMomentEnvelope D x := by
  have hx1 : 1≤x := (lemma54_small_endpoint_polynomial hL).1.trans hx.le
  have hx0 : 0<x := lt_of_lt_of_le zero_lt_one hx1
  have he := lemma54_eighth_integral_large_range hD hL (by norm_num : 8≤8) hx0 hx
  have hf := lemma54_stretched_exp_le_half_power (lemma53_scale_pos hD) hx1
  have ht : ‖lemma54EighthIntegral D 8 x‖ ≤
      lemma54EighthLogConstant*Real.exp (-((lemma53PaperScale D*Real.log x/100)^2)) +
        lemma54EighthExpConstant*Real.exp (-(x^(1/2:ℝ))/lemma53PaperScale D) := by
    change _ ≤ lemma54EighthLogConstant*Real.exp (-((lemma53PaperScale D*Real.log x/100)^2)) +
      lemma54EighthExpConstant*Real.exp (-(x^(99/100:ℝ))/lemma53PaperScale D) at he
    exact he.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hf lemma54_eighth_constants_pos.2.2.1.le))
  have hh := mul_le_mul_of_nonneg_left ht (pow_nonneg hx0.le 8)
  unfold lemma54EighthMomentEnvelope
  convert hh using 1 <;> ring

/-- Both eighth-weight tail moments are actual integrals with explicit constants. -/
theorem lemma54_eighth_envelope_integral_bound {D : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) :
    (∫ x : ℝ in Ioi 0, lemma54EighthMomentEnvelope D x) ≤
      lemma54EighthLogConstant*(100*Real.sqrt Real.pi*Real.exp 6) +
        lemma54EighthExpConstant*((2*(Nat.factorial 17:ℝ))*lemma53PaperScale D^18) := by
  have hB := lemma54_scale_ge_200 hL
  have hBp := lemma53_scale_pos hD
  have hlog := lemma54_log_tail_moment_integrable hBp 8
  have hexp := lemma54_half_power_moment_integrable hBp (q := 8) (by norm_num)
  have hlogeq := lemma54_log_tail_moment_integral hBp 8
  have hexpeq := lemma54_half_power_moment_integral hBp (q := 8) (by norm_num)
  simp only [Real.rpow_ofNat] at hlog hexp hlogeq hexpeq
  have hlogb : (∫ x : ℝ in Ioi 0, x^8*Real.exp (-((lemma53PaperScale D*Real.log x/100)^2))) ≤
      100*Real.sqrt Real.pi*Real.exp 6 := by
    rw [hlogeq]
    have hs : 4≤(lemma53PaperScale D/100)^2 := by
      have hb : 2≤lemma53PaperScale D/100 := by linarith
      nlinarith
    have he : Real.exp ((8+1:ℝ)^2/(4*(lemma53PaperScale D/100)^2)) ≤ Real.exp 6 := by
      apply Real.exp_le_exp.mpr
      apply (div_le_iff₀ (by positivity : 0<4*(lemma53PaperScale D/100)^2)).mpr
      nlinarith
    have hp : Real.sqrt Real.pi/(lemma53PaperScale D/100) ≤ 100*Real.sqrt Real.pi := by
      apply (div_le_iff₀ (by positivity : 0<lemma53PaperScale D/100)).mpr
      nlinarith [mul_le_mul_of_nonneg_left (show (1:ℝ)≤lemma53PaperScale D by linarith)
        (Real.sqrt_nonneg Real.pi)]
    exact mul_le_mul hp he (Real.exp_nonneg _) (by positivity)
  have hexpb : (∫ x : ℝ in Ioi 0, x^8*Real.exp (-(x^(1/2:ℝ))/lemma53PaperScale D)) =
      (2*(Nat.factorial 17:ℝ))*lemma53PaperScale D^18 := by
    rw [hexpeq]
    norm_num only [show (2:ℝ)*(8+1)=18 by norm_num,Real.rpow_ofNat]
    norm_num [Real.Gamma_ofNat_eq_factorial,Nat.factorial]
    ring
  unfold lemma54EighthMomentEnvelope
  rw [integral_add (hlog.const_mul _) (hexp.const_mul _),integral_const_mul,integral_const_mul,hexpb]
  exact add_le_add (mul_le_mul_of_nonneg_left hlogb lemma54_eighth_constants_pos.2.1.le) le_rfl

/-- The actual eighth moment has one uniform logarithmic polynomial budget. -/
theorem lemma54_eighth_moment_uniform_bound {D : ℕ} (hD : 1<D) (hL : 2000≤lemma23PaperL D) :
    lemma54EighthMoment D ≤ lemma54EighthMomentConstant*lemma23PaperL D^7200 := by
  let T := lemma51PaperT0 D^(51/50:ℝ)
  have ht0 : 0≤T := by have ht := (lemma54_small_endpoint_polynomial hL).1; linarith
  have hi := lemma54_eighth_moment_integrable hD hL
  have hg := lemma54_eighth_envelope_integrable hD
  have hm := integral_mono_ae (hi.mono_set (Ioi_subset_Ioi ht0))
    (hg.mono_set (Ioi_subset_Ioi ht0)) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact lemma54_eighth_envelope_bound hD hL hx)
  have hsub := setIntegral_mono_set hg
    (Eventually.of_forall (fun x => lemma54_eighth_envelope_nonneg D x))
    (Eventually.of_forall fun x hx => ht0.trans_lt hx)
  have hlarge := hm.trans (hsub.trans (lemma54_eighth_envelope_integral_bound hD hL))
  have hsmall := lemma54_eighth_small_moment_bound hD hL
  have hsplit := intervalIntegral.integral_interval_add_Ioi (a := 0) (b := T) hi (hi.mono_set (Ioi_subset_Ioi ht0))
  rw [intervalIntegral.integral_of_le ht0] at hsplit
  have hB : lemma53PaperScale D^18=lemma23PaperL D^7200 := by
    unfold lemma53PaperScale
    rw [← pow_mul]
  rw [hB] at hlarge
  have hL1 : 1≤lemma23PaperL D := by linarith
  have hpow := pow_le_pow_right₀ hL1 (show (4770:ℕ)≤7200 by norm_num)
  have hone : 1≤lemma23PaperL D^7200 := one_le_pow₀ hL1
  have hsmall' := mul_le_mul_of_nonneg_left hpow lemma54_eighth_constants_pos.1.le
  have hlog' := mul_le_mul_of_nonneg_left hone
    (show 0≤lemma54EighthLogConstant*(100*Real.sqrt Real.pi*Real.exp 6) by
      have hc := lemma54_eighth_constants_pos.2.1; positivity)
  unfold lemma54EighthMoment
  rw [← hsplit]
  dsimp only [T] at hlarge ⊢
  unfold lemma54EighthMomentConstant
  nlinarith only [hsmall,hlarge,hsmall',hlog']

end ZhangLS.Spec
