import ZhangLS.Spec.Lemma81CoarsePolynomialBounds

/-! # Original Gaussian boundary decay and uniform envelope absorption -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Set Filter
open scoped Real Topology
set_option maxHeartbeats 2000000

lemma lemma81_gaussian_boundary_decay {D : ℕ} (hL : 3 ≤ lemma23PaperL D)
    {x t : ℝ} (hx : |x| ≤ 1) (ht : lemma23PaperL D^405-1 ≤ |t|) :
    ‖lemma81Omega D (lemma81SegmentPoint D x t)‖ ≤
      2*Real.exp (-(lemma23PaperL D^10)/32) := by
  have hLp : 0 < lemma23PaperL D := by linarith only [hL]
  have hL1 : 1 ≤ lemma23PaperL D := by linarith only [hL]
  let W := lemma23PaperL D^400
  let H := lemma23PaperL D^405
  have hW : 0 < W := pow_pos hLp 400
  have hW1 : 1 ≤ W := one_le_pow₀ hL1
  have hH3 : 3 ≤ H := hL.trans (le_self_pow₀ hL1 (by norm_num))
  have hH0 : 0 ≤ H := by linarith only [hH3]
  have htAbs : H/2 ≤ |t| := by change H-1 ≤ |t| at ht; linarith only [ht,hH3]
  have ht2 : H^2/4 ≤ t^2 := by
    have hh := (sq_le_sq₀ (by positivity : 0 ≤ H/2) (abs_nonneg t)).mpr htAbs
    rw [sq_abs] at hh
    nlinarith only [hh]
  have hx2 : x^2 ≤ 1 := by nlinarith only [(abs_le.mp hx).1,(abs_le.mp hx).2]
  have hscale : lemma23PaperL D^10 * W^2 = H^2 := by dsimp [W,H]; ring
  have hHsq : 8 ≤ H^2 := by nlinarith only [hH3]
  have hpre : Real.sqrt Real.pi/W ≤ 2 := by
    have hsqrt : Real.sqrt Real.pi ≤ 2 := (Real.sqrt_le_iff).mpr ⟨by norm_num,by nlinarith only [Real.pi_le_four]⟩
    apply (div_le_iff₀ hW).mpr
    linarith only [hsqrt,hW1]
  have hexp : (x^2-t^2)/(4*W^2) ≤ -(lemma23PaperL D^10)/32 := by
    apply (div_le_iff₀ (by positivity : 0 < 4*W^2)).mpr
    nlinarith only [hx2,ht2,hscale,hHsq]
  rw [lemma81_omega_segment_norm hLp]
  exact mul_le_mul hpre (Real.exp_le_exp.mpr hexp) (Real.exp_nonneg _) (by norm_num)

lemma lemma81_gaussian_boundary_decay_at {D : ℕ} (hL : 3 ≤ lemma23PaperL D)
    {s : ℂ} (hr : |s.re-1/2| ≤ 1)
    (ht : lemma23PaperL D^405-1 ≤ |s.im-(lemma23PaperCenter D).im|) :
    ‖lemma81Omega D s‖ ≤ 2*Real.exp (-(lemma23PaperL D^10)/32) := by
  have he : lemma81SegmentPoint D (s.re-1/2) (s.im-(lemma23PaperCenter D).im) = s := by
    apply Complex.ext <;> simp only [lemma81SegmentPoint,add_re,add_im,mul_re,mul_im,
      ofReal_re,ofReal_im,I_re,I_im,zero_mul,mul_zero,one_mul,sub_zero,add_zero,zero_add]
    · change 1/2+(s.re-1/2) = s.re
      ring
    · ring
  have hh := lemma81_gaussian_boundary_decay hL hr ht
  rw [he] at hh
  exact hh

/-- Any fixed exp(K L^9) boundary growth is absorbed uniformly by the exact
original Gaussian. Constants precede epsilon and its common D-threshold. -/
theorem lemma81_uniform_boundary_envelope_small {A K : ℝ} (hA : 0 ≤ A) (_hK : 0 ≤ K)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ D : ℕ, N ≤ D →
      A*Real.exp (K*lemma23PaperL D^9)*(2*Real.exp (-(lemma23PaperL D^10)/32)) ≤ ε := by
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hd : Tendsto (fun D : ℕ => 2*A*Real.exp (-lemma23PaperL D)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul (Real.tendsto_exp_neg_atTop_nhds_zero.comp ht)
  have he := hd.eventually (gt_mem_nhds hε)
  have hl := ht.eventually (eventually_ge_atTop (max 3 (64*K)))
  obtain ⟨Ne,hNe⟩ := eventually_atTop.mp he
  obtain ⟨Nl,hNl⟩ := eventually_atTop.mp hl
  refine ⟨max Ne Nl,?_⟩
  intro D hD
  have hlarge := hNl D ((le_max_right Ne Nl).trans hD)
  have hL : 3 ≤ lemma23PaperL D := (le_max_left _ _).trans hlarge
  have hKL : 64*K ≤ lemma23PaperL D := (le_max_right _ _).trans hlarge
  have hLp : 0 < lemma23PaperL D := by linarith only [hL]
  have h9 : 64 ≤ lemma23PaperL D^9 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hL 9
    norm_num at hh
    linarith only [hh]
  have hKL9 : 64*(K*lemma23PaperL D^9) ≤ lemma23PaperL D^10 := by
    have hh := mul_le_mul_of_nonneg_right hKL (pow_nonneg hLp.le 9)
    nlinarith only [hh]
  have hL10 : 64*lemma23PaperL D ≤ lemma23PaperL D^10 := by
    have hh := mul_le_mul_of_nonneg_right h9 hLp.le
    nlinarith only [hh]
  have hphase : K*lemma23PaperL D^9 - lemma23PaperL D^10/32 ≤ -lemma23PaperL D := by
    linarith only [hKL9,hL10]
  calc
    _ = 2*A*Real.exp (K*lemma23PaperL D^9-lemma23PaperL D^10/32) := by
      rw [sub_eq_add_neg,Real.exp_add,neg_div]
      ring
    _ ≤ 2*A*Real.exp (-lemma23PaperL D) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hphase) (by positivity)
    _ ≤ _ := (hNe D ((le_max_left Ne Nl).trans hD)).le

end ZhangLS.Spec
