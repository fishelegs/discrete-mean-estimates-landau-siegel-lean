import ZhangLS.Spec.Lemma54EighthMoment

/-! # Genuine eighth-order decay of the actual Mellin transform

Eight integrations by parts, each with proved convergence and vanishing
endpoints, give the original δ(s) a uniform |s|⁻⁸ bound on Re(s)=1.
No higher-order transform estimate is assumed.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex MeasureTheory Set Finset

/-- Iterated actual integration by parts through order eight. -/
theorem lemma54_eighth_mellin_iteration {D : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) {s : ℂ} (hs : 0<s.re) :
    ∀ n : ℕ, n≤8 →
      (∏ j ∈ range n, (s+(j:ℂ)))*lemma54PaperDeltaMellin D s =
        (-1:ℂ)^n*mellin (lemma54EighthIntegral D n) (s+(n:ℂ)) := by
  intro n
  induction n with
  | zero =>
    intro hn
    simpa using
      (lemma54_eighth_zero_mellin_actual hD s).symm
  | succ n ih =>
    intro hn
    have hi := ih (by omega)
    have hs' : 0<(s+(n:ℂ)).re := by
      simp only [add_re,natCast_re]
      positivity
    have hstep := lemma54_eighth_mellin_step hD hL (by omega : n<8) hs'
    have hshift : s+((n+1:ℕ):ℂ) = s+(n:ℂ)+1 := by push_cast; ring
    rw [prod_range_succ,hshift,pow_succ]
    calc
      _ = (s+(n:ℂ))*((∏ j ∈ range n, (s+(j:ℂ)))*lemma54PaperDeltaMellin D s) := by ring
      _ = (-1:ℂ)^n*((s+(n:ℂ))*mellin (lemma54EighthIntegral D n) (s+(n:ℂ))) := by rw [hi]; ring
      _ = _ := by rw [hstep]; ring

/-- All eight actual derivative factors remain in the denominator. -/
theorem lemma54_eighth_mellin_integral_identity {D : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) {s : ℂ} (hs : 0<s.re) :
    (∏ j ∈ range 8, (s+(j:ℂ)))*lemma54PaperDeltaMellin D s =
      ∫ x : ℝ in Ioi 0, (x:ℂ)^(s+7)*lemma54EighthIntegral D 8 x := by
  have hh := lemma54_eighth_mellin_iteration hD hL hs 8 (by norm_num)
  norm_num only [show (-1:ℂ)^8=1 by norm_num,one_mul,Nat.cast_ofNat] at hh
  rw [hh]
  unfold mellin
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [smul_eq_mul]
  congr 2
  ring

/-- Positive real part prevents any of the shifted factors from reducing
its norm. This accounts for the full eighth denominator. -/
theorem lemma54_eighth_norm_shift_le {s : ℂ} (hs : 0≤s.re) (j : ℕ) : ‖s‖≤‖s+(j:ℂ)‖ := by
  have he : ‖s+(j:ℂ)‖^2 = ‖s‖^2+2*(j:ℝ)*s.re+(j:ℝ)^2 := by
    rw [Complex.sq_norm,Complex.sq_norm,Complex.normSq_apply,Complex.normSq_apply]
    simp only [add_re,add_im,natCast_re,natCast_im,add_zero]
    ring
  have hj : 0≤(j:ℝ) := Nat.cast_nonneg j
  nlinarith [norm_nonneg s,norm_nonneg (s+(j:ℂ)),mul_nonneg hj hs,sq_nonneg (j:ℝ)]

/-- The exact moment controls δ on its actual Mellin line. -/
theorem lemma54_eighth_mellin_bound_by_moment {D : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) {s : ℂ} (hs : s.re=1) :
    ‖lemma54PaperDeltaMellin D s‖ ≤ lemma54EighthMoment D/‖s‖^8 := by
  have hspos : 0<s.re := by rw [hs]; norm_num
  have hsne : s≠0 := by intro hz; simp [hz] at hs
  have hnorm : 0<‖s‖^8 := pow_pos (norm_pos_iff.mpr hsne) 8
  have hm : (∫ x : ℝ in Ioi 0,
      ‖(x:ℂ)^(s+7)*lemma54EighthIntegral D 8 x‖) = lemma54EighthMoment D := by
    unfold lemma54EighthMoment
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [norm_mul,norm_cpow_eq_rpow_re_of_pos hx]
    norm_num [hs]
  have hi := norm_integral_le_integral_norm
    (f := fun x : ℝ => (x:ℂ)^(s+7)*lemma54EighthIntegral D 8 x)
    (μ := volume.restrict (Ioi 0))
  rw [← lemma54_eighth_mellin_integral_identity hD hL hspos,hm,norm_mul,norm_prod] at hi
  have hprod : ‖s‖^8 ≤ ∏ j ∈ range 8, ‖s+(j:ℂ)‖ := by
    have hh := prod_le_prod (s := range 8) (f := fun _ => ‖s‖)
      (fun _ _ => norm_nonneg s) (fun j _ => lemma54_eighth_norm_shift_le hspos.le j)
    simpa only [prod_const,card_range] using hh
  have hh := mul_le_mul_of_nonneg_right hprod (norm_nonneg (lemma54PaperDeltaMellin D s))
  apply (le_div_iff₀ hnorm).mpr
  nlinarith only [hi,hh]

/-- Uniform original-kernel eighth-order estimate. The constant is explicit,
independent of D, s, χ, and every coefficient sequence. -/
theorem lemma54_eighth_mellin_line_bound {D : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) {s : ℂ} (hs : s.re=1) :
    ‖lemma54PaperDeltaMellin D s‖ ≤
      lemma54EighthMomentConstant*lemma23PaperL D^7200/‖s‖^8 := by
  exact (lemma54_eighth_mellin_bound_by_moment hD hL hs).trans
    (div_le_div_of_nonneg_right (lemma54_eighth_moment_uniform_bound hD hL) (by positivity))

/-- The precise eighth-order real-frequency envelope used by Section 14.
It replaces neither δ nor the genuine prime sum by an arbitrary residual. -/
theorem lemma54_eighth_mellin_frequency_bound {D : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) (t : ℝ) :
    ‖lemma54PaperDeltaMellin D (1+I*(t:ℂ))‖ ≤
      lemma54EighthMomentConstant*lemma23PaperL D^7200/(1+t^2)^4 := by
  have hh := lemma54_eighth_mellin_line_bound hD hL
    (s := 1+I*(t:ℂ)) (by simp)
  have he : ‖(1:ℂ)+I*(t:ℂ)‖^8=(1+t^2)^4 := by
    rw [show (8:ℕ)=2*4 by norm_num,pow_mul,Complex.sq_norm,Complex.normSq_apply]
    simp [pow_two]
  rwa [he] at hh

/-- An explicit common threshold, fixed before the frequency or any
character/coefficient choices, for the eighth-order actual δ estimate. -/
theorem lemma54_eighth_mellin_explicit_threshold (D : ℕ)
    (hD : ⌈Real.exp 2000⌉₊+2≤D) (t : ℝ) :
    ‖lemma54PaperDeltaMellin D (1+I*(t:ℂ))‖ ≤
      lemma54EighthMomentConstant*lemma23PaperL D^7200/(1+t^2)^4 := by
  have hD2 : 2≤D := by omega
  have hE : Real.exp 2000≤(D:ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (by omega : ⌈Real.exp 2000⌉₊≤D))
  have hlog := Real.log_le_log (Real.exp_pos 2000) hE
  rw [Real.log_exp] at hlog
  exact lemma54_eighth_mellin_frequency_bound (by omega) hlog t

end ZhangLS.Spec
