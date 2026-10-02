import ZhangLS.Spec.Proposition71HorizontalLogNorm
import ZhangLS.Spec.Lemma61WideZBounds

/-! # Actual reciprocal-Z growth for the common finite-polynomial contour

The true primitive conductor is arbitrary subject to log N≤3L^9. In
particular this covers q=p and q=Dp without replacing either by the other.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Set
set_option maxHeartbeats 3000000

lemma proposition71_Z_log_derivative_wide {D N : ℕ} [NeZero N]
    (θ : DirichletCharacter ℂ N) (hθ : θ.IsPrimitive) (hN : N≠1)
    (hlogN : Real.log (N : ℝ)≤3*lemma23PaperL D^9) (hL : 3≤lemma23PaperL D)
    {s : ℂ} (hre : |s.re|≤2*lemma23PaperL D^9)
    (ht : |s.im-(lemma23PaperCenter D).im|≤2*lemma23PaperL D^405+3) :
    ‖logDeriv (lemma23DirichletZ θ) s‖≤600*lemma23PaperL D^9 := by
  have hL1 : 1≤lemma23PaperL D := by linarith
  have hLp : 0<lemma23PaperL D := by linarith
  have hN1 : (1 : ℝ)≤N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hT1 : 1≤lemma51PaperT0 D := one_le_pow₀ hL1
  have hpow : lemma23PaperL D≤lemma23PaperL D^9 := le_self_pow₀ hL1 (by norm_num)
  have hTlog : Real.log (lemma51PaperT0 D)≤519*lemma23PaperL D^9 := by
    rw [lemma51PaperT0,Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    nlinarith [Real.log_le_self hLp.le]
  have hc : ‖Complex.log (N : ℂ)+(Real.log (lemma51PaperT0 D) : ℂ)‖≤522*lemma23PaperL D^9 := by
    rw [←Complex.natCast_log,←Complex.ofReal_add,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (add_nonneg (Real.log_nonneg hN1) (Real.log_nonneg hT1))]
    linarith
  have hi : lemma23PaperL D^(-114 : ℤ)≤1 := zpow_le_one_of_nonpos₀ hL1 (by norm_num)
  have hh := lemma61_DirichletZ_logDeriv_at_T0_wide θ hθ hN hL hre ht
  have he : logDeriv (lemma23DirichletZ θ) s=
      (logDeriv (lemma23DirichletZ θ) s+Complex.log (N : ℂ)+(Real.log (lemma51PaperT0 D) : ℂ))-
        (Complex.log (N : ℂ)+(Real.log (lemma51PaperT0 D) : ℂ)) := by ring
  rw [he]
  apply (norm_sub_le _ _).trans
  nlinarith only [hh,hc,hi,one_le_pow₀ (n := 9) hL1]

/-- A coarse bound sufficient on the original Gaussian-suppressed horizontal
edges. At the new left side Re=1/2, the exact modulus is one. -/
theorem proposition71_inverse_Z_finite_contour_bound {D N : ℕ} [NeZero N]
    (θ : DirichletCharacter ℂ N) (hθ : θ.IsPrimitive) (hN : N≠1)
    (hlogN : Real.log (N : ℝ)≤3*lemma23PaperL D^9) (hL : 3≤lemma23PaperL D)
    {s : ℂ} (hslo : 1/2≤s.re) (hshi : s.re≤3/2)
    (ht : |s.im-(lemma23PaperCenter D).im|≤lemma23PaperL D^405+1) :
    ‖(lemma23DirichletZ θ s)⁻¹‖≤Real.exp (600*lemma23PaperL D^9) := by
  have hL1 : 1≤lemma23PaperL D := by linarith
  have hwide : |s.im-(lemma23PaperCenter D).im|≤2*lemma23PaperL D^405+3 := by
    have hh : 0≤lemma23PaperL D^405 := pow_nonneg (by linarith) _
    linarith
  have htime : 0<s.im := by linarith only [(lemma61_wide_height_data hL hwide).2.1]
  have hf (x : ℝ) (_hx : x∈Icc (1/2 : ℝ) s.re) :
      DifferentiableAt ℂ (lemma23DirichletZ θ) ((x : ℂ)+I*(s.im : ℂ)) :=
    lemma23DirichletZ_differentiableAt_of_im_ne_zero θ (by simpa using htime.ne')
  have hn (x : ℝ) (_hx : x∈Icc (1/2 : ℝ) s.re) :
      lemma23DirichletZ θ ((x : ℂ)+I*(s.im : ℂ))≠0 :=
    lemma23DirichletZ_ne_zero_of_im_pos θ hθ hN (by simpa using htime)
  have hb (x : ℝ) (hx : x∈Icc (1/2 : ℝ) s.re) :
      ‖logDeriv (lemma23DirichletZ θ) ((x : ℂ)+I*(s.im : ℂ))‖≤600*lemma23PaperL D^9 := by
    apply proposition71_Z_log_derivative_wide θ hθ hN hlogN hL
    · simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,
        Complex.ofReal_im,mul_zero,zero_mul,sub_zero,add_zero]
      rw [abs_of_nonneg (by linarith only [hx.1] : 0≤x)]
      nlinarith only [hx.2,hshi,one_le_pow₀ (n := 9) hL1]
    · simpa using hwide
  have hr := (proposition71_horizontal_norm_ratio_bound hslo hf hn hb).1
  have hcrit := lemma23DirichletZ_norm_eq_one_on_critical_line θ hθ hN
    (s := ((1/2 : ℝ) : ℂ)+I*(s.im : ℂ)) (by simp)
  have hscoord : (s.re : ℂ)+I*(s.im : ℂ)=s := by apply Complex.ext <;> simp
  rw [norm_div,hcrit,hscoord,one_div,←norm_inv] at hr
  apply hr.trans
  apply Real.exp_le_exp.mpr
  exact mul_le_of_le_one_right (by positivity) (by linarith)

end ZhangLS.Spec
