import ZhangLS.Spec.Lemma84BoundaryIntegralBounds
set_option autoImplicit false
namespace ZhangLS.Spec
open Filter Topology
set_option maxHeartbeats 1500000

/-- Every fixed polynomial is absorbed by the actual left-contour saving
exp(−L^(1/10)), without replacing it by an invalid conductor-power bound. -/
lemma lemma84_stretched_exponential_absorption (C : ℝ) (hC : 0 < C) (M N : ℕ) :
    ∀ᶠ L : ℝ in atTop,
      C*L^M*Real.exp (-(L^(1/10:ℝ))) ≤ L^(-(N:ℤ)) := by
  have ht : Tendsto (fun L : ℝ => L^(1/10:ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hb := ht.eventually ((Real.isLittleO_pow_exp_atTop (n := 10*(M+N))).bound (inv_pos.mpr hC))
  filter_upwards [hb,eventually_ge_atTop (1:ℝ)] with L hbound hL
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hu : 0 < L^(1/10:ℝ) := Real.rpow_pos_of_pos hLp _
  simp only [Real.norm_eq_abs,abs_pow,abs_of_pos hu,abs_of_pos (Real.exp_pos _)] at hbound
  have hpow : (L^(1/10:ℝ))^(10*(M+N)) = L^(M+N) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hLp.le]
    rw [show (1/10:ℝ)*(10*(M+N):ℕ) = ((M+N:ℕ):ℝ) by push_cast; ring,Real.rpow_natCast]
  rw [hpow] at hbound
  have hprod : C*L^(M+N) ≤ Real.exp (L^(1/10:ℝ)) := by
    have hh := mul_le_mul_of_nonneg_left hbound hC.le
    simpa only [←mul_assoc,mul_inv_cancel₀ hC.ne',one_mul] using hh
  have he := mul_le_mul_of_nonneg_right hprod (Real.exp_pos (-(L^(1/10:ℝ)))).le
  rw [←Real.exp_add,add_neg_cancel,Real.exp_zero] at he
  rw [zpow_neg,zpow_natCast]
  rw [inv_eq_one_div]
  apply (le_div_iff₀ (pow_pos hLp N)).mpr
  rw [pow_add] at he
  nlinarith only [he]

lemma lemma84_polylog_to_polynomial (L : ℝ) (hL : 1 ≤ L) (K : ℕ) :
    (1+20*Real.log L)^K ≤ 21^K*L^K := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hlog := Real.log_le_sub_one_of_pos hLp
  have hlog0 := Real.log_nonneg hL
  have hh := pow_le_pow_left₀ (by positivity : 0 ≤ 1+20*Real.log L)
    (show 1+20*Real.log L ≤ 21*L by linarith only [hlog,hL]) K
  simpa only [mul_pow] using hh

lemma lemma84_paper_left_exponential {D : ℕ} (hL : 0 < lemma23PaperL D)
    {x : ℝ} (hxT : lemma56PaperT D < x) :
    Real.exp (-Real.log x/lemma23PaperL D) ≤
      Real.exp (-(lemma23PaperL D^(1/10:ℝ))) := by
  have hT : 0 < lemma56PaperT D := by unfold lemma56PaperT; positivity
  have hxlog := (Real.log_lt_log hT hxT).le
  unfold lemma56PaperT at hxlog
  rw [Real.log_exp] at hxlog
  have he : lemma23PaperL D^(11/10:ℝ)/lemma23PaperL D = lemma23PaperL D^(1/10:ℝ) := by
    simpa only [show (11/10:ℝ)-1 = 1/10 by norm_num,Real.rpow_one] using
      (Real.rpow_sub hL (11/10) 1).symm
  apply Real.exp_le_exp.mpr
  have hh := div_le_div_of_nonneg_right hxlog hL.le
  change lemma23PaperL D^(11/10:ℝ)/lemma23PaperL D ≤ Real.log x/lemma23PaperL D at hh
  rw [he] at hh
  rw [neg_div]
  linarith only [hh]

end ZhangLS.Spec
