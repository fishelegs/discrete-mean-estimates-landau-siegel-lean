import ZhangLS.Spec.Lemma84BoundaryMainBound
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset Filter Topology
set_option maxHeartbeats 2000000

noncomputable def lemma84BoundaryInnerExponent : ℕ :=
  lemma84BoundaryXiExponent+lemma84PiExponent
noncomputable def lemma84BoundaryInnerConstant : ℝ :=
  4*(lemma84BoundaryXiConstant+16*Real.exp 1*lemma83PrimeProductScale*(33+49*Real.pi))
lemma lemma84_boundary_inner_constant_pos : 0< lemma84BoundaryInnerConstant := by
  unfold lemma84BoundaryInnerConstant lemma83PrimeProductScale
  positivity [lemma84_boundary_xi_constant_pos]

/-- Closed boundary-layer error for the real second inner sum, with the true Π
and true L′ main term bounded explicitly. No use of (A) or original 8.4 here. -/
theorem lemma84_boundary_inner_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (hL : 100≤lemma23PaperL D) {c : ℝ} (hc : 0<c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10)
    (j : Fin 3) (μ d r : ℕ) (hd : 0<d) (hr : 0<r)
    (hQ1 : 1< lemma84Section8Cutoff D μ)
    (hQcut : lemma84Section8Cutoff D μ<lemma23PaperP D*lemma56PaperT D^(-2:ℤ))
    (hQP : lemma84Section8Cutoff D μ<lemma23PaperP D)
    (hlogQ : (1/4)*lemma23PaperL D^9≤Real.log (lemma84Section8Cutoff D μ)) :
    ‖lemma84Section8BoundaryInner χ c j μ d r‖≤
      lemma84BoundaryInnerConstant*(1+9*Real.log (lemma23PaperL D))^lemma84BoundaryInnerExponent*
        (Real.log (lemma56PaperT D))^4*lemma23PaperL D^(-9:ℤ) := by
  have hL1 : 1≤lemma23PaperL D := by linarith
  have hLp : 0< lemma23PaperL D := by linarith
  have hB : 1≤1+9*Real.log (lemma23PaperL D) := by linarith [Real.log_nonneg hL1]
  have hPoly : 0≤(1+9*Real.log (lemma23PaperL D))^lemma84BoundaryInnerExponent := by positivity
  have hH : 1≤Real.log (lemma56PaperT D) := by
    rw [lemma56PaperT,Real.log_exp]
    exact Real.one_le_rpow hL1 (by norm_num)
  have hHL : lemma23PaperL D≤Real.log (lemma56PaperT D) := by
    rw [lemma56PaperT,Real.log_exp]
    have hh := Real.rpow_le_rpow_of_exponent_le hL1 (show (1:ℝ)≤11/10 by norm_num)
    simpa only [Real.rpow_one] using hh
  have hLH : lemma23PaperL D^2≤(Real.log (lemma56PaperT D))^4 := by
    have h2 := pow_le_pow_left₀ hLp.le hHL 2
    exact h2.trans (pow_le_pow_right₀ hH (by omega))
  unfold lemma84Section8BoundaryInner
  split_ifs with hband
  swap
  · simp only [norm_zero]
    positivity [lemma84_boundary_inner_constant_pos]
  have hn0 : 0<((d*r:ℕ):ℝ) := by exact_mod_cast Nat.mul_pos hd hr
  have hn1 : 1≤((d*r:ℕ):ℝ) := by exact_mod_cast Nat.mul_pos hd hr
  have hQ := lemma84_section8_cutoff_pos D μ
  have hx1 : 1≤lemma84Section8Cutoff D μ/(d*r:ℕ) := (le_div_iff₀ hn0).mpr (by simpa using hband.2.le)
  have hxT : lemma84Section8Cutoff D μ/(d*r:ℕ)≤lemma56PaperT D := by
    have hh := (div_le_iff₀ (lemma56_paper_T_pos D)).mp hband.1
    apply (div_le_iff₀ hn0).mpr
    nlinarith only [hh]
  have hxP : lemma84Section8Cutoff D μ/(d*r:ℕ)<lemma23PaperP D := (div_le_self hQ.le hn1).trans_lt hQP
  have hcut : (d*r:ℝ)<lemma23PaperP D*lemma56PaperT D^(-2:ℤ) := by
    simpa only [Nat.cast_mul] using hband.2.trans hQcut
  have hlog := lemma83_paper_cutoff_log hL hd hr hcut
  have hlog' : Real.log (d*r:ℕ)≤lemma23PaperL D^9 := by simpa only [Nat.cast_mul] using hlog
  have hXi := lemma84_boundary_xi_small_x χ hD (by linarith) c j μ d r hd hr hlog' hx1 hxT
  have hPi := lemma84_pi_polylog_bound χ hL d r lemma84PiExponent hd hr hcut (Nat.le_ceil _)
  have hG := lemma84_boundary_g_main_bound hL hc hsmall j μ hx1 hxP
  have hder : ‖LDerivAtOne χ‖≤16*Real.exp 1*lemma23PaperL D^2 :=
    lemma32_actual_first_derivative_bound χ hD (by change 2≤lemma23PaperL D; linarith) (by simp; positivity)
  have hpowXi : (1+9*Real.log (lemma23PaperL D))^lemma84BoundaryXiExponent≤
      (1+9*Real.log (lemma23PaperL D))^lemma84BoundaryInnerExponent :=
    pow_le_pow_right₀ hB (Nat.le_add_right _ _)
  have hpowPi : (1+9*Real.log (lemma23PaperL D))^lemma84PiExponent≤
      (1+9*Real.log (lemma23PaperL D))^lemma84BoundaryInnerExponent :=
    pow_le_pow_right₀ hB (Nat.le_add_left _ _)
  have hPiScale : 0≤lemma83PrimeProductScale := by unfold lemma83PrimeProductScale; positivity
  have hmain : ‖LDerivAtOne χ*lemma83Pi χ d r*lemma84MainTerm D c j μ
      (lemma84Section8Cutoff D μ/(d*r:ℕ))‖≤
      (16*Real.exp 1*lemma83PrimeProductScale*(33+49*Real.pi))*
        (1+9*Real.log (lemma23PaperL D))^lemma84BoundaryInnerExponent*(Real.log (lemma56PaperT D))^4 := by
    rw [norm_mul,norm_mul]
    have hd' := hder.trans (mul_le_mul_of_nonneg_left hLH (by positivity))
    have hp' := hPi.trans (mul_le_mul_of_nonneg_left hpowPi hPiScale)
    have hh := mul_le_mul (mul_le_mul hd' hp' (norm_nonneg _) (by positivity)) hG (norm_nonneg _)
      (by positivity)
    nlinarith only [hh]
  have hXi' : ‖lemma84XiSum χ c j μ d r (lemma84Section8Cutoff D μ/(d*r:ℕ))‖≤
      lemma84BoundaryXiConstant*(1+9*Real.log (lemma23PaperL D))^lemma84BoundaryInnerExponent*
        (Real.log (lemma56PaperT D))^4 := by
    apply hXi.trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpowXi lemma84_boundary_xi_constant_pos.le) (by positivity)
  have herr := (norm_sub_le _ _).trans (add_le_add hXi' hmain)
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.log_pos hQ1)]
  calc
    _ ≤ ((lemma84BoundaryXiConstant+16*Real.exp 1*lemma83PrimeProductScale*(33+49*Real.pi))*
        (1+9*Real.log (lemma23PaperL D))^lemma84BoundaryInnerExponent*(Real.log (lemma56PaperT D))^4)/
      ((1/4)*lemma23PaperL D^9) := by
      apply div_le_div₀ (by positivity [lemma84_boundary_xi_constant_pos]) _ (by positivity) hlogQ
      nlinarith only [herr]
    _ = _ := by unfold lemma84BoundaryInnerConstant; simp only [zpow_neg,zpow_ofNat]; field_simp <;> ring

end ZhangLS.Spec
