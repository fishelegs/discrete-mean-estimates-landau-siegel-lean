import ZhangLS.Spec.Lemma83SmallShift
/-! Original Lemma 8.3, with the actual Section 7 coefficients, genuine
continuation, all primes retained, and a uniform absolute small-shift error. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex Filter Topology
open scoped Classical
set_option maxHeartbeats 1000000

lemma lemma83_paper_beta_norm {D : ℕ} {c : ℝ} (hL : 3 ≤ lemma23PaperL D)
    (hc : 0 < c) (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D ≤ 1/10) (j : Fin 3) :
    ‖lemma83PaperBeta D c j‖ ≤ 3*lemma44PaperAlpha D := by
  have hb := lemma52_offset_bounds hL hc hsmall
  unfold lemma83PaperBeta
  split_ifs
  · simpa only [lemma52PaperBetaOne,norm_mul,norm_I,one_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg hb.1.1] using hb.1.2
  · simpa only [lemma52PaperBetaTwo,norm_mul,norm_I,one_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg hb.2.1.1] using hb.2.1.2
  · simpa only [lemma52PaperBetaThree,norm_mul,norm_I,one_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg hb.2.2.1] using hb.2.2.2

lemma lemma83_alpha_small {D : ℕ} (hL : 100 ≤ lemma23PaperL D) :
    0 < lemma44PaperAlpha D ∧ lemma44PaperAlpha D ≤ 1/100 := by
  have hLp : 0 < lemma23PaperL D := by linarith only [hL]
  have hpow : (100:ℝ)^2 ≤ lemma23PaperL D^9 := by
    apply (pow_le_pow_left₀ (by norm_num) hL 2).trans
    exact pow_le_pow_right₀ (by linarith : (1:ℝ) ≤ lemma23PaperL D) (by norm_num)
  unfold lemma44PaperAlpha lemma23PaperP
  rw [Real.log_exp]
  refine ⟨div_pos Real.pi_pos (pow_pos hLp 9),?_⟩
  apply (div_le_iff₀ (pow_pos hLp 9)).mpr
  nlinarith [Real.pi_le_four]

lemma lemma83_paper_cutoff_log {D d r : ℕ} (hL : 100 ≤ lemma23PaperL D)
    (hd : 0 < d) (hr : 0 < r)
    (hcut : (d*r:ℝ) < lemma23PaperP D * lemma56PaperT D^(-2:ℤ)) :
    Real.log (d*r:ℕ) ≤ lemma23PaperL D^9 := by
  have hT : 1 ≤ lemma56PaperT D := by
    unfold lemma56PaperT
    apply Real.one_le_exp_iff.mpr
    exact Real.rpow_nonneg (by linarith) _
  have hTinv : lemma56PaperT D^(-2:ℤ) ≤ 1 := by
    rw [zpow_neg,zpow_ofNat]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hT)
  have hP : 0 < lemma23PaperP D := by unfold lemma23PaperP; positivity
  have hprod := hcut.trans_le (mul_le_of_le_one_right hP.le hTinv)
  have hlog := Real.log_lt_log (show (0:ℝ) < (d*r:ℝ) by positivity) hprod
  unfold lemma23PaperP at hlog
  rw [Real.log_exp] at hlog
  simpa only [Nat.cast_mul] using hlog.le

lemma lemma83_uniform_growth {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) (hβ : ∀ i, (β i).re = 0) (j : Fin 3) (d r : ℕ)
    (C : ℝ) (hBC : lemma83RegularProductBound < C) (hEC : lemma83ExceptionalConstant ≤ C)
    (s : ℂ) (hs : 9/10 < s.re) :
    ‖lemma83EulerCorrection χ β j d r s‖ <
      C*∏ p ∈ (d*r).primeFactors, (1+C*(p:ℝ)^(-s.re)) := by
  have hC : 0 < C := lemma83_regular_product_bound_pos.trans hBC
  have hprod : (∏ p ∈ (d*r).primeFactors, (1+lemma83ExceptionalConstant*(p:ℝ)^(-s.re))) ≤
      ∏ p ∈ (d*r).primeFactors, (1+C*(p:ℝ)^(-s.re)) := by
    apply Finset.prod_le_prod
    · intro p hp
      positivity [lemma83_exceptional_constant_pos]
    · intro p hp
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hEC (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  have hp : 0 < ∏ p ∈ (d*r).primeFactors, (1+C*(p:ℝ)^(-s.re)) := by
    apply prod_pos
    intro p hp
    positivity
  exact ((lemma83_euler_correction_bound χ β hβ j d r s hs.le).trans
    (mul_le_mul_of_nonneg_left hprod lemma83_regular_product_bound_pos.le)).trans_lt
      (mul_lt_mul_of_pos_right hBC hp)

/-- The complete original statement, uniformly for the already chosen positive
paper shift constant c. No assumption (A) is required in this lemma. -/
theorem lemma83_original : Lemma83Target := by
  intro c hc
  let K : ℕ := ⌈3*lemma83FiniteShiftWeight⌉₊
  have hK : 3*lemma83FiniteShiftWeight ≤ (K:ℝ) := Nat.le_ceil _
  let C := lemma83RegularProductBound+lemma83ExceptionalConstant+2
  have hC : 0 < C := by dsimp [C]; positivity [lemma83_regular_product_bound_pos,lemma83_exceptional_constant_pos]
  have hC1 : 1 ≤ C := by dsimp [C]; linarith [lemma83_regular_product_bound_pos,lemma83_exceptional_constant_pos]
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hpoly := ht.eventually (lemma83_polylog_eventually_le (lemma83TotalShiftConstant*Real.pi)
    (mul_pos lemma83_total_shift_constant_pos Real.pi_pos) (K+2))
  obtain ⟨Dc,hDc,hcsmall⟩ := lemma46_exists_contraction_threshold (c := 5*c) (by positivity)
  obtain ⟨D₀,hD₀⟩ := Filter.eventually_atTop.mp (show ∀ᶠ D : ℕ in atTop,
      2 ≤ D ∧ Dc ≤ D ∧ 100 ≤ lemma23PaperL D ∧
        (lemma83TotalShiftConstant*Real.pi)*(1+9*Real.log (lemma23PaperL D))^(K+2) ≤
          lemma23PaperL D from by
    filter_upwards [eventually_ge_atTop (2:ℕ),eventually_ge_atTop Dc,
      ht.eventually_ge_atTop 100,hpoly] with D h2 hDc hL hp
    exact ⟨h2,hDc,hL,hp⟩)
  refine ⟨C,hC,D₀,(hD₀ D₀ le_rfl).1,?_⟩
  intro D hD χ j d r hd hr hcut
  have hdata := hD₀ D hD
  have hL := hdata.2.2.1
  have ha := lemma83_alpha_small hL
  have hsmall : c*lemma44PaperAlpha D*lemma23PaperL D ≤ 1/10 := by
    have hh := hcsmall D hdata.2.1
    nlinarith only [hh]
  have hb := lemma83_paper_beta_norm (by linarith only [hL] : 3 ≤ lemma23PaperL D) hc hsmall
  have hβ := lemma83_beta_re D c
  have hy : 1 < lemma23PaperL D^9 := one_lt_pow₀ (by linarith only [hL]) (by norm_num)
  have hscale : lemma44PaperAlpha D*lemma23PaperL D^9 ≤ Real.pi := by
    unfold lemma44PaperAlpha lemma23PaperP
    rw [Real.log_exp,div_mul_cancel₀ _ (pow_ne_zero _ (by linarith only [hL] : lemma23PaperL D ≠ 0))]
  refine ⟨lemma83EulerCorrection χ (lemma83PaperBeta D c) j d r,
    lemma83_euler_is_continuation χ _ hβ j d r (mul_ne_zero hd.ne' hr.ne'),?_,?_⟩
  · intro s hs
    apply lemma83_uniform_growth χ _ hβ j d r C
    · dsimp [C]; linarith only [lemma83_exceptional_constant_pos]
    · dsimp [C]; linarith only [lemma83_regular_product_bound_pos]
    · exact hs
  · intro s hs
    have hsre : 9/10 ≤ s.re := by
      have hh := Complex.abs_re_le_norm (s-1)
      simp only [Complex.sub_re,Complex.one_re] at hh
      have hleft := (abs_le.mp (hh.trans hs)).1
      linarith only [hleft,ha.2]
    have hh := lemma83_euler_correction_small_shift χ _ hβ j d r hd.ne' hr.ne' s hsre
      (lemma44PaperAlpha D) (lemma23PaperL D^9) ha.1.le (by linarith only [ha.2]) hb hs hy
      (lemma83_paper_cutoff_log hL hd hr hcut) hscale K hK
    have hLp : 0 < lemma23PaperL D := by linarith only [hL]
    have hpoly' := hdata.2.2.2
    have herr : lemma83TotalShiftConstant*lemma44PaperAlpha D*
        (1+Real.log (lemma23PaperL D^9))^(K+2) ≤ lemma23PaperL D^(-8:ℤ) := by
      rw [Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      calc
        _ = ((lemma83TotalShiftConstant*Real.pi)*
            (1+9*Real.log (lemma23PaperL D))^(K+2))/(lemma23PaperL D^9) := by
          unfold lemma44PaperAlpha lemma23PaperP
          rw [Real.log_exp]
          ring
        _ ≤ lemma23PaperL D/(lemma23PaperL D^9) :=
          div_le_div_of_nonneg_right hpoly' (pow_nonneg hLp.le _)
        _ = _ := by rw [zpow_neg,zpow_ofNat]; field_simp
    exact (hh.trans herr).trans (le_mul_of_one_le_left (by positivity) hC1)

end ZhangLS.Spec
