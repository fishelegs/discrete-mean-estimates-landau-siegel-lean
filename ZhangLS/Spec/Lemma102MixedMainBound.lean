import ZhangLS.Spec.Lemma102MixedInterior
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Filter Topology
set_option maxHeartbeats 2500000

lemma lemma102_full_main_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (hL : 100≤lemma23PaperL D) {c : ℝ} (hc : 0<c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10)
    (j : Fin 3) (d r : ℕ) (hd : 0<d) (hr : 0<r)
    (hupper : (d*r:ℝ)≤lemma23PaperP D^(63/125:ℝ)) :
    ‖lemma102FullMain χ c j d r‖≤(2000/lemma23PaperL D^9)*
      (16*Real.exp 1*lemma102LogMainBound*lemma23PaperL D^2*‖lemma83Pi χ d r‖) := by
  have hy : (0:ℝ)<d*r := by positivity
  have hy1 : (1:ℝ)≤d*r := by exact_mod_cast Nat.mul_pos hd hr
  have hLp : 0< lemma23PaperL D := by linarith
  let M := 16*Real.exp 1*lemma102LogMainBound*lemma23PaperL D^2*‖lemma83Pi χ d r‖
  have hM : 0≤M := by dsimp [M]; positivity [lemma102_log_main_bound_pos]
  have hb {a : ℝ} (ha : a<1) (hya : (d*r:ℝ)≤lemma23PaperP D^a) :
      ‖LDerivAtOne χ*lemma83Pi χ d r*lemma102LogMain D c j (lemma101Cutoff D (d*r:ℝ) a)‖≤M := by
    have hx1 : 1≤lemma101Cutoff D (d*r:ℝ) a := (le_div_iff₀ hy).mpr (by simpa using hya)
    have hg := lemma102_log_main_bound hL hc hsmall j hx1 (lemma101_cutoff_lt_P hD hy1 ha)
    have hder := lemma84_actual_derivative_norm_upper χ hD (by linarith : 2≤lemma23PaperL D)
    rw [norm_mul,norm_mul]
    have hh := mul_le_mul (mul_le_mul_of_nonneg_right hder (norm_nonneg (lemma83Pi χ d r))) hg
      (norm_nonneg _) (show 0≤16*Real.exp 1*lemma23PaperL D^2*‖lemma83Pi χ d r‖ by positivity)
    exact hh.trans_eq (by dsimp [M]; ring)
  have hscale (z : ℂ) (hz : ‖z‖≤4*M) :
      ‖(500/(Real.log (lemma23PaperP D):ℂ))*z‖≤(2000/lemma23PaperL D^9)*M := by
    rw [norm_mul,lemma101_prefactor_norm hLp]
    exact (mul_le_mul_of_nonneg_left hz (by positivity)).trans_eq (by ring)
  unfold lemma102FullMain
  split_ifs with h1 h2
  · rw [←lemma102_initial_main_identity χ hD c j d r hd hr]
    apply hscale
    have h₁ := hb (by norm_num : (63/125:ℝ)<1) hupper
    have h₂ := hb (by norm_num : (251/500:ℝ)<1)
      (h1.trans (lemma101_half_power_le_power hD (by norm_num : (1/2:ℝ)≤251/500)))
    have h₃ := hb (by norm_num : (1/2:ℝ)<1) h1
    simpa using lemma102_second_difference_norm _ _ _ 0 0 0
      (by simpa using h₁) (by simpa using h₂) (by simpa using h₃)
  · rw [←lemma102_lower_main_identity χ c j d r hd hr]
    apply hscale
    have h₁ := hb (by norm_num : (63/125:ℝ)<1) hupper
    have h₂ := hb (by norm_num : (251/500:ℝ)<1) h2
    simpa using lemma102_two_term_norm _ _ 0 0 hM (by simpa using h₁) (by simpa using h₂)
  · rw [←lemma102_upper_main_identity χ c j d r]
    apply hscale
    exact (hb (by norm_num : (63/125:ℝ)<1) hupper).trans (by linarith)

noncomputable def lemma102MixedBoundaryExponent : ℕ := lemma84BoundaryXiExponent+lemma84PiExponent
noncomputable def lemma102MixedBoundaryConstant : ℝ :=
  2000*(lemma84BoundaryXiConstant+32*Real.exp 1*lemma102LogMainBound*lemma83PrimeProductScale+
    2+lemma84TaylorCircleConstant*lemma83PrimeProductScale)

lemma lemma102_mixed_boundary_constant_pos : 0< lemma102MixedBoundaryConstant := by
  unfold lemma102MixedBoundaryConstant lemma83PrimeProductScale
  positivity [lemma84_boundary_xi_constant_pos,lemma102_log_main_bound_pos,lemma84_circle_constants_pos.1]

/-- A uniform quantitative replacement error on the original boundary bands;
all D dependence is displayed as a fixed polylogarithm and (log T)^4/L^9. -/
theorem lemma102_mixed_boundary_pointwise :
    ∀ c : ℝ, 0<c → ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      2000≤lemma23PaperL D ∧ ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
      ∀ j : Fin 3, ∀ d r : ℕ, 0<d → 0<r → Lemma101Transition D (d*r:ℝ) →
        ‖lemma102Sum χ c j d r-lemma102FullMain χ c j d r‖≤
          lemma102MixedBoundaryConstant*(1+9*Real.log (lemma23PaperL D))^lemma102MixedBoundaryExponent*
            (Real.log (lemma56PaperT D))^4*lemma23PaperL D^(-9:ℤ) := by
  intro c hc
  obtain ⟨Nb,hNb,hbound⟩ := lemma102_genuine_boundary_bound c hc
  obtain ⟨Nc,hNc,hparams⟩ := lemma101_uniform_threshold c hc
  obtain ⟨D₀,hD₀⟩ := eventually_atTop.mp (show ∀ᶠ D : ℕ in atTop,
      Nb≤D ∧ Nc≤D ∧ 2≤D ∧ lemma23PaperP D^(63/125:ℝ)<lemma23PaperP D*lemma56PaperT D^(-2:ℤ) from by
    filter_upwards [eventually_ge_atTop Nb,eventually_ge_atTop Nc,lemma84_section8_cutoffs_eventually]
      with D hb hc hq
    exact ⟨hb,hc,hq.1,by simpa [lemma84Section8Cutoff,lemma84Section8P1] using (hq.2.2 6).2.1⟩)
  refine ⟨D₀,(hD₀ D₀ le_rfl).2.2.1,?_⟩
  intro D hDD
  obtain ⟨hNbD,hNcD,hD2,hPcut⟩ := hD₀ D hDD
  obtain ⟨_,hL,hsmall,_,_⟩ := hparams D hNcD
  refine ⟨hL,?_⟩
  intro χ hA j d r hd hr hband
  have hD : 1<D := by omega
  have hLp : 0< lemma23PaperL D := by linarith
  have hL1 : 1≤lemma23PaperL D := by linarith
  have hupper : (d*r:ℝ)≤lemma23PaperP D^(63/125:ℝ) := by
    rcases hband with ((h|h)|h)
    · exact h.2.trans (Real.rpow_le_rpow_of_exponent_le (lemma101_P_gt_one hD).le (by norm_num))
    · exact h.2.trans (Real.rpow_le_rpow_of_exponent_le (lemma101_P_gt_one hD).le (by norm_num))
    · exact h.2.le
  let B := 1+9*Real.log (lemma23PaperL D)
  let H := Real.log (lemma56PaperT D)
  let K := lemma102MixedBoundaryExponent
  have hB : 1≤B := by dsimp [B]; linarith [Real.log_nonneg hL1]
  have hH : 1≤H := by dsimp [H]; rw [lemma56PaperT,Real.log_exp]; exact Real.one_le_rpow hL1 (by norm_num)
  have hLH : lemma23PaperL D^2≤H^4 := by
    have hh : lemma23PaperL D≤H := by
      dsimp [H]; rw [lemma56PaperT,Real.log_exp]
      simpa using Real.rpow_le_rpow_of_exponent_le hL1 (show (1:ℝ)≤11/10 by norm_num)
    exact (pow_le_pow_left₀ hLp.le hh 2).trans (pow_le_pow_right₀ hH (by omega))
  have hXiPow : B^lemma84BoundaryXiExponent≤B^K :=
    pow_le_pow_right₀ hB (Nat.le_add_right _ _)
  have hPiPow : B^lemma84PiExponent≤B^K :=
    pow_le_pow_right₀ hB (Nat.le_add_left _ _)
  have hS : 0≤lemma83PrimeProductScale := by unfold lemma83PrimeProductScale; positivity
  have hPi : ‖lemma83Pi χ d r‖≤lemma83PrimeProductScale*B^K :=
    (lemma84_pi_polylog_bound χ (by linarith : 100≤lemma23PaperL D) d r lemma84PiExponent hd hr
      (hupper.trans_lt hPcut) (Nat.le_ceil _)).trans (mul_le_mul_of_nonneg_left hPiPow hS)
  have hX : lemma84BoundaryXiConstant*B^lemma84BoundaryXiExponent*H^4≤lemma84BoundaryXiConstant*B^K*H^4 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hXiPow lemma84_boundary_xi_constant_pos.le) (by positivity)
  have hY : 16*Real.exp 1*lemma102LogMainBound*lemma23PaperL D^2*‖lemma83Pi χ d r‖≤
      (16*Real.exp 1*lemma102LogMainBound*lemma83PrimeProductScale)*B^K*H^4 := by
    have hh := mul_le_mul hLH hPi (norm_nonneg _) (by positivity)
    have hh' := mul_le_mul_of_nonneg_left hh (show 0≤16*Real.exp 1*lemma102LogMainBound by positivity [lemma102_log_main_bound_pos])
    nlinarith only [hh']
  have hE : (2+lemma84TaylorCircleConstant*‖lemma83Pi χ d r‖)*lemma23PaperL D^(-6:ℤ)≤
      (2+lemma84TaylorCircleConstant*lemma83PrimeProductScale)*B^K*H^4 := by
    have hp := one_le_pow₀ hB (n:=K)
    have hh := mul_le_mul_of_nonneg_left hPi lemma84_circle_constants_pos.1.le
    have hs : 2+lemma84TaylorCircleConstant*‖lemma83Pi χ d r‖≤
        (2+lemma84TaylorCircleConstant*lemma83PrimeProductScale)*B^K := by nlinarith only [hp,hh]
    have hpow : lemma23PaperL D^(-6:ℤ)≤H^4 :=
      (zpow_le_one_of_nonpos₀ hL1 (by norm_num : (-6:ℤ)≤0)).trans (one_le_pow₀ hH)
    exact (mul_le_mul hs hpow (by positivity) (by positivity [lemma84_circle_constants_pos.1])).trans_eq (by ring)
  have hh := (norm_sub_le _ _).trans (add_le_add (hbound D hNbD χ hA j d r hd hr hband)
    (lemma102_full_main_bound χ hD (by linarith) hc hsmall j d r hd hr hupper))
  unfold lemma102BoundaryBound at hh
  have hs : lemma84BoundaryXiConstant*B^lemma84BoundaryXiExponent*H^4+
      2*(16*Real.exp 1*lemma102LogMainBound*lemma23PaperL D^2*‖lemma83Pi χ d r‖)+
      (2+lemma84TaylorCircleConstant*‖lemma83Pi χ d r‖)*lemma23PaperL D^(-6:ℤ)≤
      (lemma84BoundaryXiConstant+32*Real.exp 1*lemma102LogMainBound*lemma83PrimeProductScale+
        2+lemma84TaylorCircleConstant*lemma83PrimeProductScale)*B^K*H^4 := by nlinarith only [hX,hY,hE]
  have hs' := mul_le_mul_of_nonneg_left hs (show 0≤2000/lemma23PaperL D^9 by positivity)
  apply hh.trans
  convert hs' using 1 <;> dsimp [lemma102MixedBoundaryConstant,B,H,K] <;>
    simp only [zpow_neg,zpow_ofNat] <;> ring

end ZhangLS.Spec
