import ZhangLS.Spec.Lemma83FiniteXiEuler
import ZhangLS.Spec.Lemma83

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace ZhangLS.Spec
open Finset Complex Filter Topology
open scoped Classical

noncomputable def lemma83OriginalXiMajorantConstant : ℝ :=
  Real.exp (8+842400000*Real.pi*Real.log 4)

lemma lemma83_original_xi_majorant_constant_pos : 0<lemma83OriginalXiMajorantConstant :=
  Real.exp_pos _

lemma lemma83_original_finite_phase_exponent {D N : ℕ} {b : ℝ}
    (hL : 1≤lemma23PaperL D) (hN : 1≤N) (hNP : (N:ℝ)≤lemma23PaperP D)
    (hb : 0≤b) (hbα : b≤3*lemma44PaperAlpha D) :
    b*Real.log 4*(2+Real.log (N:ℝ)) ≤ 9*Real.pi*Real.log 4 := by
  have hLp : 0<lemma23PaperL D := by linarith
  have hα : 0<lemma44PaperAlpha D := by
    unfold lemma44PaperAlpha lemma23PaperP
    rw [Real.log_exp]
    positivity [Real.pi_pos]
  have hlogN : Real.log (N:ℝ)≤lemma23PaperL D^9 := by
    simpa only [lemma23PaperP,Real.log_exp] using Real.log_le_log (Nat.cast_pos.mpr (by omega : 0<N)) hNP
  have hNlog : 0≤Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hpow := one_le_pow₀ hL (n := 9)
  have hid : lemma44PaperAlpha D*lemma23PaperL D^9=Real.pi := by
    unfold lemma44PaperAlpha lemma23PaperP
    rw [Real.log_exp]
    exact div_mul_cancel₀ _ (pow_ne_zero _ hLp.ne')
  have hsmall : b*(2+Real.log (N:ℝ))≤9*Real.pi := by
    calc
      _ ≤ (3*lemma44PaperAlpha D)*(3*lemma23PaperL D^9) :=
        mul_le_mul hbα (by linarith) (by linarith) (by positivity)
      _ = _ := by nlinarith only [hid]
  nlinarith only [mul_le_mul_of_nonneg_right hsmall (by positivity : 0≤Real.log 4)]

/-- Original finite-D ξ convolution mass, at the closed P endpoint. -/
theorem lemma83_original_xi_finite_mass {D : ℕ} {c : ℝ}
    (hL : 3≤lemma23PaperL D) (hc : 0<c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10)
    (j : Fin 3) (d r N : ℕ) (hr : 0<r) (hN : 1≤N)
    (hNP : (N:ℝ)≤lemma23PaperP D) :
    (∑ n∈Icc 1 N,‖lemma83XiMoebius (lemma83PaperBeta D c) j d r n‖/(n:ℝ)) ≤
      lemma83OriginalXiMajorantConstant*((r:ℝ)/(r.totient:ℝ)) := by
  have hLp : 0 < lemma23PaperL D := by linarith
  have hα : 0<lemma44PaperAlpha D := by
    unfold lemma44PaperAlpha lemma23PaperP
    rw [Real.log_exp]
    positivity [Real.pi_pos]
  have hbase := lemma83_xi_moebius_finite_harmonic_bound (lemma83PaperBeta D c)
    (lemma83_beta_re D c) (3*lemma44PaperAlpha D) (by positivity)
    (lemma83_paper_beta_norm hL hc hsmall) j d r N hr
  have hex := lemma83_original_finite_phase_exponent (by linarith : 1≤lemma23PaperL D)
    hN hNP (by positivity : 0≤3*lemma44PaperAlpha D) (le_refl _)
  have he : Real.exp (8+93600000*(3*lemma44PaperAlpha D)*Real.log 4*(2+Real.log (N:ℝ))) ≤
      lemma83OriginalXiMajorantConstant := by
    unfold lemma83OriginalXiMajorantConstant
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_le_mul_of_nonneg_left hex (by norm_num : (0:ℝ)≤93600000)]
  exact hbase.trans (by
    have hh := mul_le_mul_of_nonneg_left he (by positivity : 0≤(r:ℝ)/(r.totient:ℝ))
    simpa only [mul_comm] using hh)

/-- Original finite-D Lambda is uniformly bounded for every positive m≤P. -/
theorem lemma83_original_lambda_finite_bound {D : ℕ} {c : ℝ}
    (hL : 3≤lemma23PaperL D) (hc : 0<c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10)
    (j : Fin 3) (m : ℕ) (hm : 0<m) (hmP : (m:ℝ)≤lemma23PaperP D) :
    ‖lemma83Lambda (lemma83PaperBeta D c) m (1-lemma83PaperBeta D c j)‖ ≤
      lemma83OriginalXiMajorantConstant := by
  have hLp : 0 < lemma23PaperL D := by linarith
  have hα : 0<lemma44PaperAlpha D := by
    unfold lemma44PaperAlpha lemma23PaperP
    rw [Real.log_exp]
    positivity [Real.pi_pos]
  have hbase := lemma83_lambda_finite_shift_bound (lemma83PaperBeta D c)
    (lemma83_beta_re D c) (3*lemma44PaperAlpha D) (by positivity)
    (lemma83_paper_beta_norm hL hc hsmall) j m hm
  have hex := lemma83_original_finite_phase_exponent (by linarith : 1≤lemma23PaperL D)
    (by omega : 1≤m) hmP (by positivity : 0≤3*lemma44PaperAlpha D) (le_refl _)
  apply hbase.trans
  unfold lemma83OriginalXiMajorantConstant
  apply Real.exp_le_exp.mpr
  have hp : 0≤Real.pi*Real.log 4 := by positivity [Real.pi_pos]
  nlinarith only [mul_le_mul_of_nonneg_left hex (by norm_num : (0:ℝ)≤32),hp]

/-- One threshold for the already fixed original shift parameter c. This is an
arithmetic majorant for the original P2.6 transfer, not P2.6 itself. -/
theorem lemma83_original_xi_lambda_majorant :
    ∀ c : ℝ, 0<c → ∃ C : ℝ, 0<C ∧ ∃ D₀ : ℕ, 2≤D₀ ∧
      ∀ D : ℕ, D₀≤D → ∀ j : Fin 3, ∀ d r N : ℕ, 0<d → 0<r →
        (d*r:ℝ)<lemma23PaperP D → 1≤N → (N:ℝ)≤lemma23PaperP D →
        (∑ n∈Icc 1 N,‖lemma83XiMoebius (lemma83PaperBeta D c) j d r n‖/(n:ℝ)) ≤
          C*((r:ℝ)/(r.totient:ℝ)) ∧
        ‖lemma83Lambda (lemma83PaperBeta D c) (d*r) (1-lemma83PaperBeta D c j)‖≤C := by
  intro c hc
  obtain ⟨Dc,_,hsmall⟩ := lemma52_exists_shift_threshold hc
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨D₀,hD₀⟩ := Filter.eventually_atTop.mp (show ∀ᶠ D : ℕ in atTop,
      2≤D ∧ Dc≤D ∧ 3≤lemma23PaperL D from by
    filter_upwards [eventually_ge_atTop (2:ℕ),eventually_ge_atTop Dc,ht.eventually_ge_atTop 3]
      with D h2 hDc hL
    exact ⟨h2,hDc,hL⟩)
  refine ⟨lemma83OriginalXiMajorantConstant,lemma83_original_xi_majorant_constant_pos,
    D₀,(hD₀ D₀ le_rfl).1,?_⟩
  intro D hD j d r N hd hr hdr hN hNP
  have hdata := hD₀ D hD
  refine ⟨lemma83_original_xi_finite_mass hdata.2.2 hc (hsmall D hdata.2.1) j d r N hr hN hNP,?_⟩
  apply lemma83_original_lambda_finite_bound hdata.2.2 hc (hsmall D hdata.2.1) j (d*r)
    (Nat.mul_pos hd hr)
  simpa only [Nat.cast_mul] using hdr.le

/-- The same single-threshold result for a real cutoff X, using the exact floor. -/
theorem lemma83_original_xi_lambda_majorant_real :
    ∀ c : ℝ, 0<c → ∃ C : ℝ, 0<C ∧ ∃ D₀ : ℕ, 2≤D₀ ∧
      ∀ D : ℕ, D₀≤D → ∀ j : Fin 3, ∀ d r : ℕ, 0<d → 0<r →
        (d*r:ℝ)<lemma23PaperP D → ∀ X : ℝ, 1≤X → X≤lemma23PaperP D →
        (∑ n∈Icc 1 ⌊X⌋₊,‖lemma83XiMoebius (lemma83PaperBeta D c) j d r n‖/(n:ℝ)) ≤
          C*((r:ℝ)/(r.totient:ℝ)) ∧
        ‖lemma83Lambda (lemma83PaperBeta D c) (d*r) (1-lemma83PaperBeta D c j)‖≤C := by
  intro c hc
  obtain ⟨C,hC,D₀,hD₀,h⟩ := lemma83_original_xi_lambda_majorant c hc
  refine ⟨C,hC,D₀,hD₀,?_⟩
  intro D hD j d r hd hr hdr X hX hXP
  exact h D hD j d r ⌊X⌋₊ hd hr hdr ((Nat.one_le_floor_iff X).mpr hX)
    ((Nat.floor_le (by linarith : 0≤X)).trans hXP)

end ZhangLS.Spec
