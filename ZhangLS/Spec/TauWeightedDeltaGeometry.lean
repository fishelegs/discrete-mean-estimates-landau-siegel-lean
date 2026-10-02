import ZhangLS.Spec.Proposition71DeltaLargeTail
import ZhangLS.Spec.Proposition71ConductorWeights
import ZhangLS.Spec.TauDirichletValues
import ZhangLS.Spec.Lemma53MellinIdentity

/-! # Genuine global Δ envelope and the absolute τ₅-sum geometry

Only actual Lemma5.3, divisor arithmetic and the convergent τ₅ Dirichlet
series are used. There is no discrete-mean proposition input.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

noncomputable def tauDeltaUniformConstant : ℝ := Real.sqrt Real.pi*Real.exp 1

lemma tauDelta_uniform_constant_pos : 0<tauDeltaUniformConstant := by
  unfold tauDeltaUniformConstant
  exact mul_pos (Real.sqrt_pos.mpr Real.pi_pos) (Real.exp_pos _)

theorem tauDelta_actual_uniform_bound {D:ℕ} (hD:1<D) (hL:1≤lemma23PaperL D)
    {x:ℝ} (hx:0<x) : ‖lemma53PaperDelta D x‖≤tauDeltaUniformConstant := by
  have hB1 : 1≤lemma53PaperScale D := one_le_pow₀ hL
  have hB : 0<lemma53PaperScale D := lt_of_lt_of_le zero_lt_one hB1
  have hden : 1≤16*lemma53PaperScale D^2 := by nlinarith only [hB1,sq_nonneg (lemma53PaperScale D-1)]
  have hex : 1/(16*lemma53PaperScale D^2)≤1 := (div_le_one (by positivity)).mpr hden
  exact (lemma53_paper_delta_norm_bound hD hx).trans (mul_le_mul
    (div_le_self (Real.sqrt_nonneg _) hB1) (Real.exp_le_exp.mpr hex)
    (Real.exp_nonneg _) (Real.sqrt_nonneg _))

lemma tauDelta_tau_five_partial_sum (X:ℕ) (hX:1≤X) :
    (∑n∈Icc 1 X,(lemma34Tau 5 n:ℝ))≤(X:ℝ)*(1+Real.log (X:ℝ))^5 := by
  calc
    _≤∑n∈Icc 1 X,(X:ℝ)*((lemma34Tau 5 n:ℝ)/(n:ℝ)) := by
      apply sum_le_sum
      intro n hn
      have hnp : 0<(n:ℝ) := by exact_mod_cast (mem_Icc.mp hn).1
      calc
        _=(n:ℝ)*((lemma34Tau 5 n:ℝ)/(n:ℝ)) := by field_simp
        _≤_ := mul_le_mul_of_nonneg_right (by exact_mod_cast (mem_Icc.mp hn).2) (by positivity)
    _=(X:ℝ)*∑n∈Icc 1 X,(lemma34Tau 5 n:ℝ)/(n:ℝ) := by rw [mul_sum]
    _≤_ := mul_le_mul_of_nonneg_left (proposition71_tau_harmonic_bound 5 X hX) (Nat.cast_nonneg X)

lemma tauDelta_t0_cutoff {D:ℕ} (hL:1≤lemma23PaperL D) :
    lemma51PaperT0 D^(51/50:ℝ)≤lemma23PaperL D^530 := by
  have hL0 : 0≤lemma23PaperL D := by linarith
  rw [lemma51PaperT0,←Real.rpow_natCast,←Real.rpow_mul hL0,←Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num)

/-- The full logarithm of the genuine q-scaled cutoff is paid for. -/
lemma tauDelta_head_geometry {D:ℕ} (hL:2000≤lemma23PaperL D) {q:ℝ}
    (hq:1≤q) (hqP:q≤lemma23PaperP D^10) :
    1≤⌊q*lemma23PaperL D^530⌋₊ ∧
      (⌊q*lemma23PaperL D^530⌋₊:ℝ)*(1+Real.log (⌊q*lemma23PaperL D^530⌋₊:ℝ))^5 ≤
        12^5*q*lemma23PaperL D^575 := by
  have hL1 : 1≤lemma23PaperL D := by linarith
  have hLp : 0<lemma23PaperL D := by linarith
  have hqp : 0<q := lt_of_lt_of_le zero_lt_one hq
  have hU : 1≤q*lemma23PaperL D^530 := by
    have hh : 1≤lemma23PaperL D^530 := one_le_pow₀ hL1
    have hm := mul_le_mul_of_nonneg_right hq (pow_nonneg hLp.le 530)
    simp only [one_mul] at hm
    exact hh.trans hm
  have hX : 1≤⌊q*lemma23PaperL D^530⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using hU)
  refine ⟨hX,?_⟩
  have hXp : 0<(⌊q*lemma23PaperL D^530⌋₊:ℝ) := by exact_mod_cast (show 0<⌊q*lemma23PaperL D^530⌋₊ by omega)
  have hXU : (⌊q*lemma23PaperL D^530⌋₊:ℝ)≤q*lemma23PaperL D^530 := Nat.floor_le (by positivity)
  have hlogq : Real.log q≤10*lemma23PaperL D^9 := by
    simpa only [Real.log_pow,lemma23PaperP,Real.log_exp,Nat.cast_ofNat] using Real.log_le_log hqp hqP
  have hL8 : 530≤lemma23PaperL D^8 := by
    have hh := le_self_pow₀ hL1 (by norm_num : 8≠0)
    linarith
  have hlogL : 530*Real.log (lemma23PaperL D)≤lemma23PaperL D^9 := by
    have hlog := Real.log_le_sub_one_of_pos hLp
    have hh := mul_le_mul_of_nonneg_right hL8 hLp.le
    calc
      _≤530*lemma23PaperL D := by linarith
      _≤lemma23PaperL D^8*lemma23PaperL D := hh
      _=_ := by ring
  have hlogX : Real.log (⌊q*lemma23PaperL D^530⌋₊:ℝ)≤11*lemma23PaperL D^9 := by
    apply (Real.log_le_log hXp hXU).trans
    rw [Real.log_mul hqp.ne' (pow_pos hLp _).ne',Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith
  have hlog0 : 0≤1+Real.log (⌊q*lemma23PaperL D^530⌋₊:ℝ) := by
    have := Real.log_natCast_nonneg ⌊q*lemma23PaperL D^530⌋₊
    linarith
  have hb : 1+Real.log (⌊q*lemma23PaperL D^530⌋₊:ℝ)≤12*lemma23PaperL D^9 := by
    have := one_le_pow₀ hL1 (n:=9)
    linarith
  calc
    _≤(q*lemma23PaperL D^530)*(12*lemma23PaperL D^9)^5 := by gcongr
    _=_ := by ring

/-- The q² tail scale is retained until the actual exponential absorbs one
factor q, under the explicit q≤P^10 range. -/
lemma tauDelta_tail_scale {D:ℕ} (hL:2000≤lemma23PaperL D) {q:ℝ}
    (hq:0≤q) (hqP:q≤lemma23PaperP D^10) :
    Real.exp (-lemma23PaperL D^10/2)*q^2≤q := by
  have hL0 : 0≤lemma23PaperL D := by linarith
  have he : Real.exp (-lemma23PaperL D^10/2)*lemma23PaperP D^10≤1 := by
    rw [lemma23PaperP,←Real.exp_nat_mul,←Real.exp_add]
    apply Real.exp_le_one_iff.mpr
    have hh := mul_le_mul_of_nonneg_right (show (20:ℝ)≤lemma23PaperL D by linarith) (pow_nonneg hL0 9)
    have hm : lemma23PaperL D*lemma23PaperL D^9=lemma23PaperL D^10 := by ring
    rw [hm] at hh
    norm_num only [Nat.cast_ofNat]
    linarith
  have hsmall : Real.exp (-lemma23PaperL D^10/2)*q≤1 :=
    (mul_le_mul_of_nonneg_left hqP (Real.exp_nonneg _)).trans he
  have hb := mul_le_mul_of_nonneg_right hsmall hq
  simpa only [one_mul,mul_assoc,pow_two] using hb

end ZhangLS.Spec
