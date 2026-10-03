import ZhangLS.Spec.Proposition141OffLocalGeometry
import ZhangLS.Spec.Proposition141TailGeometry
import ZhangLS.Spec.Proposition141PrimeInfiniteTail

/-! # The actual omitted-interval prime kernel, including its entire l tail

Both branches are genuine Δ envelopes. The finite branch is off-center;
the infinite branch retains (phr)² before source support bounds it by4P⁴.
The full complex p^β is kept and its norm used only for this negligible tail.
-/
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical ComplexConjugate

noncomputable def proposition141OffLocalDeltaConstant : ℝ :=
  proposition71OffCenterDeltaConstant+4*proposition71LargeDeltaTailConstant

lemma proposition141_offlocal_delta_constant_pos : 0<proposition141OffLocalDeltaConstant := by
  unfold proposition141OffLocalDeltaConstant
  have := proposition71_offcenter_delta_constant_pos
  have := proposition71_large_delta_tail_constant_pos
  positivity

lemma proposition141_actual_offlocal_delta_quadratic {D p r h l:ℕ} {R:ℝ}
    (hD:1<D) (hL:2000≤lemma23PaperL D) (hR:1≤R) (hh:0<h)
    (hr:r∈primitiveDyadicModuli R) (hp:p∈lemma56PaperPrimes D)
    (hhr:((h*r:ℕ):ℝ)≤lemma23PaperP D) (hl:0<l) (hc:l.Coprime h)
    (hnot:l∉proposition141LocalizedIndices D R h) :
    ‖lemma53PaperDelta D ((l:ℝ)/((p:ℝ)*(h:ℝ)*(r:ℝ)))‖≤
      proposition141OffLocalDeltaConstant*Real.exp (-lemma23PaperL D^10/2)*lemma23PaperP D^6/(l:ℝ)^2 := by
  have hP : 0≤lemma23PaperP D := (Real.exp_pos _).le
  have hP1 : 1≤lemma23PaperP D := Real.one_le_exp (by have := Real.log_natCast_nonneg D; positivity)
  have hhr' : (h:ℝ)*(r:ℝ)≤lemma23PaperP D := by simpa only [Nat.cast_mul] using hhr
  have hhp:0<(h:ℝ) := by exact_mod_cast hh
  have hrp:0<(r:ℝ) := by exact_mod_cast (show 0<r from Nat.zero_lt_of_lt (mem_primitiveDyadicModuli.mp hr).1)
  have hpp:0<(p:ℝ) := by exact_mod_cast ((lemma56_mem_paper_primes D p).mp hp).1.pos
  have hlp:0<(l:ℝ) := by exact_mod_cast hl
  have hC := proposition71_large_delta_tail_constant_pos.le
  have hO := proposition71_offcenter_delta_constant_pos.le
  have hE := (Real.exp_pos (-lemma23PaperL D^10/2)).le
  have hCtot := proposition141_offlocal_delta_constant_pos.le
  by_cases hlP:(l:ℝ)≤lemma23PaperP D^3
  · have hδ := proposition141_actual_offlocalized_delta hD hL hR hh hr hp hl hc hnot
    have hl2 : (l:ℝ)^2≤lemma23PaperP D^6 := by
      have hs := pow_le_pow_left₀ hlp.le hlP 2
      simpa only [←pow_mul] using hs
    have hC' : proposition71OffCenterDeltaConstant≤proposition141OffLocalDeltaConstant := by
      unfold proposition141OffLocalDeltaConstant
      linarith
    apply hδ.trans
    apply (le_div_iff₀ (sq_pos_of_pos hlp)).mpr
    calc
      _≤proposition71OffCenterDeltaConstant*Real.exp (-lemma23PaperL D^10/2)*lemma23PaperP D^6 := by gcongr
      _≤_ := by gcongr
  · have hlbig : lemma23PaperP D^3<(l:ℝ) := lt_of_not_ge hlP
    have hpmax : (p:ℝ)≤2*lemma23PaperP D :=
      (proposition141_paper_prime_le_three_halves_P (by linarith) hp).trans (by nlinarith only [hP])
    have hq : (p:ℝ)*(h:ℝ)*(r:ℝ)≤2*lemma23PaperP D*(h:ℝ)*(r:ℝ) := by gcongr
    have htail : ((p:ℝ)*(h:ℝ)*(r:ℝ))*lemma51PaperT0 D^(51/50:ℝ)<(l:ℝ) := by
      have ht : 0≤lemma51PaperT0 D^(51/50:ℝ) := Real.rpow_nonneg (pow_nonneg (by linarith : 0≤lemma23PaperL D) _) _
      exact ((mul_le_mul_of_nonneg_right hq ht).trans
        (proposition141_actual_P_cube_tail_cutoff hL hhp.le hrp.le hhr')).trans_lt hlbig
    have hδ := proposition141_scaled_large_delta_tail hD hL (by positivity : 0<(p:ℝ)*(h:ℝ)*(r:ℝ)) htail
    have hqP : (p:ℝ)*(h:ℝ)*(r:ℝ)≤2*lemma23PaperP D^2 := by
      apply hq.trans
      have hb := mul_le_mul_of_nonneg_left hhr' (show 0≤2*lemma23PaperP D by positivity)
      convert hb using 1 <;> ring
    have hq2 : ((p:ℝ)*(h:ℝ)*(r:ℝ))^2≤4*lemma23PaperP D^6 := by
      have hb := pow_le_pow_left₀ (by positivity : 0≤(p:ℝ)*(h:ℝ)*(r:ℝ)) hqP 2
      have h46 : lemma23PaperP D^4≤lemma23PaperP D^6 := pow_le_pow_right₀ hP1 (by norm_num)
      calc
        _≤(2*lemma23PaperP D^2)^2 := hb
        _=4*lemma23PaperP D^4 := by ring
        _≤_ := mul_le_mul_of_nonneg_left h46 (by norm_num)
    apply hδ.trans
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    calc
      _≤proposition71LargeDeltaTailConstant*Real.exp (-lemma23PaperL D^10/2)*(4*lemma23PaperP D^6) := by gcongr
      _≤_ := by unfold proposition141OffLocalDeltaConstant; nlinarith only [mul_nonneg (mul_nonneg hO hE) (pow_nonneg hP 6)]

/-- The actual prime kernel with χ·conj(θ) and full complex β. -/
theorem proposition141_offlocal_prime_kernel_bound {D N r h l:ℕ} {R:ℝ}
    (χ:RealPrimitiveCharacter D) (θ:DirichletCharacter ℂ N)
    (hD:1<D) (hL:2000≤lemma23PaperL D) {β:ℂ} (hβ:‖β‖<5*lemma44PaperAlpha D)
    (hR:1≤R) (hh:0<h) (hr:r∈primitiveDyadicModuli R)
    (hhr:((h*r:ℕ):ℝ)≤lemma23PaperP D) (hl:0<l) (hc:l.Coprime h)
    (hnot:l∉proposition141LocalizedIndices D R h) :
    ‖proposition141ActualShiftedPrimeKernel χ θ β h r l‖≤
      (Real.exp 40*proposition141OffLocalDeltaConstant)*Real.exp (-lemma23PaperL D^10/2)*
        lemma23PaperP D^6*lemma56PrimeMass D/(l:ℝ)^2 := by
  let K := proposition141OffLocalDeltaConstant*Real.exp (-lemma23PaperL D^10/2)*lemma23PaperP D^6/(l:ℝ)^2
  have hK : 0≤K := by dsimp [K]; have := proposition141_offlocal_delta_constant_pos; positivity
  have hb : ‖proposition141ActualShiftedPrimeKernel χ θ β h r l‖≤
      ((lemma56PaperPrimes D).card:ℝ)*(Real.exp 40*K) := by
    unfold proposition141ActualShiftedPrimeKernel
    apply (norm_sum_le _ _).trans
    calc
      _≤∑p∈lemma56PaperPrimes D,Real.exp 40*K := by
        apply sum_le_sum
        intro p hp
        rw [norm_mul]
        exact mul_le_mul (proposition141_prime_tail_shift_norm χ θ hL hβ hp)
          (proposition141_actual_offlocal_delta_quadratic hD hL hR hh hr hp hhr hl hc hnot)
          (norm_nonneg _) (Real.exp_nonneg _)
      _=_ := by simp
  apply hb.trans
  have hs := mul_le_mul_of_nonneg_right (proposition141_prime_card_le_mass D) (show 0≤Real.exp 40*K by positivity)
  convert hs using 1; dsimp [K]; ring

end ZhangLS.Spec
