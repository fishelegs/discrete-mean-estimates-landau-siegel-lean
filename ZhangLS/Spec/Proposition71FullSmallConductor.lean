import ZhangLS.Spec.Proposition71SigmaTruncation
import ZhangLS.Spec.Proposition71LargeLTailAggregate
import ZhangLS.Spec.Proposition71ConductorAggregateOrder
import ZhangLS.Spec.Proposition71QuarterConductorSaving

/-! # The genuine untruncated small-conductor component of (7.13) -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset
open scoped Classical
set_option maxHeartbeats 3000000

noncomputable def proposition71ActualSmallConductorAggregate (D : ℕ) (c b : ℝ)
    (a : ℕ → ℂ) : ℝ :=
  proposition71ConductorNormAggregate ⌊lemma23PaperP D⌋₊ ⌊(D : ℝ)^(1/4 : ℝ)⌋₊
    (fun d h r => ((d*h*r : ℕ) : ℝ)<lemma81Cutoff D)
    (fun d h _ θ => proposition71SigmaSeries D c b a h d θ)

lemma proposition71_strict_truncated_aggregate_le (D : ℕ) (c b : ℝ)
    (a : ℕ → ℂ) (X Q : ℕ) :
    proposition71ConductorNormAggregate X Q (fun d h r => ((d*h*r : ℕ) : ℝ)<lemma81Cutoff D)
      (fun d h _ θ => proposition71SigmaTruncated D c b a h d θ)≤
        proposition71SmallConductorAggregate D c b a X Q := by
  unfold proposition71ConductorNormAggregate proposition71SmallConductorAggregate
  apply sum_le_sum; intro d hd
  apply sum_le_sum; intro h hh
  apply sum_le_sum; intro r hr
  split
  · exact le_rfl
  · positivity

lemma proposition71_D_le_P {D : ℕ} (hD : 1<D) (hL : 1≤lemma23PaperL D) :
    (D : ℝ)≤lemma23PaperP D := by
  have hDp : 0<(D : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hD
  have hh : lemma23PaperL D≤lemma23PaperL D^9 := by
    simpa only [pow_one] using pow_le_pow_right₀ hL (by norm_num : 1≤(9:ℕ))
  calc
    _=Real.exp (lemma23PaperL D) := by rw [lemma23PaperL,Real.exp_log hDp]
    _≤Real.exp (lemma23PaperL D^9) := Real.exp_le_exp.mpr hh
    _=_ := rfl

theorem proposition71_actual_small_conductor_power_saving :
    ∃ C : ℝ, 0<C ∧ ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ → ∀ c b B : ℝ, 0≤B →
        |b|≤(D : ℝ)/2 → ∀ a : ℕ → ℂ, (∀n, ‖a n‖≤B) →
          proposition71ActualSmallConductorAggregate D c b a≤
            C*B*lemma56PrimeMass D*(D : ℝ)^(-1/2 : ℝ) := by
  obtain ⟨Cm,hCm,Dm,hDm,hmain⟩ := proposition71_quarter_small_conductor_power_saving
  obtain ⟨Ce,hCe,De,hDe,herror⟩ := proposition71_large_l_tail_aggregate_bound
  obtain ⟨Ds,hDs,hsum⟩ := proposition71_sigma_series_summable
  refine ⟨Cm+Ce,add_pos hCm hCe,
    max Dm (max De (max Ds ⌈Real.exp 2000⌉₊)),hDm.trans (le_max_left _ _),?_⟩
  intro D hDN χ hA c b B hB hb a ha
  have hm := (le_max_left _ _).trans hDN
  have he := (le_max_left _ _).trans ((le_max_right _ _).trans hDN)
  have hs := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hDN))
  have hExp := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hDN))
  have hD2 : 2≤D := hDm.trans hm
  have hD1 : 1≤(D : ℝ) := by exact_mod_cast (show 1≤D by omega)
  have hL : 2000≤lemma23PaperL D := by
    have hex : Real.exp 2000≤(D : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hExp)
    simpa [lemma23PaperL] using Real.log_le_log (Real.exp_pos 2000) hex
  have hP : 1≤lemma23PaperP D := Real.one_le_exp_iff.mpr (pow_nonneg (by linarith : 0≤lemma23PaperL D) 9)
  let X := ⌊lemma23PaperP D⌋₊
  let Q := ⌊(D : ℝ)^(1/4 : ℝ)⌋₊
  have hX : 1≤X := Nat.le_floor (by simpa only [Nat.cast_one] using hP)
  have hXP : (X : ℝ)≤lemma23PaperP D := Nat.floor_le (by positivity)
  have hQ : (Q : ℝ)≤(D : ℝ)^(1/4 : ℝ) := Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg D) _)
  have hQP : (Q : ℝ)≤lemma23PaperP D := by
    have hd : (D : ℝ)^(1/4 : ℝ)≤D := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hD1 (by norm_num : (1/4 : ℝ)≤1)
    exact hQ.trans (hd.trans (proposition71_D_le_P (by omega) (by linarith)))
  have ht := hmain D hm χ hA c b B hB hb a ha X Q hX hXP hQ
  have he' := herror D he (by omega) hL c b B hB a ha X Q hX hXP hQP
  have hsplit : proposition71ActualSmallConductorAggregate D c b a≤
      proposition71ConductorNormAggregate X Q (fun d h r => ((d*h*r : ℕ) : ℝ)<lemma81Cutoff D)
        (fun d h _ θ => proposition71SigmaTruncated D c b a h d θ)+
          proposition71LargeLTailAggregate D c b a X Q := by
    apply proposition71_conductor_aggregate_le_add X Q _ _ _ _
    intro d hd h hh r hr hcut θ hθ
    have hseries := hsum θ hs (by omega) hL c b B hB a ha h d (mem_Icc.mp hh).1
      (by have := (mem_Icc.mp hr).1; omega) (proposition71_hr_le_cutoff_of_dhr (mem_Icc.mp hd).1 hcut)
    rw [proposition71_sigma_exact_truncation c b a h d θ hseries]
    exact norm_add_le _ _
  have hi : (D : ℝ)⁻¹≤(D : ℝ)^(-1/2 : ℝ) := by
    have hh := Real.rpow_le_rpow_of_exponent_le hD1 (by norm_num : (-1 : ℝ)≤-1/2)
    simpa only [Real.rpow_neg_one] using hh
  have hM := lemma56_prime_mass_nonneg D
  calc
    _≤proposition71SmallConductorAggregate D c b a X Q+proposition71LargeLTailAggregate D c b a X Q :=
      hsplit.trans (add_le_add (proposition71_strict_truncated_aggregate_le D c b a X Q) le_rfl)
    _≤Cm*B*lemma56PrimeMass D*(D : ℝ)^(-1/2 : ℝ)+Ce*B*lemma56PrimeMass D/(D : ℝ) := add_le_add ht he'
    _≤_ := by
      have hh := mul_le_mul_of_nonneg_left hi (by positivity : 0≤Ce*B*lemma56PrimeMass D)
      rw [←div_eq_mul_inv] at hh
      nlinarith only [hh]

end ZhangLS.Spec
