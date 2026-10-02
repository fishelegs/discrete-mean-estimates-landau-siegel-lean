import ZhangLS.Spec.Proposition71DivisorWeights

/-! # Explicit outer conductor/totient weights in the repaired small-conductor split

No reciprocal-totient or divisor factors are absorbed into an unexplained
constant. This is the actual weight left by (7.13) after a single-conductor
σ bound and the elementary character-count bound.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset
open scoped Classical
set_option maxHeartbeats 2000000

lemma proposition71_tau_harmonic_bound (k X : ℕ) (hX : 1≤X) :
    (∑ n∈Icc 1 X, (lemma34Tau k n : ℝ)/(n : ℝ))≤(1+Real.log (X : ℝ))^k := by
  have hH : 0≤(harmonic X : ℝ) := by
    simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
    exact sum_nonneg (fun _ _ => by positivity)
  have hh := lemma34_tau_weighted_sum_le_harmonic_pow k X hX
  simp only [div_eq_mul_inv]
  exact hh.trans (pow_le_pow_left₀ hH (harmonic_le_one_add_log X) k)

/-- Explicit triple weight sum, including all common-prime effects in φ(hr). -/
theorem proposition71_small_conductor_weight_sum (X Q : ℕ) (hX : 1≤X) (hQ : 1≤Q) :
    (∑ d∈Icc 1 X, ∑ h∈Icc 1 X, ∑ r∈Icc 1 Q,
      (lemma34Tau 5 d : ℝ)*(r : ℝ)^(3/2 : ℝ)/((d : ℝ)*(Nat.totient (h*r) : ℝ))) ≤
        (Q : ℝ)^(3/2 : ℝ)*(1+Real.log (X : ℝ))^7*(1+Real.log (Q : ℝ))^2 := by
  have hterm {d h r : ℕ} (hd : d∈Icc 1 X) (hh : h∈Icc 1 X) (hr : r∈Icc 1 Q) :
      (lemma34Tau 5 d : ℝ)*(r : ℝ)^(3/2 : ℝ)/((d : ℝ)*(Nat.totient (h*r) : ℝ)) ≤
        ((lemma34Tau 5 d : ℝ)/(d : ℝ))*((lemma34Tau 2 h : ℝ)/(h : ℝ))*
          ((lemma34Tau 2 r : ℝ)/(r : ℝ))*(Q : ℝ)^(3/2 : ℝ) := by
    have hdp : 0<d := (mem_Icc.mp hd).1
    have hhp : 0<h := (mem_Icc.mp hh).1
    have hrp : 0<r := (mem_Icc.mp hr).1
    have hb := proposition71_reciprocal_product_totient hhp hrp
    have hrQ : (r : ℝ)^(3/2 : ℝ)≤(Q : ℝ)^(3/2 : ℝ) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast (mem_Icc.mp hr).2) (by norm_num)
    calc
      _=((lemma34Tau 5 d : ℝ)/(d : ℝ))*(r : ℝ)^(3/2 : ℝ)*(Nat.totient (h*r) : ℝ)⁻¹ := by ring
      _≤((lemma34Tau 5 d : ℝ)/(d : ℝ))*(r : ℝ)^(3/2 : ℝ)*
          ((lemma34Tau 2 h : ℝ)*(lemma34Tau 2 r : ℝ)/((h : ℝ)*(r : ℝ))) := by gcongr
      _=((lemma34Tau 5 d : ℝ)/(d : ℝ))*((lemma34Tau 2 h : ℝ)/(h : ℝ))*
          ((lemma34Tau 2 r : ℝ)/(r : ℝ))*(r : ℝ)^(3/2 : ℝ) := by ring
      _≤_ := by gcongr
  calc
    _≤∑ d∈Icc 1 X, ∑ h∈Icc 1 X, ∑ r∈Icc 1 Q,
        ((lemma34Tau 5 d : ℝ)/(d : ℝ))*((lemma34Tau 2 h : ℝ)/(h : ℝ))*
          ((lemma34Tau 2 r : ℝ)/(r : ℝ))*(Q : ℝ)^(3/2 : ℝ) := by
      apply sum_le_sum
      intro d hd
      apply sum_le_sum
      intro h hh
      exact sum_le_sum (fun r hr => hterm hd hh hr)
    _=(∑ d∈Icc 1 X, (lemma34Tau 5 d : ℝ)/(d : ℝ))*
        (∑ h∈Icc 1 X, (lemma34Tau 2 h : ℝ)/(h : ℝ))*
        (∑ r∈Icc 1 Q, (lemma34Tau 2 r : ℝ)/(r : ℝ))*(Q : ℝ)^(3/2 : ℝ) := by
      simp only [←sum_mul,←mul_sum]
    _≤(1+Real.log (X : ℝ))^5*(1+Real.log (X : ℝ))^2*
        (1+Real.log (Q : ℝ))^2*(Q : ℝ)^(3/2 : ℝ) := by
      have hd := proposition71_tau_harmonic_bound 5 X hX
      have hh := proposition71_tau_harmonic_bound 2 X hX
      have hr := proposition71_tau_harmonic_bound 2 Q hQ
      have hd0 : 0≤∑ d∈Icc 1 X, (lemma34Tau 5 d : ℝ)/(d : ℝ) := sum_nonneg (fun _ _ => by positivity)
      have hh0 : 0≤∑ h∈Icc 1 X, (lemma34Tau 2 h : ℝ)/(h : ℝ) := sum_nonneg (fun _ _ => by positivity)
      have hr0 : 0≤∑ r∈Icc 1 Q, (lemma34Tau 2 r : ℝ)/(r : ℝ) := sum_nonneg (fun _ _ => by positivity)
      gcongr
    _=_ := by ring

/-- A smaller *internal* conductor split absorbs the genuine 1/D Mellin tail.
This changes no coefficient, arithmetic sum, or final proposition statement. -/
theorem proposition71_quarter_split_small_budget {D Q : ℝ}
    (hD : 0<D) (hQ : 0≤Q) (hQD : Q≤D^(1/4 : ℝ)) :
    Q^(3/2 : ℝ)/D≤D^(-5/8 : ℝ) := by
  have hh := Real.rpow_le_rpow hQ hQD (by norm_num : (0:ℝ)≤3/2)
  rw [←Real.rpow_mul hD.le] at hh
  norm_num at hh
  apply (div_le_div_of_nonneg_right hh hD.le).trans_eq
  calc
    D^(3/8 : ℝ)/D=D^(3/8 : ℝ)/D^(1 : ℝ) := by rw [Real.rpow_one]
    _=D^(-5/8 : ℝ) := by rw [←Real.rpow_sub hD]; norm_num

/-- The matching large-conductor lower endpoint still gives a power saving. -/
theorem proposition71_quarter_split_large_budget {D R : ℝ}
    (hD : 0<D) (hR : D^(1/4 : ℝ)≤R) :
    R^(-1/2 : ℝ)≤D^(-1/8 : ℝ) := by
  have hh := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hD _) hR (by norm_num : (-1/2 : ℝ)≤0)
  rw [←Real.rpow_mul hD.le] at hh
  norm_num at hh
  convert hh using 1 <;> norm_num

end ZhangLS.Spec
