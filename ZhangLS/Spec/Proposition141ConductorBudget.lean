import ZhangLS.Spec.Proposition71CharacterConductorWeights
import ZhangLS.Spec.Proposition141DivisorBudget

/-! # Retained small-conductor arithmetic weights for Section14

The original split r<D³ is kept. The exact D | hr filter is equivalent to
its printed h-congruence. Bounding this positive filtered weight by a full
box is legitimate and keeps the extra D and τ₅(D₁) factors. This is only the
arithmetic budget; the analytic character sum must still be attached.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Finset
open scoped Classical

/-- The printed h ≡ 0 mod D/(D,r) is the exact divisibility condition. -/
theorem proposition141_conductor_congruence {D h r : ℕ} (hD : 0<D) :
    D∣h*r ↔ D/(D.gcd r)∣h := by
  let g := D.gcd r
  have hg : 0<g := Nat.gcd_pos_of_pos_left r hD
  have heD : g*(D/g)=D := Nat.mul_div_cancel' (Nat.gcd_dvd_left D r)
  have her : g*(r/g)=r := Nat.mul_div_cancel' (Nat.gcd_dvd_right D r)
  have hcop : (D/g).Coprime (r/g) := Nat.gcd_div_gcd_div_gcd_of_pos_left hD
  constructor
  · intro hd
    have hh : g*(D/g)∣g*(h*(r/g)) := by simpa only [heD,mul_left_comm g h,her] using hd
    have hq := (Nat.mul_dvd_mul_iff_left hg).mp hh
    exact hcop.dvd_of_dvd_mul_right hq
  · intro hh
    have hq : D/g∣h*(r/g) := dvd_mul_of_dvd_left hh _
    have hm := Nat.mul_dvd_mul_left g hq
    simpa only [heD,mul_left_comm g h,her] using hm

noncomputable def proposition141SmallConductorModuli (D h : ℕ) : Finset ℕ :=
  (Icc 1 (D^3)).filter (fun r => 1<r ∧ r<D^3 ∧ D∣h*r)

/-- Counted positive conductor weight, with the original source filter and
all D₁ and d divisor factors present. -/
theorem proposition141_small_counted_weight_sum (D D₁ X : ℕ) (hX : 1≤X) :
    (∑d∈Icc 1 X, ∑h∈Icc 1 X, ∑r∈proposition141SmallConductorModuli D h,
      (D:ℝ)*(lemma34Tau 5 D₁:ℝ)*(lemma34Tau 5 d:ℝ)*Real.sqrt (r:ℝ)*(r.totient:ℝ)/
        ((d:ℝ)*((h*r).totient:ℝ))) ≤
      (D:ℝ)*(lemma34Tau 5 D₁:ℝ)*((D^3:ℕ):ℝ)^(3/2:ℝ)*(1+Real.log (X:ℝ))^7 := by
  have hsub (h : ℕ) : proposition141SmallConductorModuli D h⊆Icc 1 (D^3) := filter_subset _ _
  calc
    _ ≤ ∑d∈Icc 1 X, ∑h∈Icc 1 X, ∑r∈Icc 1 (D^3),
      (D:ℝ)*(lemma34Tau 5 D₁:ℝ)*(lemma34Tau 5 d:ℝ)*Real.sqrt (r:ℝ)*(r.totient:ℝ)/
        ((d:ℝ)*((h*r).totient:ℝ)) := by
      apply sum_le_sum
      intro d hd
      apply sum_le_sum
      intro h hh
      exact sum_le_sum_of_subset_of_nonneg (hsub h) (fun _ _ _ => by positivity)
    _ = ((D:ℝ)*(lemma34Tau 5 D₁:ℝ))*(∑d∈Icc 1 X, ∑h∈Icc 1 X, ∑r∈Icc 1 (D^3),
      (lemma34Tau 5 d:ℝ)*Real.sqrt (r:ℝ)*(r.totient:ℝ)/((d:ℝ)*((h*r).totient:ℝ))) := by
      simp only [mul_sum]
      apply sum_congr rfl
      intro d hd
      apply sum_congr rfl
      intro h hh
      apply sum_congr rfl
      intro r hr
      ring
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left
        (proposition71_counted_conductor_weight_sum X (D^3) hX)
        (show 0≤(D:ℝ)*(lemma34Tau 5 D₁:ℝ) by positivity)
      simpa only [mul_assoc] using hh

/-- The eighth Mellin height tail pays for the full original D³ conductor
count, with D⁻³ᐟ² left before the exterior Gauss prefactor. -/
theorem proposition141_eighth_counted_tail_identity {D : ℝ} (hD : 0<D) :
    D*(D^3)^(3/2:ℝ)/D^7=D^(-3/2:ℝ) := by
  rw [←Real.rpow_natCast D 3,←Real.rpow_mul hD.le]
  norm_num
  nth_rw 1 [←Real.rpow_one D]
  rw [←Real.rpow_add hD,←Real.rpow_natCast D 7,←Real.rpow_sub hD]
  norm_num

/-- Including |τ(χ)|/D=1/√D leaves D⁻² before the divisor decomposition. -/
theorem proposition141_eighth_gauss_tail_identity {D : ℝ} (hD : 0<D) :
    (D*(D^3)^(3/2:ℝ)/D^7)/Real.sqrt D=D^(-2:ℝ) := by
  rw [proposition141_eighth_counted_tail_identity hD,Real.sqrt_eq_rpow,←Real.rpow_sub hD]
  norm_num

/-- After summing EVERY D₁ divisor, the retained eighth-tail arithmetic
factor still has the explicit saving 32768/D. -/
theorem proposition141_eighth_divisor_tail_budget {D : ℕ} (hD : 0<D) :
    (∑D₁∈D.divisors,(lemma34Tau 5 D₁:ℝ))*
      (((D:ℝ)*((D:ℝ)^3)^(3/2:ℝ)/(D:ℝ)^7)/Real.sqrt (D:ℝ)) ≤32768/(D:ℝ) := by
  have hDp : 0<(D:ℝ) := by exact_mod_cast hD
  rw [proposition141_eighth_gauss_tail_identity hDp]
  have hh := mul_le_mul_of_nonneg_right (proposition141_divisor_tau_five_budget D)
    (Real.rpow_nonneg hDp.le (-2:ℝ))
  apply hh.trans_eq
  rw [show (-2:ℝ)=-(2:ℝ) by norm_num,Real.rpow_neg hDp.le]
  rw [Real.rpow_two]
  field_simp

end ZhangLS.Spec
