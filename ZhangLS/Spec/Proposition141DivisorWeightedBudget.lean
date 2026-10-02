import ZhangLS.Spec.Proposition141DivisorBounds
import ZhangLS.Spec.Proposition71ConductorWeights

/-! # The exact D₂-weighted divisor budget

The Section14 weight D₂=D/D₁ is retained through the divisor sum. After
exterior Gauss normalization, this costs only a harmonic τ₅ divisor sum
rather than a pointwise bound for τ₆(D).
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Finset
open scoped Classical

theorem proposition141_divisor_tau_five_harmonic {D:ℕ} (hD:1≤D) :
    (∑d∈D.divisors,(lemma34Tau 5 d:ℝ)/(d:ℝ))≤(1+Real.log (D:ℝ))^5 := by
  have hsub : D.divisors⊆Icc 1 D := by
    intro d hd
    have hdiv := (Nat.mem_divisors.mp hd).1
    have hDp : 0<D := by omega
    exact mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos hdiv hDp,Nat.le_of_dvd hDp hdiv⟩
  exact (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _=>by positivity)).trans
    (proposition71_tau_harmonic_bound 5 D hD)

/-- Exact dependence on the complementary divisor D₂. -/
theorem proposition141_complementary_divisor_sum (D:ℕ) :
    (∑d∈D.divisors,(lemma34Tau 5 d:ℝ)*((D/d:ℕ):ℝ))=
      (D:ℝ)*∑d∈D.divisors,(lemma34Tau 5 d:ℝ)/(d:ℝ) := by
  rw [mul_sum]
  apply sum_congr rfl
  intro d hd
  have hdiv := (Nat.mem_divisors.mp hd).1
  have hDp := Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2
  have hdp : 0<(d:ℝ) := by exact_mod_cast Nat.pos_of_dvd_of_pos hdiv hDp
  have he : (d:ℝ)*((D/d:ℕ):ℝ)=(D:ℝ) := by exact_mod_cast Nat.mul_div_cancel' hdiv
  have hq : ((D/d:ℕ):ℝ)=(D:ℝ)/(d:ℝ) :=
    (eq_div_iff hdp.ne').mpr (by simpa only [mul_comm] using he)
  rw [hq]
  ring

theorem proposition141_complementary_divisor_budget {D:ℕ} (hD:1≤D) :
    (∑d∈D.divisors,(lemma34Tau 5 d:ℝ)*((D/d:ℕ):ℝ))≤
      (D:ℝ)*(1+Real.log (D:ℝ))^5 := by
  rw [proposition141_complementary_divisor_sum]
  exact mul_le_mul_of_nonneg_left (proposition141_divisor_tau_five_harmonic hD) (Nat.cast_nonneg D)

/-- Precisely the D₁ divisor budget after D₂/D^(3/2) from the large mean
and 1/sqrt(D) from the exterior Gauss normalization are combined. -/
theorem proposition141_normalized_complementary_divisor_budget {D:ℕ} (hD:0<D) :
    (∑d∈D.divisors,(lemma34Tau 5 d:ℝ)*((D/d:ℕ):ℝ)/(D:ℝ)^2)≤
      (1+Real.log (D:ℝ))^5/(D:ℝ) := by
  have hDp : 0<(D:ℝ) := by exact_mod_cast hD
  rw [←sum_div]
  have hb := div_le_div_of_nonneg_right (proposition141_complementary_divisor_budget (by omega : 1≤D))
    (sq_nonneg (D:ℝ))
  apply hb.trans_eq
  field_simp

end ZhangLS.Spec
