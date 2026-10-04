import ZhangLS.Spec.RamifiedHeadHarmonicReindex
import ZhangLS.Spec.RamifiedHeadHarmonicTau
import ZhangLS.Spec.RamifiedHeadHarmonicMajorants

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Finset
open scoped Classical

lemma ramifiedHead_nu_weight_mul {D q : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 0 < D) (hqD : q ∣ D) (n : ℕ) :
    ramifiedHeadNuWeight χ (q*n) ≤
      ((lemma34Tau 4 q : ℝ)/(q : ℝ))*ramifiedHeadNuWeight χ n := by
  unfold ramifiedHeadNuWeight
  rw [ramifiedHead_nu_mul_divisor χ hD.ne' hqD, Nat.cast_mul]
  calc
    _ ≤ ‖lemma23NuArithmeticFunction χ n‖ *
        ((lemma34Tau 4 q : ℝ)*(lemma34Tau 4 n : ℝ))/((q : ℝ)*(n : ℝ)) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left (ramified_tau_mul_le_real 4 q n (by omega)) (norm_nonneg _)
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

lemma ramifiedHead_nu_pair_fibre_le {D X : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 0 < D) {dm : ℕ × ℕ} (hdm : dm ∈ ramifiedHeadPairs D X) :
    let t := ramifiedHeadSplit D dm
    ramifiedHeadNuWeight χ dm.1 * ramifiedHeadNuWeight χ dm.2 ≤
      ((lemma34Tau 4 t.1 : ℝ)*(lemma34Tau 4 (D/t.1) : ℝ)/(D : ℝ)) *
        ramifiedHeadNuWeight χ t.2.1 * ramifiedHeadNuWeight χ t.2.2 := by
  let t := ramifiedHeadSplit D dm
  have ht := ramifiedHead_split_data hD hdm
  have hgD : t.1 ∣ D := (Nat.mem_divisors.mp ht.1).1
  have hqD : D/t.1 ∣ D := Nat.div_dvd_of_dvd hgD
  have hgq : t.1*(D/t.1)=D := Nat.mul_div_cancel' hgD
  have hh := mul_le_mul
    (ramifiedHead_nu_weight_mul χ hD hgD t.2.1)
    (ramifiedHead_nu_weight_mul χ hD hqD t.2.2)
    (ramifiedHead_nu_weight_nonneg χ _)
    (mul_nonneg (by positivity) (ramifiedHead_nu_weight_nonneg χ _))
  rw [ht.2.2.2.1, ht.2.2.2.2] at hh
  apply hh.trans_eq
  have hgqR : (t.1 : ℝ)*(D/t.1 : ℕ)=D := by exact_mod_cast hgq
  change _ = ((lemma34Tau 4 t.1 : ℝ)*(lemma34Tau 4 (D/t.1) : ℝ)/(D : ℝ)) * _ * _
  rw [← hgqR]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The stronger positive νν estimate; no character or conductor coprimality
restriction on either summation index is used. -/
theorem ramifiedHead_nu_pair_harmonic_le {D X : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 0 < D) (hX : 1 ≤ X) :
    (∑ dm ∈ ramifiedHeadPairs D X,
      ramifiedHeadNuWeight χ dm.1 * ramifiedHeadNuWeight χ dm.2) ≤
      (lemma34Tau 8 D : ℝ)/(D : ℝ) * (harmonic X : ℝ)^16 := by
  let S := ∑ n ∈ Icc 1 X, ramifiedHeadNuWeight χ n
  have hS : 0 ≤ S := sum_nonneg (fun n _ => ramifiedHead_nu_weight_nonneg χ n)
  calc
    _ ≤ ∑ g ∈ D.divisors, ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
        ((lemma34Tau 4 g : ℝ)*(lemma34Tau 4 (D/g) : ℝ)/(D : ℝ)) *
          ramifiedHeadNuWeight χ a * ramifiedHeadNuWeight χ b := by
      apply ramifiedHead_reindex_le hD
      · intro g hg a ha b hb
        exact mul_nonneg (mul_nonneg (by positivity)
          (ramifiedHead_nu_weight_nonneg χ a)) (ramifiedHead_nu_weight_nonneg χ b)
      · intro dm hdm
        exact ramifiedHead_nu_pair_fibre_le χ hD hdm
    _ = ((∑ g ∈ D.divisors,
        (lemma34Tau 4 g : ℝ)*(lemma34Tau 4 (D/g) : ℝ))/(D : ℝ))*S^2 := by
      dsimp only [S]
      simp only [← mul_sum, ← sum_mul, sum_div]
      ring
    _ = (lemma34Tau 8 D : ℝ)/(D : ℝ)*S^2 := by rw [ramified_tau_four_convolution]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc
        S^2 ≤ ((harmonic X : ℝ)^8)^2 :=
          pow_le_pow_left₀ hS (ramifiedHead_nu_weight_harmonic_le χ X hX) 2
        _ = _ := by ring

/-- The actual upsilon-nu pair is dominated before any summation restrictions
are dropped. -/
lemma ramifiedHead_actual_pair_le {D : ℕ} (χ : RealPrimitiveCharacter D) (d m : ℕ) :
    ‖lemma23UpsilonArithmeticFunction χ d‖ * ‖lemma23NuArithmeticFunction χ m‖ *
      (lemma34Tau 4 d : ℝ) * (lemma34Tau 4 m : ℝ) / ((d : ℝ)*(m : ℝ)) ≤
        ramifiedHeadNuWeight χ d * ramifiedHeadNuWeight χ m := by
  calc
    _ ≤ ‖lemma23NuArithmeticFunction χ d‖ * ‖lemma23NuArithmeticFunction χ m‖ *
        (lemma34Tau 4 d : ℝ) * (lemma34Tau 4 m : ℝ) / ((d : ℝ)*(m : ℝ)) := by
      gcongr
      exact ramifiedHead_upsilon_norm_le_nu χ d
    _ = _ := by
      simp only [ramifiedHeadNuWeight, div_eq_mul_inv, mul_inv_rev]
      ring

/-- Constant-one, conductor-uniform finite harmonic bound for the actual
ramified equality arithmetic coefficients. No assumption (A) is used. -/
theorem ramifiedHead_actual_harmonic_le {D X : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 0 < D) (hX : 1 ≤ X) :
    (∑ d ∈ Icc 1 X, ∑ m ∈ (Icc 1 X).filter (fun m => D ∣ d*m),
      ‖lemma23UpsilonArithmeticFunction χ d‖ * ‖lemma23NuArithmeticFunction χ m‖ *
        (lemma34Tau 4 d : ℝ) * (lemma34Tau 4 m : ℝ) / ((d : ℝ)*(m : ℝ))) ≤
      (lemma34Tau 8 D : ℝ)/(D : ℝ)*(harmonic X : ℝ)^16 := by
  have hh : (∑ dm ∈ ramifiedHeadPairs D X,
      ‖lemma23UpsilonArithmeticFunction χ dm.1‖ * ‖lemma23NuArithmeticFunction χ dm.2‖ *
        (lemma34Tau 4 dm.1 : ℝ) * (lemma34Tau 4 dm.2 : ℝ) /
          ((dm.1 : ℝ)*(dm.2 : ℝ))) ≤
      (lemma34Tau 8 D : ℝ)/(D : ℝ)*(harmonic X : ℝ)^16 := by
    apply (sum_le_sum (fun dm _ => ramifiedHead_actual_pair_le χ dm.1 dm.2)).trans
    exact ramifiedHead_nu_pair_harmonic_le χ hD hX
  simpa only [ramifiedHeadPairs, sum_filter, sum_product] using hh

/-- The logarithmic form of the actual ramified equality bound. -/
theorem ramifiedHead_actual_log_le {D X : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 0 < D) (hX : 1 ≤ X) :
    (∑ d ∈ Icc 1 X, ∑ m ∈ (Icc 1 X).filter (fun m => D ∣ d*m),
      ‖lemma23UpsilonArithmeticFunction χ d‖ * ‖lemma23NuArithmeticFunction χ m‖ *
        (lemma34Tau 4 d : ℝ) * (lemma34Tau 4 m : ℝ) / ((d : ℝ)*(m : ℝ))) ≤
      (lemma34Tau 8 D : ℝ)/(D : ℝ)*(1+Real.log (X : ℝ))^16 := by
  have hH : 0 ≤ (harmonic X : ℝ) := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    exact sum_nonneg (fun _ _ => by positivity)
  exact (ramifiedHead_actual_harmonic_le χ hD hX).trans
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hH (harmonic_le_one_add_log X) 16) (by positivity))

end ZhangLS.Spec
