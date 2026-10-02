import ZhangLS.Spec.Lemma32ActualHasseCorrelation
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma32_actual_prime_distinct_quartic_correlation_bound {p : ℕ} [Fact p.Prime]
    (χ : RealPrimitiveCharacter p) {H : ℕ} (hH : H ≤ p) (v : Fin 4 → Fin H)
    (hv : Function.Injective v) :
    |lemma32QuarticCorrelation χ v| ≤ 2*Real.sqrt (p : ℝ)+1 := by
  have hi : Function.Injective (fun i : Fin 4 => ((v i).val : ZMod p)) :=
    (lemma32_short_residue_cast_injective hH).comp hv
  have he := lemma32_actual_prime_distinct_quartic_hasse_bound χ
    ((v 0).val : ZMod p) ((v 1).val : ZMod p) ((v 2).val : ZMod p)
    ((v 3).val : ZMod p) (hi.ne (by decide)) (hi.ne (by decide)) (hi.ne (by decide))
    (hi.ne (by decide)) (hi.ne (by decide)) (hi.ne (by decide))
  have hr := Complex.abs_re_le_norm
    (∑ x : ZMod p, χ.chi ((x+(v 0).val)*(x+(v 1).val)*(x+(v 2).val)*(x+(v 3).val)))
  apply LE.le.trans ?_ he
  simpa only [lemma32QuarticCorrelation, Fin.prod_univ_four, Complex.re_sum] using hr

lemma lemma32_actual_prime_distinct_fourth_moment_bound {p : ℕ} [Fact p.Prime]
    (χ : RealPrimitiveCharacter p) {H : ℕ} (hH : H ≤ p) :
    lemma32DistinctFourthMoment χ H ≤ (H : ℝ)^4*(2*Real.sqrt (p : ℝ)+1) := by
  let S := (Finset.univ \ lemma32DegenerateQuarticTuples H).filter Function.Injective
  have hc : S.card ≤ H^4 := by
    have hc := Finset.card_le_card (Finset.subset_univ S)
    simpa only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] using hc
  have hh : (0 : ℝ) ≤ 2*Real.sqrt (p : ℝ)+1 := by positivity
  calc
    lemma32DistinctFourthMoment χ H ≤ ∑ v ∈ S, (2*Real.sqrt (p : ℝ)+1) := by
      apply Finset.sum_le_sum
      intro v hv
      exact lemma32_actual_prime_distinct_quartic_correlation_bound χ hH v
        (Finset.mem_filter.mp hv).2
    _ = (S.card : ℝ)*(2*Real.sqrt (p : ℝ)+1) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (H : ℝ)^4*(2*Real.sqrt (p : ℝ)+1) := by
      apply mul_le_mul_of_nonneg_right _ hh
      exact_mod_cast hc

lemma lemma32_actual_prime_fourth_moment_hasse_bound {p : ℕ} [Fact p.Prime]
    (χ : RealPrimitiveCharacter p) {H : ℕ} (hH : H ≤ p) :
    lemma32BurgessFourthMoment χ H ≤ 3*(p : ℝ)*(H : ℝ)^2+12*(H : ℝ)^3+
      (H : ℝ)^4*(2*Real.sqrt (p : ℝ)+1) := by
  have hr := lemma32_actual_prime_fourth_moment_distinct_reduction χ hH
  have hd := lemma32_actual_prime_distinct_fourth_moment_bound χ hH
  linarith

end ZhangLS.Spec
