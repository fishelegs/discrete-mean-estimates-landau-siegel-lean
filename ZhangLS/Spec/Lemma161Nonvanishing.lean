import ZhangLS.Spec.Lemma161MainTerm

set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex Filter Topology Set
open scoped Classical
set_option maxHeartbeats 1600000

noncomputable def lemma161ReciprocalBound : ℝ :=
  Real.exp (2 * ∑' q : Nat.Primes, lemma152CorrectionConstant*(q.val:ℝ)^(-(19/10:ℝ)))

noncomputable def lemma161MainLowerBound : ℝ := 1/lemma161ReciprocalBound

lemma lemma161_reciprocal_bound_pos : 0 < lemma161ReciprocalBound := Real.exp_pos _

lemma lemma161_main_lower_bound_pos : 0 < lemma161MainLowerBound :=
  one_div_pos.mpr lemma161_reciprocal_bound_pos

lemma lemma161_inverse_norm_upper {z : ℂ} {w : ℝ}
    (hz : (3/4:ℝ) ≤ ‖z‖) (hw : ‖z-1‖ ≤ w) : ‖z⁻¹‖ ≤ 1+2*w := by
  have hz0 : z ≠ 0 := by intro h; rw [h,norm_zero] at hz; norm_num at hz
  have he : z⁻¹-1 = (1-z)/z := by field_simp
  have hb : ‖z⁻¹-1‖ ≤ w/(3/4:ℝ) := by
    rw [he,norm_div,norm_sub_rev]
    exact div_le_div₀ ((norm_nonneg _).trans hw) hw (by norm_num) hz
  have hh := norm_le_norm_sub_add z⁻¹ (1:ℂ)
  rw [norm_one] at hh
  have hw0 := (norm_nonneg (z-1)).trans hw
  linarith

lemma lemma161_finite_reciprocal_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (P : Nat.Primes → Prop) (hP : ∀ q, P q → q.val = 2 → χ.evalNat 2 ≠ 1)
    (S : Finset Nat.Primes) :
    ‖∏ q ∈ S, (lemma161RestrictedFactor χ 0 P q 1)⁻¹‖ ≤ lemma161ReciprocalBound := by
  have hnorm (q : Nat.Primes) :
      ‖(lemma161RestrictedFactor χ 0 P q 1)⁻¹‖ ≤
        1+2*(lemma152CorrectionConstant*(q.val:ℝ)^(-(19/10:ℝ))) := by
    apply lemma161_inverse_norm_upper
    · unfold lemma161RestrictedFactor
      split_ifs with hq
      · rw [lemma161_zero_center_factor]
        exact lemma161_main_factor_norm_lower χ q (hP q hq)
      · norm_num
    · exact lemma161_restricted_error χ 0 rfl P q 1 (by norm_num)
  rw [norm_prod]
  apply (prod_le_prod (fun _ _ => norm_nonneg _) (fun q _ => hnorm q)).trans
  apply (Real.prod_one_add_le_exp_sum S (fun q : Nat.Primes =>
    mul_nonneg (by norm_num : (0:ℝ)≤2)
      (mul_nonneg lemma152_correction_constant_pos.le (Real.rpow_nonneg (Nat.cast_nonneg _) _)))).trans
  apply Real.exp_le_exp.mpr
  rw [← mul_sum]
  exact mul_le_mul_of_nonneg_left
    (lemma152_majorant_summable.sum_le_tsum S (fun q _ =>
      mul_nonneg lemma152_correction_constant_pos.le (Real.rpow_nonneg (Nat.cast_nonneg _) _)))
    (by norm_num)

lemma lemma161_finite_center_lower {D : ℕ} (χ : RealPrimitiveCharacter D)
    (P : Nat.Primes → Prop) (hP : ∀ q, P q → q.val = 2 → χ.evalNat 2 ≠ 1)
    (S : Finset Nat.Primes) :
    lemma161MainLowerBound ≤ ‖∏ q ∈ S, lemma161RestrictedFactor χ 0 P q 1‖ := by
  have hne (q : Nat.Primes) : lemma161RestrictedFactor χ 0 P q 1 ≠ 0 := by
    unfold lemma161RestrictedFactor
    split_ifs with hq
    · rw [lemma161_zero_center_factor]
      intro he
      have hh := lemma161_main_factor_norm_lower χ q (hP q hq)
      rw [he,norm_zero] at hh
      norm_num at hh
    · exact one_ne_zero
  have he : (∏ q ∈ S, lemma161RestrictedFactor χ 0 P q 1) *
      (∏ q ∈ S, (lemma161RestrictedFactor χ 0 P q 1)⁻¹) = 1 := by
    rw [← prod_mul_distrib]
    exact prod_eq_one (fun q _ => mul_inv_cancel₀ (hne q))
  have hn := congrArg norm he
  rw [norm_mul,norm_one] at hn
  have hprod := lemma161_finite_reciprocal_bound χ P hP S
  unfold lemma161MainLowerBound
  apply (div_le_iff₀ lemma161_reciprocal_bound_pos).mpr
  calc
    (1:ℝ) = ‖∏ q ∈ S, lemma161RestrictedFactor χ 0 P q 1‖ *
        ‖∏ q ∈ S, (lemma161RestrictedFactor χ 0 P q 1)⁻¹‖ := hn.symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hprod (norm_nonneg _)

lemma lemma161_restricted_center_lower {D : ℕ} (χ : RealPrimitiveCharacter D)
    (P : Nat.Primes → Prop) (hP : ∀ q, P q → q.val = 2 → χ.evalNat 2 ≠ 1) :
    lemma161MainLowerBound ≤ ‖lemma161RestrictedProduct χ 0 P 1‖ := by
  have ht := (lemma161_restricted_multipliable χ 0 rfl P 1 (by norm_num)).hasProd.norm
  exact ge_of_tendsto' ht (fun S => by simpa only [norm_prod] using lemma161_finite_center_lower χ P hP S)

/-- Uniform nonzero main constant, valid in both original χ(2) cases. -/
lemma lemma161_main_norm_lower {D : ℕ} (χ : RealPrimitiveCharacter D) :
    lemma161MainLowerBound ≤ ‖lemma161MainTerm χ‖ := by
  rw [← lemma161_zero_center_equals_main]
  unfold lemma161Star
  split_ifs with hχ
  · rw [norm_mul]
    norm_num only [Complex.norm_ofNat]
    have hh := lemma161_restricted_center_lower χ (fun q => 2 < q.val)
      (fun q hq heq => by omega)
    linarith [norm_nonneg (lemma161RestrictedProduct χ 0 (fun q => 2 < q.val) 1)]
  · have hh := lemma161_restricted_center_lower χ (fun _ => True) (fun _ _ _ => hχ)
    simpa [lemma161RestrictedProduct,lemma161RestrictedFactor,lemma161EulerProduct] using hh

lemma lemma161_main_ne_zero {D : ℕ} (χ : RealPrimitiveCharacter D) :
    lemma161MainTerm χ ≠ 0 := by
  intro h
  have hh := lemma161_main_norm_lower χ
  rw [h,norm_zero] at hh
  exact (not_le_of_gt lemma161_main_lower_bound_pos) hh

end ZhangLS.Spec
