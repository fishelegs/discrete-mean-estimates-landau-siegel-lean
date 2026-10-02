import ZhangLS.Spec.Lemma161NormalizedProduct
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex Filter Topology
open scoped Classical
set_option maxHeartbeats 1500000

lemma lemma161_restricted_prime_comparison {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (P : Nat.Primes → Prop) (hsmall : ‖β‖ ≤ 1/10)
    (q : Nat.Primes) (s : ℂ) (hs : 9/10 ≤ s.re) (hs1 : ‖s-1‖ ≤ 1/10) :
    ‖lemma161RestrictedFactor χ β P q s-lemma161RestrictedFactor χ 0 P q 1‖ ≤
      10*lemma152CorrectionConstant*(‖β‖+‖s-1‖)*(q.val:ℝ)^(-(17/10:ℝ)) := by
  unfold lemma161RestrictedFactor
  split_ifs
  · exact lemma161_prime_comparison χ β hβ hsmall q s hs hs1
  · simp only [sub_self,norm_zero]
    have hC := lemma152_correction_constant_pos
    positivity

lemma lemma161_restricted_norm_le {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (P : Nat.Primes → Prop) (q : Nat.Primes)
    (s : ℂ) (hs : 9/10 ≤ s.re) :
    ‖lemma161RestrictedFactor χ β P q s‖ ≤ 1+lemma152CorrectionConstant*(q.val:ℝ)^(-(19/10:ℝ)) := by
  have hh := norm_le_norm_sub_add (lemma161RestrictedFactor χ β P q s) (1:ℂ)
  rw [norm_one] at hh
  linarith [lemma161_restricted_error χ β hβ P q s hs]

lemma lemma161_finite_restricted_comparison {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (P : Nat.Primes → Prop) (hsmall : ‖β‖ ≤ 1/10)
    (s : ℂ) (hs : 9/10 ≤ s.re) (hs1 : ‖s-1‖ ≤ 1/10) (S : Finset Nat.Primes) :
    ‖(∏ q ∈ S, lemma161RestrictedFactor χ β P q s) -
      ∏ q ∈ S, lemma161RestrictedFactor χ 0 P q 1‖ ≤
        lemma152UniformVariationConstant*(‖β‖+‖s-1‖) := by
  let E := ‖β‖+‖s-1‖
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hC := lemma152_correction_constant_pos
  have hb := lemma83_product_perturbation S
    (fun q => lemma161RestrictedFactor χ β P q s) (fun q => lemma161RestrictedFactor χ 0 P q 1)
    (fun q => 1+lemma152CorrectionConstant*(q.val:ℝ)^(-(19/10:ℝ)))
    (fun q => 10*lemma152CorrectionConstant*E*(q.val:ℝ)^(-(17/10:ℝ)))
    (fun q _ => by have := mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg q.val) (-(19/10:ℝ))); linarith)
    (fun q _ => lemma161_restricted_norm_le χ β hβ P q s hs)
    (fun q _ => lemma161_restricted_norm_le χ 0 rfl P q 1 (by norm_num))
    (fun q _ => lemma161_restricted_prime_comparison χ β hβ P hsmall q s hs hs1)
  have hsum : (∑ q ∈ S, 10*lemma152CorrectionConstant*E*(q.val:ℝ)^(-(17/10:ℝ))) ≤
      (10*lemma152CorrectionConstant*E)*(1+∑' q : Nat.Primes, (q.val:ℝ)^(-(17/10:ℝ))) := by
    rw [← mul_sum]
    gcongr
    exact (lemma152_variation_majorant_summable.sum_le_tsum S
      (fun q _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)).trans (by linarith)
  refine hb.trans ?_
  calc
    _ ≤ lemma152ProductBound*((10*lemma152CorrectionConstant*E)*
        (1+∑' q : Nat.Primes, (q.val:ℝ)^(-(17/10:ℝ)))) := by
      apply mul_le_mul (lemma152_finite_majorant_product_le S) hsum
        (Finset.sum_nonneg (fun _ _ => by positivity)) lemma152_product_bound_pos.le
    _ = _ := by unfold lemma152UniformVariationConstant; dsimp [E]; ring

/-- Uniform quantitative perturbation of the genuinely convergent Euler product. -/
lemma lemma161_restricted_comparison {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (P : Nat.Primes → Prop) (hsmall : ‖β‖ ≤ 1/10)
    (s : ℂ) (hs : 9/10 ≤ s.re) (hs1 : ‖s-1‖ ≤ 1/10) :
    ‖lemma161RestrictedProduct χ β P s - lemma161RestrictedProduct χ 0 P 1‖ ≤
      lemma152UniformVariationConstant*(‖β‖+‖s-1‖) := by
  have ht := (lemma161_restricted_multipliable χ β hβ P s hs).hasProd
  have hz := (lemma161_restricted_multipliable χ 0 rfl P 1 (by norm_num)).hasProd
  apply le_of_tendsto (ht.sub hz).norm
  filter_upwards with S
  exact lemma161_finite_restricted_comparison χ β hβ P hsmall s hs hs1 S

lemma lemma161_euler_product_comparison {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (hsmall : ‖β‖ ≤ 1/10)
    (s : ℂ) (hs : 9/10 ≤ s.re) (hs1 : ‖s-1‖ ≤ 1/10) :
    ‖lemma161EulerProduct χ β s-lemma161EulerProduct χ 0 1‖ ≤
      lemma152UniformVariationConstant*(‖β‖+‖s-1‖) := by
  simpa [lemma161RestrictedProduct,lemma161RestrictedFactor,lemma161EulerProduct] using
    lemma161_restricted_comparison χ β hβ (fun _ => True) hsmall s hs hs1

lemma lemma161_star_comparison {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (hsmall : ‖β‖ ≤ 1/10)
    (s : ℂ) (hs : 9/10 ≤ s.re) (hs1 : ‖s-1‖ ≤ 1/10) :
    ‖lemma161Star χ β s-lemma161Star χ 0 1‖ ≤
      (2*lemma152UniformVariationConstant)*(‖β‖+‖s-1‖) := by
  unfold lemma161Star
  split_ifs
  · rw [← mul_sub,norm_mul]
    norm_num only [Complex.norm_ofNat]
    have h := lemma161_restricted_comparison χ β hβ (fun q => 2 < q.val) hsmall s hs hs1
    nlinarith
  · have h := lemma161_euler_product_comparison χ β hβ hsmall s hs hs1
    have hp := lemma152_uniform_variation_constant_pos
    nlinarith [norm_nonneg β,norm_nonneg (s-1)]

end ZhangLS.Spec
