import ZhangLS.Spec.Lemma152PrimeComparison
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex Filter Topology
open scoped Classical
set_option maxHeartbeats 1500000

noncomputable def lemma152ProductBound : ℝ :=
  Real.exp (∑' q : Nat.Primes, lemma152CorrectionConstant*(q.val:ℝ)^(-(19/10:ℝ)))

noncomputable def lemma152UniformVariationConstant : ℝ :=
  10*lemma152CorrectionConstant*lemma152ProductBound*
    (1+∑' q : Nat.Primes, (q.val:ℝ)^(-(17/10:ℝ)))

lemma lemma152_variation_majorant_summable :
    Summable (fun q : Nat.Primes => (q.val:ℝ)^(-(17/10:ℝ))) := by
  exact (Real.summable_nat_rpow.mpr (by norm_num : -(17/10:ℝ) < -1)).subtype Nat.Prime

lemma lemma152_product_bound_pos : 0 < lemma152ProductBound := Real.exp_pos _

lemma lemma152_uniform_variation_constant_pos : 0 < lemma152UniformVariationConstant := by
  unfold lemma152UniformVariationConstant
  have ht : 0 ≤ ∑' q : Nat.Primes, (q.val:ℝ)^(-(17/10:ℝ)) :=
    tsum_nonneg (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hC := lemma152_correction_constant_pos
  have hB := lemma152_product_bound_pos
  positivity

lemma lemma152_finite_majorant_product_le (S : Finset Nat.Primes) :
    (∏ q ∈ S, (1+lemma152CorrectionConstant*(q.val:ℝ)^(-(19/10:ℝ)))) ≤ lemma152ProductBound := by
  apply (Real.prod_one_add_le_exp_sum S (fun q : Nat.Primes =>
    mul_nonneg lemma152_correction_constant_pos.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))).trans
  apply Real.exp_le_exp.mpr
  exact lemma152_majorant_summable.sum_le_tsum S (fun q _ =>
    mul_nonneg lemma152_correction_constant_pos.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))

lemma lemma152_prime_norm_le {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (hβ : ∀ i, (β i).re = 0) (q : Nat.Primes)
    (s : ℂ) (hs : 9/10 ≤ s.re) :
    ‖lemma152PrimeFactor χ β q s‖ ≤ 1+lemma152CorrectionConstant*(q.val:ℝ)^(-(19/10:ℝ)) := by
  have hh := norm_le_norm_sub_add (lemma152PrimeFactor χ β q s) (1:ℂ)
  rw [norm_one] at hh
  linarith [lemma152_prime_error_uniform χ β hβ q s hs]

lemma lemma152_finite_product_comparison {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (hβ : ∀ i, (β i).re = 0) (hsmall : ∀ i, ‖β i‖ ≤ 1/10)
    (s : ℂ) (hs : 9/10 ≤ s.re) (hs1 : ‖s-1‖ ≤ 1/10) (S : Finset Nat.Primes) :
    ‖(∏ q ∈ S, lemma152PrimeFactor χ β q s) -
      ∏ q ∈ S, lemma152PrimeFactor χ (fun _ => 0) q 1‖ ≤
        lemma152UniformVariationConstant*(‖β 0‖+‖β 1‖+‖s-1‖) := by
  let E := ‖β 0‖+‖β 1‖+‖s-1‖
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hC := lemma152_correction_constant_pos
  have hb := lemma83_product_perturbation S
    (fun q => lemma152PrimeFactor χ β q s) (fun q => lemma152PrimeFactor χ (fun _ => 0) q 1)
    (fun q => 1+lemma152CorrectionConstant*(q.val:ℝ)^(-(19/10:ℝ)))
    (fun q => 10*lemma152CorrectionConstant*E*(q.val:ℝ)^(-(17/10:ℝ)))
    (fun q _ => by have := mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg q.val) (-(19/10:ℝ))); linarith)
    (fun q _ => lemma152_prime_norm_le χ β hβ q s hs)
    (fun q _ => lemma152_prime_norm_le χ (fun _ => 0) (fun _ => rfl) q 1 (by norm_num))
    (fun q _ => lemma152_prime_comparison χ β hβ hsmall q s hs hs1)
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
lemma lemma152_euler_product_comparison {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (hβ : ∀ i, (β i).re = 0) (hsmall : ∀ i, ‖β i‖ ≤ 1/10)
    (s : ℂ) (hs : 9/10 ≤ s.re) (hs1 : ‖s-1‖ ≤ 1/10) :
    ‖lemma152EulerProduct χ β s - lemma152EulerProduct χ (fun _ => 0) 1‖ ≤
      lemma152UniformVariationConstant*(‖β 0‖+‖β 1‖+‖s-1‖) := by
  have ht := (lemma152_euler_product_multipliable χ β hβ s hs).hasProd
  have hz := (lemma152_euler_product_multipliable χ (fun _ => 0) (fun _ => rfl) 1 (by norm_num)).hasProd
  apply le_of_tendsto (ht.sub hz).norm
  filter_upwards with S
  exact lemma152_finite_product_comparison χ β hβ hsmall s hs hs1 S

end ZhangLS.Spec
