import ZhangLS.Spec.Lemma153CenterPrimeComparison
import ZhangLS.Spec.Lemma153CenterProductBounds
/-! Quantitative center perturbation for the source-repaired Lemma 15.3
Euler product.  The bound is absolute in D.  No quotient by an infinite
product or additional nonvanishing assumption is used. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex Filter Topology
open scoped Classical
set_option maxHeartbeats 1500000

noncomputable def lemma153CenterVariationConstant : ℝ :=
  lemma153UnramifiedProductBound * lemma153CenterPrimeConstant *
    (1+∑' q : Nat.Primes, (q.val:ℝ)^(-(9/5:ℝ)))

lemma lemma153_center_variation_majorant_summable :
    Summable (fun q : Nat.Primes => (q.val:ℝ)^(-(9/5:ℝ))) := by
  exact (Real.summable_nat_rpow.mpr (by norm_num : -(9/5:ℝ)< -1)).subtype Nat.Prime

lemma lemma153_center_variation_constant_pos : 0 < lemma153CenterVariationConstant := by
  have ht : 0 ≤ ∑' q : Nat.Primes, (q.val:ℝ)^(-(9/5:ℝ)) :=
    tsum_nonneg (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hC := lemma153_center_prime_constant_pos
  have hB := lemma153_unramified_product_bound_pos
  unfold lemma153CenterVariationConstant
  positivity

/-- Ramified factors really cancel in a center comparison; they have not
been replaced by the unramified formula. -/
lemma lemma153_ramified_center_difference_eq_zero {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (γ : ℂ) (q : Nat.Primes) (hq : q.val ∣ D) :
    lemma153PrimeFactor χ β γ q 1 - lemma153PrimeFactor χ (fun _ => 0) 0 q 1 = 0 := by
  simp [lemma153PrimeFactor,hq]

lemma lemma153_finite_center_product_comparison {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (γ : ℂ) (hpar : Lemma153SmallParameters β γ) (S : Finset Nat.Primes) :
    ‖(∏ q ∈ S, lemma153PrimeFactor χ β γ q 1) -
      ∏ q ∈ S, lemma153PrimeFactor χ (fun _ => 0) 0 q 1‖ ≤
        lemma153CenterVariationConstant*(‖β 0‖+‖β 1‖+‖γ‖) := by
  let E := ‖β 0‖+‖β 1‖+‖γ‖
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hC := lemma153_center_prime_constant_pos
  have hb := lemma83_product_perturbation S
    (fun q => lemma153PrimeFactor χ β γ q 1)
    (fun q => lemma153PrimeFactor χ (fun _ => 0) 0 q 1)
    (fun q => 1+100000*(q.val:ℝ)^(-(3/2:ℝ)))
    (fun q => lemma153CenterPrimeConstant*E*(q.val:ℝ)^(-(9/5:ℝ)))
    (fun q _ => by
      have := Real.rpow_nonneg (Nat.cast_nonneg q.val : (0:ℝ)≤q.val) (-(3/2:ℝ))
      linarith)
    (fun q _ => lemma153_prime_center_norm_le χ β γ hpar q)
    (fun q _ => lemma153_prime_center_norm_le χ (fun _ => 0) 0 lemma153_zero_parameters q)
    (fun q _ => lemma153_center_prime_comparison χ β γ hpar q)
  have hsum : (∑ q ∈ S, lemma153CenterPrimeConstant*E*(q.val:ℝ)^(-(9/5:ℝ))) ≤
      (lemma153CenterPrimeConstant*E)*(1+∑' q : Nat.Primes, (q.val:ℝ)^(-(9/5:ℝ))) := by
    rw [← mul_sum]
    gcongr
    exact (lemma153_center_variation_majorant_summable.sum_le_tsum S
      (fun q _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)).trans (by linarith)
  refine hb.trans ?_
  calc
    _ ≤ lemma153UnramifiedProductBound*((lemma153CenterPrimeConstant*E)*
        (1+∑' q : Nat.Primes, (q.val:ℝ)^(-(9/5:ℝ)))) := by
      apply mul_le_mul (lemma153_finite_center_majorant_product_le S) hsum
        (Finset.sum_nonneg (fun _ _ => by positivity)) lemma153_unramified_product_bound_pos.le
    _ = _ := by unfold lemma153CenterVariationConstant; dsimp [E]; ring

/-- Uniform perturbation for the genuinely convergent repaired correction
product, including the exact finite ramified factors. -/
lemma lemma153_repaired_euler_center_comparison {D : ℕ} (hD : D ≠ 0)
    (χ : RealPrimitiveCharacter D) (β : Fin 2 → ℂ) (γ : ℂ)
    (hpar : Lemma153SmallParameters β γ) :
    ‖lemma153EulerProduct χ β γ 1 - lemma153EulerProduct χ (fun _ => 0) 0 1‖ ≤
      lemma153CenterVariationConstant*(‖β 0‖+‖β 1‖+‖γ‖) := by
  have ht := (lemma153_euler_product_multipliable hD χ β γ hpar 1 (by norm_num)).hasProd
  have hz := (lemma153_euler_product_multipliable hD χ (fun _ => 0) 0
    lemma153_zero_parameters 1 (by norm_num)).hasProd
  apply le_of_tendsto (ht.sub hz).norm
  filter_upwards with S
  exact lemma153_finite_center_product_comparison χ β γ hpar S

/-- The original main term is retained; its prime product excludes q∣D. -/
lemma lemma153_repaired_center_main_comparison {D : ℕ} (hD : D ≠ 0)
    (χ : RealPrimitiveCharacter D) (β : Fin 2 → ℂ) (γ : ℂ)
    (hpar : Lemma153SmallParameters β γ) :
    ‖lemma153EulerProduct χ β γ 1 - lemma153MainTerm χ‖ ≤
      lemma153CenterVariationConstant*(‖β 0‖+‖β 1‖+‖γ‖) := by
  rw [← lemma153_zero_product_equals_main hD χ]
  exact lemma153_repaired_euler_center_comparison hD χ β γ hpar

/-- Fully expanded main term: this is the actual ramification-restricted
product, not the product over all primes of the unramified formula. -/
lemma lemma153_repaired_center_main_explicit {D : ℕ} (hD : D ≠ 0)
    (χ : RealPrimitiveCharacter D) (β : Fin 2 → ℂ) (γ : ℂ)
    (hpar : Lemma153SmallParameters β γ) :
    ‖lemma153EulerProduct χ β γ 1 - (Nat.totient D:ℂ)^2/(D:ℂ)^2 *
      ∏' q : {q : Nat.Primes // ¬q.val ∣ D},
        (1-(q.val.val:ℂ)^(-2:ℤ))^2/(1-χ.evalNat q.val.val*(q.val.val:ℂ)^(-2:ℤ))‖ ≤
      lemma153CenterVariationConstant*(‖β 0‖+‖β 1‖+‖γ‖) :=
  lemma153_repaired_center_main_comparison hD χ β γ hpar

end ZhangLS.Spec
