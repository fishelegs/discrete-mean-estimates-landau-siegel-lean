import ZhangLS.Spec.Lemma153EulerBounds
/-! Normal convergence and holomorphy of the repaired Euler product.
The bound explicitly depends on D through the finite ramified contribution.
This file does not silently identify this product with a Dirichlet quotient. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex Filter Topology Set
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def lemma153Majorant (D : ℕ) (q : Nat.Primes) : ℝ :=
  100000*(q.val:ℝ)^(-(3/2:ℝ)) +
    if q.val ∣ D then 3*(q.val:ℝ)^(-(3/4:ℝ)) else 0

lemma lemma153_majorant_nonneg (D : ℕ) (q : Nat.Primes) :
    0 ≤ lemma153Majorant D q := by
  unfold lemma153Majorant
  split_ifs <;> positivity

lemma lemma153_majorant_summable {D : ℕ} (hD : D ≠ 0) :
    Summable (lemma153Majorant D) := by
  have hbase : Summable (fun q : Nat.Primes => 100000*(q.val:ℝ)^(-(3/2:ℝ))) :=
    ((Real.summable_nat_rpow.mpr (by norm_num : -(3/2:ℝ)< -1)).subtype Nat.Prime).mul_left 100000
  have hram : Summable (fun q : Nat.Primes => if q.val ∣ D then 3*(q.val:ℝ)^(-(3/4:ℝ)) else 0) := by
    have hn : Summable ((D.primeFactors : Set ℕ).indicator
        (fun q : ℕ => 3*(q:ℝ)^(-(3/4:ℝ)))) :=
      summable_subtype_iff_indicator.mp (D.primeFactors.finite_toSet.summable _)
    convert hn.subtype Nat.Prime using 1
    funext q
    have hm : q.val ∈ D.primeFactors ↔ q.val ∣ D := by
      simp [Nat.mem_primeFactors,q.property,hD]
    by_cases hq : q.val ∣ D
    · simp [Set.indicator_apply,hq,hm.mpr hq]
    · simp [Set.indicator_apply,hq,show q.val ∉ D.primeFactors by simpa only [hm] using hq]
  exact hbase.add hram

lemma lemma153_prime_error_uniform {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (γ : ℂ) (hpar : Lemma153SmallParameters β γ)
    (q : Nat.Primes) (s : ℂ) (hs : 3/4 ≤ s.re) :
    ‖lemma153PrimeFactor χ β γ q s-1‖ ≤ lemma153Majorant D q := by
  have hz : ‖lemma32PrimeMonomial q.val s‖ ≤ (q.val:ℝ)^(-(3/4:ℝ)) := by
    rw [lemma83_prime_monomial_norm_rpow q.property.pos]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast q.property.one_lt.le) (by linarith)
  have hz1 : ‖lemma32PrimeMonomial q.val s‖ ≤ 1 := hz.trans
    (Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast q.property.one_lt.le) (by norm_num))
  unfold lemma153PrimeFactor lemma153Majorant
  split_ifs with hq
  · have hh := lemma153_ramified_factor_error (lemma32PrimeMonomial q.val s) hz1
    have hp : 0 ≤ 100000*(q.val:ℝ)^(-(3/2:ℝ)) := by positivity
    linarith
  · simpa using lemma153_unramified_factor_error χ β γ hpar q s hs

lemma lemma153_prime_factor_differentiable {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (γ : ℂ) (q : Nat.Primes) :
    Differentiable ℂ (lemma153PrimeFactor χ β γ q) := by
  intro s
  have hm : DifferentiableAt ℂ (lemma32PrimeMonomial q.val) s :=
    lemma32_prime_monomial_differentiable q.val s
  unfold lemma153PrimeFactor lemma153UnramifiedPrimeFactor lemma153ShiftedLocalCorrection
  split_ifs <;> fun_prop

lemma lemma153_products_locally_uniform {D : ℕ} (hD : D ≠ 0)
    (χ : RealPrimitiveCharacter D) (β : Fin 2 → ℂ) (γ : ℂ)
    (hpar : Lemma153SmallParameters β γ) :
    TendstoLocallyUniformlyOn
      (fun S : Finset Nat.Primes => fun s : ℂ => ∏ q ∈ S, lemma153PrimeFactor χ β γ q s)
      (lemma153EulerProduct χ β γ) atTop {s : ℂ | 3/4 < s.re} := by
  have hh := Summable.hasProdLocallyUniformlyOn_one_add
    (f := fun q : Nat.Primes => fun s : ℂ => lemma153PrimeFactor χ β γ q s-1)
    (isOpen_lt continuous_const Complex.continuous_re) (lemma153_majorant_summable hD)
    (Filter.Eventually.of_forall fun q s hs => lemma153_prime_error_uniform χ β γ hpar q s hs.le)
    (fun q => ((lemma153_prime_factor_differentiable χ β γ q).continuous.continuousOn).sub continuousOn_const)
  simpa only [hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn,add_sub_cancel,
    lemma153EulerProduct] using hh

lemma lemma153_euler_product_multipliable {D : ℕ} (hD : D ≠ 0)
    (χ : RealPrimitiveCharacter D) (β : Fin 2 → ℂ) (γ : ℂ)
    (hpar : Lemma153SmallParameters β γ) (s : ℂ) (hs : 3/4 ≤ s.re) :
    Multipliable (fun q : Nat.Primes => lemma153PrimeFactor χ β γ q s) := by
  have hsum : Summable (fun q : Nat.Primes => ‖lemma153PrimeFactor χ β γ q s-1‖) :=
    (lemma153_majorant_summable hD).of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun q => lemma153_prime_error_uniform χ β γ hpar q s hs)
  simpa only [add_sub_cancel] using multipliable_one_add_of_summable hsum

/-- The product is holomorphic on an open region containing the closed
half-plane Re s≥9/10, including every boundary point in the paper statement. -/
lemma lemma153_euler_product_analyticOnNhd {D : ℕ} (hD : D ≠ 0)
    (χ : RealPrimitiveCharacter D) (β : Fin 2 → ℂ) (γ : ℂ)
    (hpar : Lemma153SmallParameters β γ) :
    AnalyticOnNhd ℂ (lemma153EulerProduct χ β γ) {s : ℂ | 3/4 < s.re} := by
  apply DifferentiableOn.analyticOnNhd ?_ (isOpen_lt continuous_const Complex.continuous_re)
  apply (lemma153_products_locally_uniform hD χ β γ hpar).differentiableOn
  · filter_upwards with S
    exact DifferentiableOn.fun_finsetProd fun q _ =>
      (lemma153_prime_factor_differentiable χ β γ q).differentiableOn
  · exact isOpen_lt continuous_const Complex.continuous_re

noncomputable def lemma153DBound (D : ℕ) : ℝ := Real.exp (∑' q : Nat.Primes, lemma153Majorant D q)

/-- Explicit boundedness. Its finite ramified dependence must be preserved in
any downstream contour argument; it is not asserted to be absolute in D. -/
lemma lemma153_euler_product_norm_bound {D : ℕ} (hD : D ≠ 0)
    (χ : RealPrimitiveCharacter D) (β : Fin 2 → ℂ) (γ : ℂ)
    (hpar : Lemma153SmallParameters β γ) (s : ℂ) (hs : 3/4 ≤ s.re) :
    ‖lemma153EulerProduct χ β γ s‖ ≤ lemma153DBound D := by
  have ht := (lemma153_euler_product_multipliable hD χ β γ hpar s hs).hasProd.norm
  apply le_of_tendsto ht
  filter_upwards with S
  calc
    _ ≤ ∏ q ∈ S, (1+lemma153Majorant D q) := by
      apply prod_le_prod (fun _ _ => norm_nonneg _)
      intro q hq
      have hh := norm_le_norm_sub_add (lemma153PrimeFactor χ β γ q s) (1:ℂ)
      rw [norm_one] at hh
      linarith [lemma153_prime_error_uniform χ β γ hpar q s hs]
    _ ≤ Real.exp (∑ q ∈ S, lemma153Majorant D q) :=
      Real.prod_one_add_le_exp_sum S (lemma153_majorant_nonneg D)
    _ ≤ lemma153DBound D := by
      apply Real.exp_le_exp.mpr
      exact (lemma153_majorant_summable hD).sum_le_tsum S (fun q _ => lemma153_majorant_nonneg D q)

end ZhangLS.Spec
