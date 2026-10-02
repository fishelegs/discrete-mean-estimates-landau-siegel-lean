import ZhangLS.Spec.Lemma83LocalCorrection
import ZhangLS.Spec.Lemma32ProductAnalytic
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn

set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex Filter Topology Set
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def lemma83RegularRadius : ℝ := Real.exp (-(9/10)*Real.log 2)
noncomputable def lemma83RegularConstant : ℝ := 8/(1-lemma83RegularRadius)

lemma lemma83_regular_radius_pos : 0 < lemma83RegularRadius := Real.exp_pos _
lemma lemma83_regular_radius_lt_one : lemma83RegularRadius < 1 := by
  unfold lemma83RegularRadius
  rw [Real.exp_lt_one_iff]
  have := Real.log_pos (show (1:ℝ) < 2 by norm_num)
  nlinarith

lemma lemma83_regular_constant_pos : 0 < lemma83RegularConstant := by
  unfold lemma83RegularConstant
  exact div_pos (by norm_num) (sub_pos.mpr lemma83_regular_radius_lt_one)

lemma lemma83_regular_correction_norm_error (b c t x : ℂ)
    (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) (ht : ‖t‖ ≤ 1/2)
    (hx : ‖x‖ ≤ lemma83RegularRadius) :
    ‖lemma83RegularCorrection b c t x - 1‖ ≤
      lemma83RegularConstant * ‖t‖ * ‖x‖ := by
  have hb' : ‖1-b‖ ≤ 2 := by
    have := norm_sub_le (1:ℂ) b
    norm_num only [norm_one] at this
    linarith
  have hc' : ‖1-c‖ ≤ 2 := by
    have := norm_sub_le (1:ℂ) c
    norm_num only [norm_one] at this
    linarith
  have ht' : 1/2 ≤ ‖1-t‖ := by
    have := norm_sub_norm_le (1:ℂ) t
    norm_num only [norm_one] at this
    linarith
  have hx' : 1-lemma83RegularRadius ≤ ‖1-x‖ := by
    have := norm_sub_norm_le (1:ℂ) x
    norm_num only [norm_one] at this
    linarith
  have hnum : ‖t*x*(1-b)*(1-c)‖ ≤ 4*‖t‖*‖x‖ := by
    simp only [norm_mul]
    nlinarith [norm_nonneg t, norm_nonneg x, norm_nonneg (1-b), norm_nonneg (1-c),
      mul_nonneg (norm_nonneg t) (norm_nonneg x),
      mul_le_mul hb' hc' (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 2)]
  have hden : (1/2)*(1-lemma83RegularRadius) ≤ ‖(1-t)*(1-x)‖ := by
    rw [norm_mul]
    exact mul_le_mul ht' hx' (le_of_lt (sub_pos.mpr lemma83_regular_radius_lt_one))
      (norm_nonneg _)
  calc
    _ = ‖t*x*(1-b)*(1-c)‖ / ‖(1-t)*(1-x)‖ := by
      rw [lemma83RegularCorrection]
      simp only [sub_sub_cancel_left, norm_neg, norm_div]
    _ ≤ (4*‖t‖*‖x‖)/((1/2)*(1-lemma83RegularRadius)) := by
      exact div_le_div₀ (by positivity) hnum (by
        exact mul_pos (by norm_num) (sub_pos.mpr lemma83_regular_radius_lt_one)) hden
    _ = _ := by
      unfold lemma83RegularConstant
      field_simp
      ring

lemma lemma83_prime_monomial_norm_rpow {q : ℕ} (hq : 0 < q) (s : ℂ) :
    ‖lemma32PrimeMonomial q s‖ = (q:ℝ)^(-s.re) := by
  rw [lemma32_prime_monomial_norm,Real.rpow_def_of_pos (Nat.cast_pos.mpr hq)]
  congr 1
  ring

lemma lemma83_shift_monomial_norm {q : ℕ} (hq : 0 < q) (β : ℂ) (hβ : β.re = 0) :
    ‖lemma32PrimeMonomial q β‖ = 1 := by
  simp [lemma83_prime_monomial_norm_rpow hq, hβ]

lemma lemma83_t_monomial_norm {q : ℕ} (hq : 0 < q) (β : ℂ) (hβ : β.re = 0) :
    ‖lemma32PrimeMonomial q (1-β)‖ = (q:ℝ)⁻¹ := by
  simp [lemma83_prime_monomial_norm_rpow hq,hβ,Real.rpow_neg_one]

lemma lemma83_character_monomial_norm_le {D : ℕ} (χ : RealPrimitiveCharacter D)
    (q : Nat.Primes) (s : ℂ) (hs : 9/10 ≤ s.re) :
    ‖χ.evalNat q.val * lemma32PrimeMonomial q.val s‖ ≤ (q.val:ℝ)^(-(9/10:ℝ)) := by
  rw [norm_mul]
  calc
    _ ≤ 1*‖lemma32PrimeMonomial q.val s‖ :=
      mul_le_mul_of_nonneg_right (χ.evalNat_norm_le_one _) (norm_nonneg _)
    _ = (q.val:ℝ)^(-s.re) := by rw [one_mul,lemma83_prime_monomial_norm_rpow q.property.pos]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast q.property.one_lt.le) (by linarith)

lemma lemma83_character_monomial_norm_radius {D : ℕ} (χ : RealPrimitiveCharacter D)
    (q : Nat.Primes) (s : ℂ) (hs : 9/10 ≤ s.re) :
    ‖χ.evalNat q.val * lemma32PrimeMonomial q.val s‖ ≤ lemma83RegularRadius := by
  apply (lemma83_character_monomial_norm_le χ q s hs).trans
  calc
    (q.val:ℝ)^(-(9/10:ℝ)) ≤ (2:ℝ)^(-(9/10:ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast q.property.two_le) (by norm_num)
    _ = _ := by rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2)]; unfold lemma83RegularRadius; congr 1; ring

noncomputable def lemma83RegularPrimeFactor {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) (j : Fin 3) (q : Nat.Primes) (s : ℂ) : ℂ :=
  lemma83RegularCorrection (lemma32PrimeMonomial q.val (β (j+1)))
    (lemma32PrimeMonomial q.val (β (j+2))) (lemma32PrimeMonomial q.val (1-β j))
    (χ.evalNat q.val * lemma32PrimeMonomial q.val s)

lemma lemma83_regular_prime_error_uniform {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) (hβ : ∀ i, (β i).re = 0) (j : Fin 3)
    (q : Nat.Primes) (s : ℂ) (hs : 9/10 ≤ s.re) :
    ‖lemma83RegularPrimeFactor χ β j q s - 1‖ ≤
      lemma83RegularConstant*(q.val:ℝ)^(-(19/10:ℝ)) := by
  have ht : ‖lemma32PrimeMonomial q.val (1-β j)‖ ≤ 1/2 := by
    rw [lemma83_t_monomial_norm q.property.pos _ (hβ j)]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2)
      (show (2:ℝ) ≤ q.val by exact_mod_cast q.property.two_le)
  have hb := lemma83_regular_correction_norm_error
    (lemma32PrimeMonomial q.val (β (j+1)))
    (lemma32PrimeMonomial q.val (β (j+2)))
    (lemma32PrimeMonomial q.val (1-β j))
    (χ.evalNat q.val * lemma32PrimeMonomial q.val s)
    (by rw [lemma83_shift_monomial_norm q.property.pos _ (hβ _)])
    (by rw [lemma83_shift_monomial_norm q.property.pos _ (hβ _)])
    ht (lemma83_character_monomial_norm_radius χ q s hs)
  rw [lemma83_t_monomial_norm q.property.pos _ (hβ j)] at hb
  refine hb.trans ?_
  calc
    _ ≤ lemma83RegularConstant * (q.val:ℝ)⁻¹ * (q.val:ℝ)^(-(9/10:ℝ)) :=
      mul_le_mul_of_nonneg_left (lemma83_character_monomial_norm_le χ q s hs)
        (mul_nonneg lemma83_regular_constant_pos.le (by positivity))
    _ = _ := by
      rw [← Real.rpow_neg_one, mul_assoc, ← Real.rpow_add (Nat.cast_pos.mpr q.property.pos)]
      norm_num

lemma lemma83_regular_prime_factor_differentiableOn {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) (hβ : ∀ i, (β i).re = 0) (j : Fin 3) (q : Nat.Primes) :
    DifferentiableOn ℂ (lemma83RegularPrimeFactor χ β j q) {s : ℂ | 9/10 < s.re} := by
  have hmon := (lemma32_prime_monomial_differentiable q.val).differentiableOn
    (s := {s : ℂ | 9/10 < s.re})
  have hx : DifferentiableOn ℂ (fun s : ℂ => χ.evalNat q.val * lemma32PrimeMonomial q.val s)
      {s : ℂ | 9/10 < s.re} := hmon.const_mul _
  have ht : 1-lemma32PrimeMonomial q.val (1-β j) ≠ 0 := by
    apply sub_ne_zero.mpr
    intro he
    have hn := lemma32_prime_monomial_norm_lt_one q.property.one_lt (1-β j)
      (by simp [hβ j])
    rw [← he] at hn
    norm_num at hn
  have hx' : ∀ s ∈ {s : ℂ | 9/10 < s.re},
      1-χ.evalNat q.val*lemma32PrimeMonomial q.val s ≠ 0 := by
    intro s hs
    apply sub_ne_zero.mpr
    intro he
    have hn := (lemma83_character_monomial_norm_radius χ q s hs.le).trans_lt
      lemma83_regular_radius_lt_one
    rw [← he] at hn
    norm_num at hn
  unfold lemma83RegularPrimeFactor lemma83RegularCorrection
  exact (((hx.const_mul _).mul_const _).mul_const _ |>.div
    ((hx.const_sub 1).const_mul _) (fun s hs => mul_ne_zero ht (hx' s hs))).const_sub 1

/-- Restrict the regular Euler product to any subset of primes, in particular primes outside dr. -/
noncomputable def lemma83RestrictedRegularFactor {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) (j : Fin 3) (P : Nat.Primes → Prop) (q : Nat.Primes) (s : ℂ) : ℂ :=
  if P q then lemma83RegularPrimeFactor χ β j q s else 1

noncomputable def lemma83RegularEulerProduct {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) (j : Fin 3) (P : Nat.Primes → Prop) (s : ℂ) : ℂ :=
  ∏' q : Nat.Primes, lemma83RestrictedRegularFactor χ β j P q s

lemma lemma83_restricted_regular_factor_differentiableOn {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) (hβ : ∀ i, (β i).re = 0) (j : Fin 3)
    (P : Nat.Primes → Prop) (q : Nat.Primes) :
    DifferentiableOn ℂ (lemma83RestrictedRegularFactor χ β j P q)
      {s : ℂ | 9/10 < s.re} := by
  unfold lemma83RestrictedRegularFactor
  by_cases hq : P q
  · simpa only [if_pos hq] using lemma83_regular_prime_factor_differentiableOn χ β hβ j q
  · simp only [if_neg hq]
    exact differentiableOn_const _

lemma lemma83_restricted_regular_error_uniform {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) (hβ : ∀ i, (β i).re = 0) (j : Fin 3)
    (P : Nat.Primes → Prop) (q : Nat.Primes) (s : ℂ) (hs : 9/10 ≤ s.re) :
    ‖lemma83RestrictedRegularFactor χ β j P q s-1‖ ≤
      lemma83RegularConstant*(q.val:ℝ)^(-(19/10:ℝ)) := by
  by_cases hq : P q
  · simpa [lemma83RestrictedRegularFactor,hq] using
      lemma83_regular_prime_error_uniform χ β hβ j q s hs
  · simp only [lemma83RestrictedRegularFactor,if_neg hq,sub_self,norm_zero]
    exact mul_nonneg lemma83_regular_constant_pos.le (Real.rpow_nonneg (Nat.cast_nonneg _) _)

lemma lemma83_regular_majorant_summable :
    Summable (fun q : Nat.Primes => lemma83RegularConstant*(q.val:ℝ)^(-(19/10:ℝ))) := by
  have hn : Summable (fun n : ℕ => (n:ℝ)^(-(19/10:ℝ))) := Real.summable_nat_rpow.mpr (by norm_num)
  exact (hn.subtype Nat.Prime).mul_left _

lemma lemma83_regular_products_locally_uniform {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) (hβ : ∀ i, (β i).re = 0) (j : Fin 3) (P : Nat.Primes → Prop) :
    TendstoLocallyUniformlyOn
      (fun S : Finset Nat.Primes => fun s : ℂ => ∏ q ∈ S,
        lemma83RestrictedRegularFactor χ β j P q s)
      (lemma83RegularEulerProduct χ β j P) atTop {s : ℂ | 9/10 < s.re} := by
  have hh := Summable.hasProdLocallyUniformlyOn_one_add
    (f := fun q : Nat.Primes => fun s : ℂ => lemma83RestrictedRegularFactor χ β j P q s-1)
    (isOpen_lt continuous_const Complex.continuous_re) lemma83_regular_majorant_summable
    (Filter.Eventually.of_forall fun q s hs =>
      lemma83_restricted_regular_error_uniform χ β hβ j P q s hs.le)
    (fun q => (lemma83_restricted_regular_factor_differentiableOn χ β hβ j P q).continuousOn.sub
      continuousOn_const)
  simpa only [hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn,add_sub_cancel,
    lemma83RegularEulerProduct] using hh

lemma lemma83_regular_euler_product_multipliable {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) (hβ : ∀ i, (β i).re = 0) (j : Fin 3) (P : Nat.Primes → Prop)
    (s : ℂ) (hs : 9/10 ≤ s.re) :
    Multipliable (fun q : Nat.Primes => lemma83RestrictedRegularFactor χ β j P q s) := by
  have hsumm : Summable (fun q : Nat.Primes => ‖lemma83RestrictedRegularFactor χ β j P q s-1‖) :=
    lemma83_regular_majorant_summable.of_nonneg_of_le (fun q => norm_nonneg _)
      (fun q => lemma83_restricted_regular_error_uniform χ β hβ j P q s hs)
  simpa only [add_sub_cancel] using multipliable_one_add_of_summable hsumm

lemma lemma83_regular_euler_product_analyticOnNhd {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) (hβ : ∀ i, (β i).re = 0) (j : Fin 3) (P : Nat.Primes → Prop) :
    AnalyticOnNhd ℂ (lemma83RegularEulerProduct χ β j P) {s : ℂ | 9/10 < s.re} := by
  apply DifferentiableOn.analyticOnNhd ?_ (isOpen_lt continuous_const Complex.continuous_re)
  apply (lemma83_regular_products_locally_uniform χ β hβ j P).differentiableOn
  · filter_upwards with S
    exact DifferentiableOn.fun_finsetProd fun q _ =>
      lemma83_restricted_regular_factor_differentiableOn χ β hβ j P q
  · exact isOpen_lt continuous_const Complex.continuous_re

noncomputable def lemma83RegularProductBound : ℝ :=
  Real.exp (∑' q : Nat.Primes, lemma83RegularConstant*(q.val:ℝ)^(-(19/10:ℝ)))

lemma lemma83_regular_product_bound_pos : 0 < lemma83RegularProductBound := Real.exp_pos _

lemma lemma83_regular_finite_product_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) (hβ : ∀ i, (β i).re = 0) (j : Fin 3) (P : Nat.Primes → Prop)
    (s : ℂ) (hs : 9/10 ≤ s.re) (S : Finset Nat.Primes) :
    ‖∏ q ∈ S, lemma83RestrictedRegularFactor χ β j P q s‖ ≤ lemma83RegularProductBound := by
  let f (q : Nat.Primes) : ℂ := lemma83RestrictedRegularFactor χ β j P q s
  have hh := S.norm_prod_one_add_sub_one_le (fun q => f q-1)
  simp only [add_sub_cancel] at hh
  have hsum : (∑ q ∈ S, ‖f q-1‖) ≤
      ∑' q : Nat.Primes, lemma83RegularConstant*(q.val:ℝ)^(-(19/10:ℝ)) := by
    calc
      _ ≤ ∑ q ∈ S, lemma83RegularConstant*(q.val:ℝ)^(-(19/10:ℝ)) :=
        Finset.sum_le_sum (fun q _ => lemma83_restricted_regular_error_uniform χ β hβ j P q s hs)
      _ ≤ _ := lemma83_regular_majorant_summable.sum_le_tsum S (fun q _ =>
        mul_nonneg lemma83_regular_constant_pos.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  have hnorm := norm_le_norm_sub_add (∏ q ∈ S, f q) (1:ℂ)
  norm_num only [norm_one] at hnorm
  calc
    _ ≤ Real.exp (∑ q ∈ S, ‖f q-1‖) := by dsimp [f] at *; linarith
    _ ≤ _ := Real.exp_le_exp.mpr hsum

lemma lemma83_regular_euler_product_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) (hβ : ∀ i, (β i).re = 0) (j : Fin 3) (P : Nat.Primes → Prop)
    (s : ℂ) (hs : 9/10 ≤ s.re) :
    ‖lemma83RegularEulerProduct χ β j P s‖ ≤ lemma83RegularProductBound := by
  have ht : Tendsto (fun S : Finset Nat.Primes => ∏ q ∈ S,
      lemma83RestrictedRegularFactor χ β j P q s) atTop
      (𝓝 (lemma83RegularEulerProduct χ β j P s)) :=
    (lemma83_regular_euler_product_multipliable χ β hβ j P s hs).hasProd
  apply le_of_tendsto ht.norm
  filter_upwards with S
  exact lemma83_regular_finite_product_bound χ β hβ j P s hs S

@[simp] lemma lemma83_regular_prime_factor_zero_shift {D : ℕ} (χ : RealPrimitiveCharacter D)
    (j : Fin 3) (q : Nat.Primes) (s : ℂ) :
    lemma83RegularPrimeFactor χ (fun _ => 0) j q s = 1 := by
  simp [lemma83RegularPrimeFactor,lemma32PrimeMonomial,lemma83RegularCorrection]

@[simp] lemma lemma83_restricted_regular_factor_zero_shift {D : ℕ} (χ : RealPrimitiveCharacter D)
    (j : Fin 3) (P : Nat.Primes → Prop) (q : Nat.Primes) (s : ℂ) :
    lemma83RestrictedRegularFactor χ (fun _ => 0) j P q s = 1 := by
  simp [lemma83RestrictedRegularFactor]

@[simp] lemma lemma83_regular_euler_product_zero_shift {D : ℕ} (χ : RealPrimitiveCharacter D)
    (j : Fin 3) (P : Nat.Primes → Prop) (s : ℂ) :
    lemma83RegularEulerProduct χ (fun _ => 0) j P s = 1 := by
  simp [lemma83RegularEulerProduct]

end ZhangLS.Spec
