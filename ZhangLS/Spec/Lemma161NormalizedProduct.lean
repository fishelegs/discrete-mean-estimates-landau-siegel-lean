import ZhangLS.Spec.Lemma161PrimeComparison
import ZhangLS.Spec.Lemma152ProductComparison

set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex Filter Topology Set
open scoped Classical
set_option maxHeartbeats 1500000

noncomputable def lemma161RestrictedFactor {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (P : Nat.Primes → Prop) (q : Nat.Primes) (s : ℂ) : ℂ :=
  if P q then lemma161PrimeFactor χ β q s else 1

noncomputable def lemma161RestrictedProduct {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (P : Nat.Primes → Prop) (s : ℂ) : ℂ :=
  ∏' q : Nat.Primes, lemma161RestrictedFactor χ β P q s

noncomputable def lemma161Star {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (s : ℂ) : ℂ :=
  if χ.evalNat 2 = 1 then
    2*lemma161RestrictedProduct χ β (fun q => 2 < q.val) s
  else lemma161EulerProduct χ β s

lemma lemma161_restricted_product_eq_subtype {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (P : Nat.Primes → Prop) (s : ℂ) :
    lemma161RestrictedProduct χ β P s =
      ∏' q : {q : Nat.Primes // P q}, lemma161PrimeFactor χ β q.val s := by
  symm
  exact tprod_subtype {q | P q} (fun q => lemma161PrimeFactor χ β q s)

lemma lemma161_restricted_error {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (P : Nat.Primes → Prop) (q : Nat.Primes)
    (s : ℂ) (hs : 9/10 ≤ s.re) :
    ‖lemma161RestrictedFactor χ β P q s-1‖ ≤
      lemma152CorrectionConstant*(q.val:ℝ)^(-(19/10:ℝ)) := by
  unfold lemma161RestrictedFactor
  split_ifs
  · exact lemma161_prime_error_uniform χ β hβ q s hs
  · simp only [sub_self,norm_zero]
    exact mul_nonneg lemma152_correction_constant_pos.le (Real.rpow_nonneg (Nat.cast_nonneg _) _)

lemma lemma161_restricted_multipliable {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (P : Nat.Primes → Prop) (s : ℂ) (hs : 9/10 ≤ s.re) :
    Multipliable (fun q : Nat.Primes => lemma161RestrictedFactor χ β P q s) := by
  have hsum : Summable (fun q : Nat.Primes => ‖lemma161RestrictedFactor χ β P q s-1‖) :=
    lemma152_majorant_summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun q => lemma161_restricted_error χ β hβ P q s hs)
  simpa only [add_sub_cancel] using multipliable_one_add_of_summable hsum

lemma lemma161_restricted_differentiableOn {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (P : Nat.Primes → Prop) (q : Nat.Primes) :
    DifferentiableOn ℂ (lemma161RestrictedFactor χ β P q) {s : ℂ | 9/10 < s.re} := by
  change DifferentiableOn ℂ (fun s => if P q then lemma161PrimeFactor χ β q s else 1) _
  by_cases hq : P q
  · simpa only [if_pos hq] using lemma161_prime_factor_differentiableOn χ β q
  · simpa only [if_neg hq] using
      (differentiableOn_const (1:ℂ) : DifferentiableOn ℂ (fun _ : ℂ => (1:ℂ)) _)

lemma lemma161_restricted_analytic {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (P : Nat.Primes → Prop) :
    AnalyticOnNhd ℂ (lemma161RestrictedProduct χ β P) {s : ℂ | 9/10 < s.re} := by
  have hprod : TendstoLocallyUniformlyOn
      (fun S : Finset Nat.Primes => fun s : ℂ => ∏ q ∈ S, lemma161RestrictedFactor χ β P q s)
      (lemma161RestrictedProduct χ β P) atTop {s : ℂ | 9/10 < s.re} := by
    have hh := Summable.hasProdLocallyUniformlyOn_one_add
      (f := fun q : Nat.Primes => fun s : ℂ => lemma161RestrictedFactor χ β P q s-1)
      (isOpen_lt continuous_const Complex.continuous_re) lemma152_majorant_summable
      (Filter.Eventually.of_forall fun q s hs => lemma161_restricted_error χ β hβ P q s hs.le)
      (fun q => (lemma161_restricted_differentiableOn χ β P q).continuousOn.sub continuousOn_const)
    simpa only [hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn,add_sub_cancel,
      lemma161RestrictedProduct] using hh
  apply DifferentiableOn.analyticOnNhd ?_ (isOpen_lt continuous_const Complex.continuous_re)
  apply hprod.differentiableOn
  · filter_upwards with S
    exact DifferentiableOn.fun_finsetProd fun q _ => lemma161_restricted_differentiableOn χ β P q
  · exact isOpen_lt continuous_const Complex.continuous_re

lemma lemma161_star_analytic {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) :
    AnalyticOnNhd ℂ (lemma161Star χ β) {s : ℂ | 9/10 < s.re} := by
  change AnalyticOnNhd ℂ (fun s => if χ.evalNat 2 = 1 then
    2*lemma161RestrictedProduct χ β (fun q => 2 < q.val) s else lemma161EulerProduct χ β s) _
  by_cases h : χ.evalNat 2 = 1
  · simp only [lemma161Star,if_pos h]
    exact analyticOnNhd_const.mul (lemma161_restricted_analytic χ β hβ _)
  · simpa only [lemma161Star,if_neg h] using lemma161_euler_product_analyticOnNhd χ β hβ

end ZhangLS.Spec
