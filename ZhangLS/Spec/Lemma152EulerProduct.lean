import ZhangLS.Spec.Lemma152CorrectionBounds
import ZhangLS.Spec.Lemma152LocalSeries
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex Filter Topology Set
open scoped Classical
set_option maxHeartbeats 1500000

noncomputable def lemma152PrimeFactor {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (q : Nat.Primes) (s : ℂ) : ℂ :=
  lemma152LocalCorrection (lemma32PrimeMonomial q.val (β 0))
    (lemma32PrimeMonomial q.val (β 1)) (q.val:ℂ)⁻¹ (χ.evalNat q.val)
      (lemma32PrimeMonomial q.val s)

noncomputable def lemma152EulerProduct {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (s : ℂ) : ℂ := ∏' q : Nat.Primes, lemma152PrimeFactor χ β q s

lemma lemma152_monomial_norm_le (q : Nat.Primes) (s : ℂ) (hs : 9/10 ≤ s.re) :
    ‖lemma32PrimeMonomial q.val s‖ ≤ (q.val:ℝ)^(-(9/10:ℝ)) := by
  rw [lemma83_prime_monomial_norm_rpow q.property.pos]
  exact Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast q.property.one_lt.le) (by linarith)

lemma lemma152_monomial_norm_radius (q : Nat.Primes) (s : ℂ) (hs : 9/10 ≤ s.re) :
    ‖lemma32PrimeMonomial q.val s‖ ≤ lemma83RegularRadius := by
  apply (lemma152_monomial_norm_le q s hs).trans
  calc
    (q.val:ℝ)^(-(9/10:ℝ)) ≤ (2:ℝ)^(-(9/10:ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast q.property.two_le) (by norm_num)
    _ = _ := by
      rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2)]
      unfold lemma83RegularRadius
      congr 1
      ring

lemma lemma152_prime_error_uniform {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (hβ : ∀ i, (β i).re = 0) (q : Nat.Primes)
    (s : ℂ) (hs : 9/10 ≤ s.re) :
    ‖lemma152PrimeFactor χ β q s-1‖ ≤
      lemma152CorrectionConstant*(q.val:ℝ)^(-(19/10:ℝ)) := by
  have hu : ‖(q.val:ℂ)⁻¹‖ ≤ 1/2 := by
    rw [norm_inv,Complex.norm_natCast]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2)
      (show (2:ℝ) ≤ q.val by exact_mod_cast q.property.two_le)
  have hh := lemma152_correction_norm_error
    (lemma32PrimeMonomial q.val (β 0)) (lemma32PrimeMonomial q.val (β 1))
    (q.val:ℂ)⁻¹ (χ.evalNat q.val) (lemma32PrimeMonomial q.val s)
    (by rw [lemma83_shift_monomial_norm q.property.pos _ (hβ 0)])
    (by rw [lemma83_shift_monomial_norm q.property.pos _ (hβ 1)])
    hu (χ.evalNat_norm_le_one _) (lemma152_monomial_norm_radius q s hs)
  rw [norm_inv,Complex.norm_natCast] at hh
  refine hh.trans ?_
  calc
    _ ≤ lemma152CorrectionConstant*(q.val:ℝ)⁻¹*(q.val:ℝ)^(-(9/10:ℝ)) :=
      mul_le_mul_of_nonneg_left (lemma152_monomial_norm_le q s hs)
        (mul_nonneg lemma152_correction_constant_pos.le (by positivity))
    _ = _ := by
      rw [← Real.rpow_neg_one,mul_assoc,← Real.rpow_add (Nat.cast_pos.mpr q.property.pos)]
      norm_num

lemma lemma152_prime_factor_differentiableOn {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (q : Nat.Primes) :
    DifferentiableOn ℂ (lemma152PrimeFactor χ β q) {s : ℂ | 9/10 < s.re} := by
  intro s hs
  have hm : DifferentiableAt ℂ (lemma32PrimeMonomial q.val) s :=
    lemma32_prime_monomial_differentiable q.val s
  have hxu : ‖lemma32PrimeMonomial q.val s‖ < 1 :=
    (lemma152_monomial_norm_radius q s hs.le).trans_lt lemma83_regular_radius_lt_one
  have hvx : 1-χ.evalNat q.val*lemma32PrimeMonomial q.val s ≠ 0 :=
    lemma83_one_sub_ne_zero (lt_of_le_of_lt (by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (χ.evalNat_norm_le_one q.val)) hxu)
  have hx : 1-lemma32PrimeMonomial q.val s ≠ 0 := lemma83_one_sub_ne_zero hxu
  have hu0 : ‖(q.val:ℂ)⁻¹‖ < 1 := by
    rw [norm_inv,Complex.norm_natCast]
    exact (inv_lt_one₀ (Nat.cast_pos.mpr q.property.pos)).mpr (by exact_mod_cast q.property.one_lt)
  have hu : 1-(q.val:ℂ)⁻¹ ≠ 0 := lemma83_one_sub_ne_zero hu0
  have hvu : 1-χ.evalNat q.val*(q.val:ℂ)⁻¹ ≠ 0 :=
    lemma83_one_sub_ne_zero (lt_of_le_of_lt (by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (χ.evalNat_norm_le_one q.val)) hu0)
  have hd1 := mul_ne_zero hu hvx
  have hd2 := mul_ne_zero (mul_ne_zero (mul_ne_zero hu hvu) hx) hvx
  apply DifferentiableAt.differentiableWithinAt
  unfold lemma152PrimeFactor lemma152LocalCorrection
  fun_prop (disch := first | exact hd1 | exact hd2)

lemma lemma152_majorant_summable :
    Summable (fun q : Nat.Primes => lemma152CorrectionConstant*(q.val:ℝ)^(-(19/10:ℝ))) := by
  have hn : Summable (fun n : ℕ => (n:ℝ)^(-(19/10:ℝ))) := Real.summable_nat_rpow.mpr (by norm_num)
  exact (hn.subtype Nat.Prime).mul_left _

lemma lemma152_products_locally_uniform {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (hβ : ∀ i, (β i).re = 0) :
    TendstoLocallyUniformlyOn
      (fun S : Finset Nat.Primes => fun s : ℂ => ∏ q ∈ S, lemma152PrimeFactor χ β q s)
      (lemma152EulerProduct χ β) atTop {s : ℂ | 9/10 < s.re} := by
  have hh := Summable.hasProdLocallyUniformlyOn_one_add
    (f := fun q : Nat.Primes => fun s : ℂ => lemma152PrimeFactor χ β q s-1)
    (isOpen_lt continuous_const Complex.continuous_re) lemma152_majorant_summable
    (Filter.Eventually.of_forall fun q s hs => lemma152_prime_error_uniform χ β hβ q s hs.le)
    (fun q => (lemma152_prime_factor_differentiableOn χ β q).continuousOn.sub continuousOn_const)
  simpa only [hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn,add_sub_cancel,
    lemma152EulerProduct] using hh

lemma lemma152_euler_product_multipliable {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (hβ : ∀ i, (β i).re = 0) (s : ℂ) (hs : 9/10 ≤ s.re) :
    Multipliable (fun q : Nat.Primes => lemma152PrimeFactor χ β q s) := by
  have hsumm : Summable (fun q : Nat.Primes => ‖lemma152PrimeFactor χ β q s-1‖) :=
    lemma152_majorant_summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun q => lemma152_prime_error_uniform χ β hβ q s hs)
  simpa only [add_sub_cancel] using multipliable_one_add_of_summable hsumm

lemma lemma152_euler_product_analyticOnNhd {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (hβ : ∀ i, (β i).re = 0) :
    AnalyticOnNhd ℂ (lemma152EulerProduct χ β) {s : ℂ | 9/10 < s.re} := by
  apply DifferentiableOn.analyticOnNhd ?_ (isOpen_lt continuous_const Complex.continuous_re)
  apply (lemma152_products_locally_uniform χ β hβ).differentiableOn
  · filter_upwards with S
    exact DifferentiableOn.fun_finsetProd fun q _ => lemma152_prime_factor_differentiableOn χ β q
  · exact isOpen_lt continuous_const Complex.continuous_re

end ZhangLS.Spec
