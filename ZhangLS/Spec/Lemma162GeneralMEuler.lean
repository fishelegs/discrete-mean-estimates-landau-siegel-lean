import ZhangLS.Spec.Lemma162ActualMLocal
import ZhangLS.Spec.Lemma162GeneralMSeries
import ZhangLS.Spec.Lemma161EulerProduct
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex Filter Topology Set
open scoped Classical
set_option maxHeartbeats 2500000

noncomputable def lemma162GeneralMEulerProduct {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (d l : ℕ) (s : ℂ) : ℂ :=
  ∏' q : Nat.Primes, lemma162GeneralMPrimeFactor χ β d l q s

noncomputable def lemma162GeneralMExceptionBound : ℝ :=
  2+lemma152CorrectionConstant+10/(1-lemma83RegularRadius)

lemma lemma162_general_m_exception_bound_pos : 0 < lemma162GeneralMExceptionBound := by
  have hC := lemma152_correction_constant_pos
  have hR := sub_pos.mpr lemma83_regular_radius_lt_one
  unfold lemma162GeneralMExceptionBound
  positivity

lemma lemma162_general_m_prime_error_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (d l : ℕ) (q : Nat.Primes)
    (s : ℂ) (hs : 9/10 ≤ s.re) :
    ‖lemma162GeneralMPrimeFactor χ β d l q s-1‖ ≤
      lemma152CorrectionConstant*(q.val:ℝ)^(-(19/10:ℝ)) +
        if q.val ∣ d*l then lemma162GeneralMExceptionBound else 0 := by
  by_cases hex : q.val ∣ d*l
  · rw [if_pos hex]
    have hbase : ‖lemma161PrimeFactor χ β q s‖ ≤ 1+lemma152CorrectionConstant := by
      have hnorm : ‖lemma161PrimeFactor χ β q s‖ ≤ 1+lemma152CorrectionConstant*(q.val:ℝ)^(-(19/10:ℝ)) := by
        have he := lemma161_prime_error_uniform χ β hβ q s hs
        have hn := norm_add_le (lemma161PrimeFactor χ β q s-1) (1:ℂ)
        simp only [sub_add_cancel,norm_one] at hn
        linarith
      apply hnorm.trans
      have hp := Real.rpow_le_one_of_one_le_of_nonpos
        (show (1:ℝ) ≤ q.val by exact_mod_cast q.property.one_lt.le) (by norm_num : -(19/10:ℝ) ≤ 0)
      have hC := lemma152_correction_constant_pos
      nlinarith
    let u : ℂ := (q.val:ℂ)⁻¹
    let v := χ.evalNat q.val
    let x := lemma32PrimeMonomial q.val s
    let δ : ℝ := 1-lemma83RegularRadius
    have hδ : 0<δ := sub_pos.mpr lemma83_regular_radius_lt_one
    have hu : ‖u‖ ≤ 1/2 := by
      dsimp [u]
      rw [norm_inv,Complex.norm_natCast]
      simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2)
        (show (2:ℝ) ≤ q.val by exact_mod_cast q.property.two_le)
    have hx : ‖x‖ ≤ lemma83RegularRadius := lemma152_monomial_norm_radius q s hs
    have hx1 : ‖x‖ ≤ 1 := hx.trans lemma83_regular_radius_lt_one.le
    have hv : ‖v‖ ≤ 1 := χ.evalNat_norm_le_one _
    have hvx : ‖v*x‖ ≤ lemma83RegularRadius := by
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) hv).trans hx
    have hdv : δ ≤ ‖1-v*x‖ := lemma152_one_sub_norm_lower hvx
    have hdu : 1/2 ≤ ‖1-u‖ := by
      have hh := lemma152_one_sub_norm_lower hu
      linarith only [hh]
    have hlarge : ‖lemma162GeneralMPrimeFactor χ β d l q s‖ ≤
        1+lemma152CorrectionConstant+10/δ := by
      unfold lemma162GeneralMPrimeFactor
      change ‖if q.val ∣ d then if q.val ∣ l then (1-v*x)⁻¹ else
          (1-v*x/(1-u))/(1-v*x) else if q.val ∣ l then
          lemma161PrimeFactor χ β q s+lemma161LambdaFactor χ β q.val 1*v*x/((1-u)*(1-v*x))
          else lemma161PrimeFactor χ β q s‖ ≤ _
      split_ifs
      · rw [norm_inv]
        have hi : ‖1-v*x‖⁻¹ ≤ 1/δ := by
          simpa only [one_div] using one_div_le_one_div_of_le hδ hdv
        have hC := lemma152_correction_constant_pos
        have hi0 : 0 ≤ 1/δ := by positivity
        rw [show 10/δ = 10*(1/δ) by ring]
        nlinarith
      · have hnum : ‖1-v*x/(1-u)‖ ≤ 3 := by
          apply (norm_sub_le _ _).trans
          rw [norm_one,norm_div,norm_mul]
          have hn : ‖v‖*‖x‖ ≤ 1 := by nlinarith [norm_nonneg v,norm_nonneg x]
          have hh := div_le_div₀ (by norm_num) hn (by norm_num : (0:ℝ)<1/2) hdu
          norm_num at hh
          linarith
        rw [norm_div]
        have hh := div_le_div₀ (by positivity) hnum hδ hdv
        have hC := lemma152_correction_constant_pos
        have hi0 : 0 ≤ 1/δ := by positivity
        have he : 3/δ = 3*(1/δ) := by ring
        have he10 : 10/δ = 10*(1/δ) := by ring
        rw [he] at hh
        rw [he10]
        nlinarith
      · apply (norm_add_le _ _).trans
        have hl := lemma161_lambda_norm_le χ β hβ q.property
        have hterm : ‖lemma161LambdaFactor χ β q.val 1*v*x/((1-u)*(1-v*x))‖ ≤ 10/δ := by
          simp only [norm_div,norm_mul]
          have hn : ‖lemma161LambdaFactor χ β q.val 1‖*‖v‖*‖x‖ ≤ 5 := by
            calc
              ‖lemma161LambdaFactor χ β q.val 1‖*‖v‖*‖x‖ ≤ 5*1*1 := by gcongr
              _ = 5 := by norm_num
          have hden : (1/2)*δ ≤ ‖1-u‖*‖1-v*x‖ := mul_le_mul hdu hdv hδ.le (norm_nonneg _)
          apply (div_le_div₀ (by positivity) hn (by positivity : 0 < (1/2)*δ) hden).trans
          have hδn : δ ≠ 0 := hδ.ne'
          field_simp
          norm_num
        linarith
      · exact hbase.trans (le_add_of_nonneg_right (by positivity))
    have hn := norm_sub_le (lemma162GeneralMPrimeFactor χ β d l q s) (1:ℂ)
    rw [norm_one] at hn
    have hmajor : 0 ≤ lemma152CorrectionConstant*(q.val:ℝ)^(-(19/10:ℝ)) := by
      have := lemma152_correction_constant_pos
      positivity
    dsimp [lemma162GeneralMExceptionBound,δ] at *
    linarith
  · rw [if_neg hex,add_zero]
    have hqd : ¬q.val ∣ d := fun h => hex (h.trans (dvd_mul_right d l))
    have hql : ¬q.val ∣ l := fun h => hex (h.trans (dvd_mul_left l d))
    simpa [lemma162GeneralMPrimeFactor,hqd,hql] using lemma161_prime_error_uniform χ β hβ q s hs

lemma lemma162_prime_divisor_indicator_summable {N : ℕ} (hN : N ≠ 0) (f : ℕ → ℝ) :
    Summable (fun q : Nat.Primes => if q.val ∣ N then f q.val else 0) := by
  have hn : Summable ((N.primeFactors : Set ℕ).indicator f) :=
    summable_subtype_iff_indicator.mp (N.primeFactors.finite_toSet.summable _)
  convert hn.subtype Nat.Prime using 1
  funext q
  have hm : q.val ∈ N.primeFactors ↔ q.val ∣ N := by simp [Nat.mem_primeFactors,q.property,hN]
  by_cases hq : q.val ∣ N
  · simp [hq,hm.mpr hq]
  · simp [hq,show q.val ∉ N.primeFactors by simpa only [hm] using hq]

noncomputable def lemma162GeneralMMajorant (d l : ℕ) (q : Nat.Primes) : ℝ :=
  lemma152CorrectionConstant*(q.val:ℝ)^(-(19/10:ℝ)) +
    if q.val ∣ d*l then lemma162GeneralMExceptionBound else 0

lemma lemma162_general_m_majorant_summable {d l : ℕ} (hd : d ≠ 0) (hl : l ≠ 0) :
    Summable (lemma162GeneralMMajorant d l) :=
  lemma152_majorant_summable.add
    (lemma162_prime_divisor_indicator_summable (mul_ne_zero hd hl) (fun _ => lemma162GeneralMExceptionBound))

lemma lemma162_general_m_prime_differentiableOn {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (d l : ℕ) (q : Nat.Primes) :
    DifferentiableOn ℂ (lemma162GeneralMPrimeFactor χ β d l q) {s : ℂ | 9/10 < s.re} := by
  intro s hs
  have hm := lemma32_prime_monomial_differentiable q.val s
  have hb : DifferentiableAt ℂ (lemma161PrimeFactor χ β q) s :=
    (lemma161_prime_factor_differentiableOn χ β q).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)
  have hx : ‖lemma32PrimeMonomial q.val s‖ < 1 :=
    (lemma152_monomial_norm_radius q s hs.le).trans_lt lemma83_regular_radius_lt_one
  have hvx : 1-χ.evalNat q.val*lemma32PrimeMonomial q.val s ≠ 0 :=
    lemma83_one_sub_ne_zero (lt_of_le_of_lt (by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (χ.evalNat_norm_le_one _)) hx)
  have hu : 1-(q.val:ℂ)⁻¹ ≠ 0 := lemma83_one_sub_ne_zero (by
    rw [norm_inv,Complex.norm_natCast]
    exact (inv_lt_one₀ (Nat.cast_pos.mpr q.property.pos)).mpr (by exact_mod_cast q.property.one_lt))
  apply DifferentiableAt.differentiableWithinAt
  unfold lemma162GeneralMPrimeFactor
  dsimp only
  split_ifs <;> fun_prop (disch := first | exact hvx | exact hu | exact mul_ne_zero hu hvx)

lemma lemma162_general_m_products_locally_uniform {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) {d l : ℕ} (hd : d ≠ 0) (hl : l ≠ 0) :
    TendstoLocallyUniformlyOn
      (fun S : Finset Nat.Primes => fun s : ℂ => ∏ q ∈ S, lemma162GeneralMPrimeFactor χ β d l q s)
      (lemma162GeneralMEulerProduct χ β d l) atTop {s : ℂ | 9/10 < s.re} := by
  have hh := Summable.hasProdLocallyUniformlyOn_one_add
    (f := fun q : Nat.Primes => fun s : ℂ => lemma162GeneralMPrimeFactor χ β d l q s-1)
    (isOpen_lt continuous_const Complex.continuous_re) (lemma162_general_m_majorant_summable hd hl)
    (Filter.Eventually.of_forall fun q s hs => lemma162_general_m_prime_error_bound χ β hβ d l q s hs.le)
    (fun q => (lemma162_general_m_prime_differentiableOn χ β d l q).continuousOn.sub continuousOn_const)
  simpa only [hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn,add_sub_cancel,
    lemma162GeneralMEulerProduct] using hh

lemma lemma162_general_m_euler_multipliable {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) {d l : ℕ} (hd : d ≠ 0) (hl : l ≠ 0)
    (s : ℂ) (hs : 9/10 ≤ s.re) :
    Multipliable (fun q : Nat.Primes => lemma162GeneralMPrimeFactor χ β d l q s) := by
  have hsum : Summable (fun q : Nat.Primes => ‖lemma162GeneralMPrimeFactor χ β d l q s-1‖) :=
    (lemma162_general_m_majorant_summable hd hl).of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun q => lemma162_general_m_prime_error_bound χ β hβ d l q s hs)
  simpa only [add_sub_cancel] using multipliable_one_add_of_summable hsum

lemma lemma162_general_m_analyticOnNhd {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) {d l : ℕ} (hd : d ≠ 0) (hl : l ≠ 0) :
    AnalyticOnNhd ℂ (lemma162GeneralMEulerProduct χ β d l) {s : ℂ | 9/10 < s.re} := by
  apply DifferentiableOn.analyticOnNhd ?_ (isOpen_lt continuous_const Complex.continuous_re)
  apply (lemma162_general_m_products_locally_uniform χ β hβ hd hl).differentiableOn
  · filter_upwards with S
    exact DifferentiableOn.fun_finsetProd fun q _ => lemma162_general_m_prime_differentiableOn χ β d l q
  · exact isOpen_lt continuous_const Complex.continuous_re

end ZhangLS.Spec
