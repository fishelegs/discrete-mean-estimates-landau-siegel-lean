import ZhangLS.Spec.Lemma153BaseClosed
import ZhangLS.Spec.Lemma153LocalCorrection
import ZhangLS.Spec.Lemma152PrimeComparison
import ZhangLS.Spec.Lemma152LocalNorm
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 2500000

/-- Every denominator in the local zeta/L removal is bounded away from zero
at the normalization point Re(s)=1. -/
lemma lemma153_local_removal_norm_le (a b v y : ℂ)
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hv : ‖v‖ ≤ 1) (hy : ‖y‖ ≤ 1/2) :
    ‖lemma152LocalRemoval a b v y‖ ≤ 9 := by
  have hay : ‖a*y‖ ≤ 1/2 := (by rw [norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) ha).trans hy)
  have hby : ‖b*y‖ ≤ 1/2 := (by rw [norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) hb).trans hy)
  have hvy : ‖v*y‖ ≤ 1/2 := (by rw [norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) hv).trans hy)
  have ha' : ‖1-a*y‖ ≤ 3/2 := by have := norm_sub_le (1:ℂ) (a*y); rw [norm_one] at this; linarith
  have hb' : ‖1-b*y‖ ≤ 3/2 := by have := norm_sub_le (1:ℂ) (b*y); rw [norm_one] at this; linarith
  have hy' : 1/2 ≤ ‖1-y‖ := by have := norm_sub_norm_le (1:ℂ) y; rw [norm_one] at this; linarith
  have hv' : 1/2 ≤ ‖1-v*y‖ := by have := norm_sub_norm_le (1:ℂ) (v*y); rw [norm_one] at this; linarith
  unfold lemma152LocalRemoval
  rw [norm_div,norm_mul,norm_mul]
  apply (div_le_div₀ (by positivity)
    (mul_le_mul ha' hb' (norm_nonneg _) (by norm_num : (0:ℝ)≤3/2))
    (by norm_num : (0:ℝ)<(1/2)*(1/2))
    (mul_le_mul hy' hv' (by norm_num) (norm_nonneg _))).trans
  norm_num

/-- Pointwise nonzero bound from the proved small-shift comparison, not an
assumption about a normalized local denominator. -/
lemma lemma153_base_norm_lower {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (hβ : ∀ i, (β i).re = 0) (hsmall : ∀ i, ‖β i‖ ≤ 1/10)
    (γ : ℂ) (hγ : γ.re = 0) (hγsmall : ‖γ‖ ≤ 1/10)
    (herr : 10*lemma152CorrectionConstant*(‖β 0‖+‖β 1‖+‖γ‖) ≤ 1/2)
    (q : Nat.Primes) :
    1/18 ≤ ‖lemma153BaseClosed ((q.val:ℂ)^(-β 0)) ((q.val:ℂ)^(-β 1))
      (q.val:ℂ)⁻¹ (χ.evalNat q.val) (lemma32PrimeMonomial q.val (1-γ))‖ := by
  let y := lemma32PrimeMonomial q.val (1-γ)
  have hs : (1-γ).re = 1 := by simp [hγ]
  have hd : ‖(1-γ)-1‖ = ‖γ‖ := by simp
  have hcmp := lemma152_prime_comparison χ β hβ hsmall q (1-γ)
    (by rw [hs]; norm_num) (by simpa only [hd] using hγsmall)
  rw [hd] at hcmp
  have hp1 : (1:ℝ) ≤ q.val := by exact_mod_cast q.property.one_lt.le
  have hpwr : (q.val:ℝ)^(-(17/10:ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hp1 (by norm_num)
  have herr0 : 0 ≤ 10*lemma152CorrectionConstant*(‖β 0‖+‖β 1‖+‖γ‖) := by
    have := lemma152_correction_constant_pos
    positivity
  have hdiff : ‖lemma152PrimeFactor χ β q (1-γ)-lemma152PrimeFactor χ (fun _ => 0) q 1‖ ≤ 1/2 :=
    hcmp.trans ((mul_le_of_le_one_right herr0 hpwr).trans herr)
  have hz : 1 ≤ ‖lemma152PrimeFactor χ (fun _ => 0) q 1‖ :=
    (lemma153_zero_center_factor_real χ q).2.trans (Complex.re_le_norm _)
  have hpn : 1/2 ≤ ‖lemma152PrimeFactor χ β q (1-γ)‖ := by
    have ht := norm_sub_norm_le (lemma152PrimeFactor χ (fun _ => 0) q 1)
      (lemma152PrimeFactor χ β q (1-γ))
    rw [norm_sub_rev] at ht
    linarith
  have hy : ‖y‖ ≤ 1/2 := lemma152_monomial_norm_half q.property (1-γ) (by rw [hs])
  have hca := lemma153_base_closed_correction_identity
    ((q.val:ℂ)^(-β 0)) ((q.val:ℂ)^(-β 1)) (q.val:ℂ)⁻¹ (χ.evalNat q.val) y
  have he : lemma152PrimeFactor χ β q (1-γ) =
      lemma152LocalRemoval ((q.val:ℂ)^(-β 0)) ((q.val:ℂ)^(-β 1)) (χ.evalNat q.val) y *
        lemma153BaseClosed ((q.val:ℂ)^(-β 0)) ((q.val:ℂ)^(-β 1))
          (q.val:ℂ)⁻¹ (χ.evalNat q.val) y := by
    unfold lemma152PrimeFactor
    rw [lemma32_prime_monomial_eq_cpow q.property.pos (β 0),
      lemma32_prime_monomial_eq_cpow q.property.pos (β 1),
      ← lemma153_actual_local_correction χ β hβ q.property y (hy.trans_lt (by norm_num)),
      (lemma153_base_closed_hasSum χ β hβ q.property y (hy.trans_lt (by norm_num))).tsum_eq]
  rw [he,norm_mul] at hpn
  have hR := lemma153_local_removal_norm_le ((q.val:ℂ)^(-β 0)) ((q.val:ℂ)^(-β 1))
    (χ.evalNat q.val) y (by rw [lemma83_cpow_shift_norm q.property.pos _ (hβ 0)])
    (by rw [lemma83_cpow_shift_norm q.property.pos _ (hβ 1)]) (χ.evalNat_norm_le_one _) hy
  have hb := mul_le_mul_of_nonneg_right hR
    (norm_nonneg (lemma153BaseClosed ((q.val:ℂ)^(-β 0)) ((q.val:ℂ)^(-β 1))
      (q.val:ℂ)⁻¹ (χ.evalNat q.val) y))
  dsimp [y] at *
  linarith

/-- Quantitative summable-shape bound for the corrected quadratic factor.
Here the ratio hypotheses will be obtained from the actual arithmetic local
series and the independently proved denominator lower bound. -/
lemma lemma153_shifted_correction_error_bound (B C E F lam t z : ℂ)
    (hB : B ≠ 0) (hcompat : B = C+lam*E-lam*F)
    (ht : ‖t‖ ≤ 1) (u K : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1/2) (hK : 1 ≤ K)
    (hg : ‖C/B-1‖ ≤ K*u) (he : ‖lam*E/B-1‖ ≤ K*u) (hf : ‖lam*F/B‖ ≤ K) :
    ‖lemma153ShiftedLocalCorrection B C E F lam t z-1‖ ≤
      4*K*u*‖z‖+6*K*‖z‖^2 := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hg' : ‖C/B‖ ≤ 1+K*u := by have := norm_le_norm_sub_add (C/B) (1:ℂ); rw [norm_one] at this; linarith
  have he' : ‖lam*E/B‖ ≤ 1+K*u := by have := norm_le_norm_sub_add (lam*E/B) (1:ℂ); rw [norm_one] at this; linarith
  have ht2 : ‖t^2‖ ≤ 1 := by rw [norm_pow]; nlinarith [norm_nonneg t]
  have htp : ‖t^2+t+1‖ ≤ 3 := by
    have h1 := norm_add_le (t^2+t) (1:ℂ)
    have h2 := norm_add_le (t^2) t
    rw [norm_one] at h1
    linarith
  have hlin : ‖2*(C+lam*E*t)/B-2*(1+t)‖ ≤ 4*K*u := by
    rw [show 2*(C+lam*E*t)/B-2*(1+t) = 2*((C/B-1)+t*(lam*E/B-1)) by ring,norm_mul]
    norm_num only [norm_ofNat]
    have hn : ‖(C/B-1)+t*(lam*E/B-1)‖ ≤ 2*K*u := by
      apply (norm_add_le _ _).trans
      rw [norm_mul]
      have hh := mul_le_mul ht he (norm_nonneg _) (by norm_num : (0:ℝ)≤1)
      nlinarith
    linarith
  have hquad : ‖(t^2*C+lam*E-(t^2+t+1)*lam*F)/B‖ ≤ 6*K := by
    rw [show (t^2*C+lam*E-(t^2+t+1)*lam*F)/B =
      t^2*(C/B)+lam*E/B-(t^2+t+1)*(lam*F/B) by ring]
    apply (norm_sub_le _ _).trans
    apply (add_le_add (norm_add_le _ _) le_rfl).trans
    simp only [norm_mul]
    have hh1 := mul_le_mul ht2 hg' (norm_nonneg _) (by norm_num : (0:ℝ)≤1)
    have hh2 := mul_le_mul htp hf (norm_nonneg _) (by norm_num : (0:ℝ)≤3)
    nlinarith
  rw [lemma153_shifted_local_polynomial B C E F lam t z hB hcompat]
  rw [show 1+(2*(C+lam*E*t)/B-2*(1+t))*z+
      (t^2*C+lam*E-(t^2+t+1)*lam*F)/B*z^2-1 =
        (2*(C+lam*E*t)/B-2*(1+t))*z+
          (t^2*C+lam*E-(t^2+t+1)*lam*F)/B*z^2 by ring]
  apply (norm_add_le _ _).trans
  simp only [norm_mul,norm_pow]
  gcongr

end ZhangLS.Spec
