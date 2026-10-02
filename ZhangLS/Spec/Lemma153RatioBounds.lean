import ZhangLS.Spec.Lemma153LocalBounds
import ZhangLS.Spec.Lemma153PrimeLocal
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 2500000

lemma lemma153_kappa_rational_bounds (a b y : ℂ)
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hy : ‖y‖ ≤ 1/2) :
    ‖lemma152KappaRational a b y‖ ≤ 6 ∧
      ‖lemma152KappaRational a b y-1‖ ≤ 14*‖y‖ := by
  have hay : ‖a*y‖ ≤ 1/2 := by rw [norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) ha).trans hy
  have hby : ‖b*y‖ ≤ 1/2 := by rw [norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) hb).trans hy
  have ha' : 1/2 ≤ ‖1-a*y‖ := by have := norm_sub_norm_le (1:ℂ) (a*y); rw [norm_one] at this; linarith
  have hb' : 1/2 ≤ ‖1-b*y‖ := by have := norm_sub_norm_le (1:ℂ) (b*y); rw [norm_one] at this; linarith
  have hd : 1/4 ≤ ‖(1-a*y)*(1-b*y)‖ := by rw [norm_mul]; nlinarith [norm_nonneg (1-a*y),norm_nonneg (1-b*y)]
  have hn : ‖1-y‖ ≤ 3/2 := by have := norm_sub_le (1:ℂ) y; rw [norm_one] at this; linarith
  constructor
  · rw [lemma152KappaRational,norm_div]
    exact (div_le_div₀ (by positivity) hn (by norm_num : (0:ℝ)<1/4) hd).trans (by norm_num)
  · have han := lemma83_one_sub_ne_zero (hay.trans_lt (by norm_num))
    have hbn := lemma83_one_sub_ne_zero (hby.trans_lt (by norm_num))
    have he : lemma152KappaRational a b y-1 =
        (y*(a+b-1)-a*b*y^2)/((1-a*y)*(1-b*y)) := by
      unfold lemma152KappaRational
      repeat' field_simp [han,hbn,mul_comm]
      all_goals ring
    have hab : ‖a+b-1‖ ≤ 3 := by
      have h1 := norm_sub_le (a+b) (1:ℂ)
      have h2 := norm_add_le a b
      rw [norm_one] at h1
      linarith
    have hnum : ‖y*(a+b-1)-a*b*y^2‖ ≤ (7/2)*‖y‖ := by
      apply (norm_sub_le _ _).trans
      simp only [norm_mul,norm_pow]
      have h1 := mul_le_mul_of_nonneg_left hab (norm_nonneg y)
      have h2 : ‖a‖*‖b‖ ≤ 1 := by nlinarith [norm_nonneg a,norm_nonneg b]
      have h3 := mul_le_mul_of_nonneg_right h2 (sq_nonneg ‖y‖)
      nlinarith [norm_nonneg y]
    rw [he,norm_div]
    apply (div_le_div₀ (by positivity) hnum (by norm_num : (0:ℝ)<1/4) hd).trans
    ring_nf
    exact le_rfl

lemma lemma153_lambda_rational_difference (a b u v : ℂ)
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hu : ‖u‖ ≤ 1/2) (hv : ‖v‖ ≤ 1) :
    ‖lemma153LocalLambda a b u v-1‖ ≤ 7*‖u‖ := by
  have hvu : ‖v*u‖ ≤ 1/2 := by rw [norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) hv).trans hu
  have hvun := lemma83_one_sub_ne_zero (hvu.trans_lt (by norm_num))
  have hd : 1/2 ≤ ‖1-v*u‖ := by have := norm_sub_norm_le (1:ℂ) (v*u); rw [norm_one] at this; linarith
  have hcoef : ‖1-a-b‖ ≤ 3 := by
    have h1 := norm_sub_le (1-a) b
    have h2 := norm_sub_le (1:ℂ) a
    rw [norm_one] at h2
    linarith
  have he : lemma153LocalLambda a b u v-1 =
      (v*u*(1-a-b)+a*b*v^2*u^2)/(1-v*u) := by
    unfold lemma153LocalLambda
    field_simp [hvun]
    ring
  have hnum : ‖v*u*(1-a-b)+a*b*v^2*u^2‖ ≤ (7/2)*‖u‖ := by
    apply (norm_add_le _ _).trans
    simp only [norm_mul,norm_pow]
    have hvu' : ‖v‖*‖u‖ ≤ ‖u‖ := mul_le_of_le_one_left (norm_nonneg _) hv
    have h1 := mul_le_mul hvu' hcoef (norm_nonneg _) (norm_nonneg _)
    have h2 : ‖a‖*‖b‖*‖v‖^2 ≤ 1 := by
      calc
        ‖a‖*‖b‖*‖v‖^2 ≤ 1*1*1^2 := by gcongr
        _ = 1 := by norm_num
    have h3 := mul_le_mul_of_nonneg_right h2 (sq_nonneg ‖u‖)
    nlinarith [norm_nonneg u]
  rw [he,norm_div]
  apply (div_le_div₀ (by positivity) hnum (by norm_num : (0:ℝ)<1/2) hd).trans
  ring_nf
  exact le_rfl

lemma lemma153_base_norm_difference {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (hβ : ∀ i, (β i).re = 0) (hp : p.Prime)
    (y : ℂ) (hy : ‖y‖ ≤ 1/2) :
    ‖lemma153BaseClosed ((p:ℂ)^(-β 0)) ((p:ℂ)^(-β 1)) (p:ℂ)⁻¹ (χ.evalNat p) y-1‖ ≤
      384*‖y‖ := by
  have hs := lemma152_coefficient_local_norm_series χ β hβ hp y hy
  have hb := lemma153_base_closed_hasSum χ β hβ hp y (hy.trans_lt (by norm_num))
  have ht : HasSum (fun n : ℕ => lemma152Coefficient χ β 1 1 (p^(n+1))*y^(n+1))
      (lemma153BaseClosed ((p:ℂ)^(-β 0)) ((p:ℂ)^(-β 1)) (p:ℂ)⁻¹ (χ.evalNat p) y-1) := by
    simpa using (hasSum_nat_add_iff' 1).mpr hb
  have hsn : Summable (fun n : ℕ => ‖lemma152Coefficient χ β 1 1 (p^(n+1))*y^(n+1)‖) :=
    summable_norm_iff.mpr ht.summable
  have hsum : (∑' n : ℕ, ‖lemma152Coefficient χ β 1 1 (p^(n+1))*y^(n+1)‖) ≤ 384*‖y‖ := by
    have hh := hs.2
    rw [hs.1.tsum_eq_zero_add] at hh
    simp only [pow_zero,lemma152_coefficient_one,mul_one,norm_one] at hh
    linarith
  rw [← ht.tsum_eq]
  exact (norm_tsum_le_tsum_norm hsn).trans hsum

/-- The three normalized true local ratios satisfy a uniform O(1/q)
first-order bound and a uniform mixed-ratio bound. -/
lemma lemma153_normalized_ratio_bounds (B lam K A y : ℂ) (u : ℝ)
    (hu : 0 ≤ u) (hu1 : u ≤ 1/2) (hy : ‖y‖ = u)
    (hB : B ≠ 0) (hBi : ‖B⁻¹‖ ≤ 18) (hB1 : ‖B-1‖ ≤ 384*u)
    (hlam : ‖lam‖ ≤ 5) (hlam1 : ‖lam-1‖ ≤ 7*u)
    (hK : ‖K‖ ≤ 6) (hK1 : ‖K-1‖ ≤ 14*u) (hA : ‖A‖ ≤ 2) :
    ‖(B+lam*A*y*K)/B-1‖ ≤ 10000*u ∧
      ‖lam*((1-A*y)*K)/B-1‖ ≤ 10000*u ∧ ‖lam*K/B‖ ≤ 10000 := by
  have hcross : ‖lam*A*y*K‖ ≤ 60*u := by
    simp only [norm_mul,hy]
    calc
      _ ≤ 5*2*u*6 := by gcongr
      _ = _ := by ring
  have hprod : ‖lam*K-1‖ ≤ 77*u := by
    rw [show lam*K-1 = lam*(K-1)+(lam-1) by ring]
    apply (norm_add_le _ _).trans
    rw [norm_mul]
    have hh := mul_le_mul hlam hK1 (norm_nonneg _) (by norm_num : (0:ℝ)≤5)
    linarith
  have hnum : ‖lam*((1-A*y)*K)-B‖ ≤ 521*u := by
    rw [show lam*((1-A*y)*K)-B = (lam*K-1)-lam*A*y*K-(B-1) by ring]
    apply (norm_sub_le _ _).trans
    apply (add_le_add (norm_sub_le _ _) le_rfl).trans
    linarith
  refine ⟨?_,?_,?_⟩
  · rw [show (B+lam*A*y*K)/B-1 = (lam*A*y*K)*B⁻¹ by field_simp
      <;> ring,norm_mul]
    have hh := mul_le_mul hcross hBi (norm_nonneg _) (by positivity : 0 ≤ 60*u)
    nlinarith
  · rw [show lam*((1-A*y)*K)/B-1 = (lam*((1-A*y)*K)-B)*B⁻¹ by field_simp
      <;> ring,norm_mul]
    have hh := mul_le_mul hnum hBi (norm_nonneg _) (by positivity : 0 ≤ 521*u)
    nlinarith
  · simp only [div_eq_mul_inv,norm_mul]
    calc
      ‖lam‖*‖K‖*‖B⁻¹‖ ≤ 5*6*18 := by gcongr
      _ ≤ 10000 := by norm_num

end ZhangLS.Spec
