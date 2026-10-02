import ZhangLS.Spec.Proposition71DeltaOneSeries

/-! # The genuine finite-short/infinite-long Δ₁ transform

The two arbitrary coefficient sequences are independent of any character in
Z. The actual q n scale and the factors 1/q and 1/n are kept exactly.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Finset
open scoped Classical
set_option maxHeartbeats 3000000

noncomputable def proposition71FrontDominantIntegrand (D : ℕ) (c : ℕ → ℂ)
    (S : Finset ℕ) (a : ℕ → ℂ) (q : ℝ) (t : ℝ) : ℂ :=
  (q : ℂ)^(((3/2 : ℂ)+(t : ℂ)*I)-1)*LSeries c ((3/2 : ℂ)+(t : ℂ)*I)*
    (∑n∈S, a n*(n : ℂ)^(((3/2 : ℂ)+(t : ℂ)*I)-1))*proposition71GammaOmegaKernel D t

noncomputable def proposition71DeltaOneDoubleTerm (D : ℕ) (c : ℕ → ℂ)
    (S : Finset ℕ) (a : ℕ → ℂ) (q : ℝ) (m : ℕ) : ℂ :=
  if m=0 then 0 else c m*∑n∈S, (a n/(n : ℂ))*lemma53PaperDeltaOne D ((m : ℝ)/(q*(n : ℝ)))

lemma proposition71_positive_shifted_power_product {q n : ℝ} (hq : 0<q) (hn : 0<n) (s : ℂ) :
    (q : ℂ)^(s-1)*(n : ℂ)^(s-1)=
      (q : ℂ)⁻¹*(n : ℂ)⁻¹*((q*n : ℝ) : ℂ)^s := by
  rw [Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr hq.ne'),
    Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr hn.ne'),Complex.cpow_one,Complex.cpow_one,
    Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg hq.le hn.le]
  ring

lemma proposition71_front_dominant_finite_expansion (D : ℕ) (c : ℕ → ℂ)
    (S : Finset ℕ) (hS : ∀n∈S, 0<n) (a : ℕ → ℂ) {q : ℝ} (hq : 0<q) (t : ℝ) :
    proposition71FrontDominantIntegrand D c S a q t=
      (q : ℂ)⁻¹*∑n∈S, (a n/(n : ℂ))*
        (LSeries c ((3/2 : ℂ)+(t : ℂ)*I)*((q*(n : ℝ) : ℝ) : ℂ)^((3/2 : ℂ)+(t : ℂ)*I)*
          proposition71GammaOmegaKernel D t) := by
  unfold proposition71FrontDominantIntegrand
  rw [mul_sum,sum_mul,mul_sum]
  apply sum_congr rfl; intro n hn
  have hnp : 0<(n : ℝ) := by exact_mod_cast hS n hn
  have he := proposition71_positive_shifted_power_product hq hnp ((3/2 : ℂ)+(t : ℂ)*I)
  simp only [Complex.ofReal_natCast] at he
  calc
    _=(LSeries c ((3/2 : ℂ)+(t : ℂ)*I)*a n*proposition71GammaOmegaKernel D t)*
        ((q : ℂ)^(((3/2 : ℂ)+(t : ℂ)*I)-1)*(n : ℂ)^(((3/2 : ℂ)+(t : ℂ)*I)-1)) := by ring
    _=_ := by rw [he]; ring

/-- Exact normalization of the actual infinite-long, finite-short transform. -/
theorem proposition71_actual_delta_one_double_series {D : ℕ} (hD : 1<D)
    (c : ℕ → ℂ) (hseries : LSeriesSummable c (3/2 : ℂ))
    (S : Finset ℕ) (hS : ∀n∈S, 0<n) (a : ℕ → ℂ) {q : ℝ} (hq : 0<q) :
    Integrable (proposition71FrontDominantIntegrand D c S a q) ∧
      Summable (proposition71DeltaOneDoubleTerm D c S a q) ∧
        ((1/(2*Real.pi) : ℝ) : ℂ)*(∫t : ℝ, proposition71FrontDominantIntegrand D c S a q t)=
          (q : ℂ)⁻¹*(∑' m, proposition71DeltaOneDoubleTerm D c S a q m) := by
  let F := fun (n : ℕ) (t : ℝ) => LSeries c ((3/2 : ℂ)+(t : ℂ)*I)*
    ((q*(n : ℝ) : ℝ) : ℂ)^((3/2 : ℂ)+(t : ℂ)*I)*proposition71GammaOmegaKernel D t
  let G := fun (n m : ℕ) => if m=0 then (0 : ℂ) else c m*lemma53PaperDeltaOne D ((m : ℝ)/(q*(n : ℝ)))
  have hsingle (n : ℕ) (hn : n∈S) := proposition71_actual_delta_one_series hD c
    (mul_pos hq (by exact_mod_cast hS n hn : 0<(n : ℝ))) hseries
  have hI (n : ℕ) (hn : n∈S) : Integrable (fun t : ℝ => (a n/(n : ℂ))*F n t) :=
    (hsingle n hn).1.const_mul _
  have hfun : proposition71FrontDominantIntegrand D c S a q=
      fun t : ℝ => (q : ℂ)⁻¹*∑n∈S, (a n/(n : ℂ))*F n t :=
    funext (proposition71_front_dominant_finite_expansion D c S hS a hq)
  have hint : Integrable (proposition71FrontDominantIntegrand D c S a q) := by
    rw [hfun]
    exact (integrable_finsetSum S hI).const_mul _
  have hterm (m : ℕ) : proposition71DeltaOneDoubleTerm D c S a q m=
      ∑n∈S, (a n/(n : ℂ))*G n m := by
    by_cases hm : m=0
    · subst m; simp [proposition71DeltaOneDoubleTerm,G]
    · simp only [proposition71DeltaOneDoubleTerm,if_neg hm,G,mul_sum]
      apply sum_congr rfl; intro n hn; ring
  have hsum := hasSum_sum (s := S) (fun n hn => ((hsingle n hn).2.1.hasSum).mul_left (a n/(n : ℂ)))
  have hsum' : HasSum (proposition71DeltaOneDoubleTerm D c S a q)
      (∑n∈S, (a n/(n : ℂ))*(∑' m, G n m)) := by
    apply hsum.congr
    intro T
    apply Finset.sum_congr rfl
    intro m hm
    exact (hterm m).symm
  refine ⟨hint,hsum'.summable,?_⟩
  rw [hsum'.tsum_eq,hfun,integral_const_mul,integral_finsetSum S hI]
  simp_rw [integral_const_mul]
  calc
    _=(q : ℂ)⁻¹*∑n∈S, (a n/(n : ℂ))*
        ((((1/(2*Real.pi) : ℝ) : ℂ))*(∫t : ℝ, F n t)) := by
      simp only [mul_sum]
      apply sum_congr rfl; intro n hn; ring
    _=_ := by
      congr 1
      apply sum_congr rfl; intro n hn
      rw [(hsingle n hn).2.2]

end ZhangLS.Spec
