import ZhangLS.Spec.Lemma121Definitions

set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace ZhangLS.Spec
open Complex Finset
open scoped Real

noncomputable def lemma121StrictPolynomial {D : ℕ} (χ : RealPrimitiveCharacter D)
    (x : ℝ) (s : ℂ) : ℂ :=
  ∑ n ∈ lemma82StrictCutoff x, χ.evalNat n*(n:ℂ)^(-s)

lemma lemma121_strict_polynomial_endpoint {D : ℕ} (χ : RealPrimitiveCharacter D)
    {x : ℝ} (hx : 1≤x) (s : ℂ) :
    lemma82FinitePolynomial χ x s-lemma121StrictPolynomial χ x s =
      if (⌊x⌋₊:ℝ)=x then χ.evalNat ⌊x⌋₊*(⌊x⌋₊:ℂ)^(-s) else 0 := by
  have hx0 : 0≤x := by linarith
  have hn : 1≤⌊x⌋₊ := (Nat.le_floor_iff hx0).mpr (by simpa using hx)
  unfold lemma82FinitePolynomial lemma121StrictPolynomial lemma82StrictCutoff
  rw [Finset.sum_filter,← Finset.sum_sub_distrib]
  have he (n : ℕ) (hn' : n ∈ Finset.Icc 1 ⌊x⌋₊) :
      χ.evalNat n*(n:ℂ)^(-s)-(if (n:ℝ)<x then χ.evalNat n*(n:ℂ)^(-s) else 0) =
      if n=⌊x⌋₊ then (if (⌊x⌋₊:ℝ)=x then χ.evalNat ⌊x⌋₊*(⌊x⌋₊:ℂ)^(-s) else 0) else 0 := by
    have hnx : (n:ℝ)≤x := (Nat.le_floor_iff hx0).mp (Finset.mem_Icc.mp hn').2
    by_cases hlt : (n:ℝ)<x
    · simp only [hlt,if_pos,sub_self]
      by_cases heq : n=⌊x⌋₊
      · subst n; simp [ne_of_lt hlt]
      · simp [heq]
    · have heq : (n:ℝ)=x := le_antisymm hnx (le_of_not_gt hlt)
      have hf : n=⌊x⌋₊ := by rw [← heq,Nat.floor_natCast]
      subst n
      simp [heq]
  rw [Finset.sum_congr rfl he]
  simp [hn]

lemma lemma121_finite_polynomial_error {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) {x : ℝ} (hx : 1≤x) {s : ℂ} (hs : s.re=1) (hsn : ‖s‖≤2) :
    ‖lemma82FinitePolynomial χ x s-dirichletLFunction χ s‖≤3*(D:ℝ)/x := by
  have hxp : 0<x := zero_lt_one.trans_le hx
  have hh := lemma82_scaled_remainder_norm χ hD hx (by rw [hs]; norm_num)
  unfold lemma82ScaledRemainder at hh
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hxp,hs,Real.rpow_one] at hh
  rw [norm_sub_rev]
  apply (le_div_iff₀ hxp).mpr
  calc
    _ = x*‖dirichletLFunction χ s-lemma82FinitePolynomial χ x s‖ := by ring
    _ ≤ (D:ℝ)*(‖s‖/1+1) := by simpa [hs] using hh
    _ ≤ _ := by nlinarith [Nat.cast_nonneg (α := ℝ) D]

lemma lemma121_strict_polynomial_error {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) {x : ℝ} (hx : 1≤x) {s : ℂ} (hs : s.re=1) (hsn : ‖s‖≤2) :
    ‖lemma121StrictPolynomial χ x s-dirichletLFunction χ s‖≤4*(D:ℝ)/x := by
  have hxp : 0<x := zero_lt_one.trans_le hx
  have hendpoint : ‖lemma121StrictPolynomial χ x s-lemma82FinitePolynomial χ x s‖≤1/x := by
    rw [norm_sub_rev,lemma121_strict_polynomial_endpoint χ hx s]
    split_ifs with heq
    · rw [norm_mul,← Complex.ofReal_natCast,heq,
        Complex.norm_cpow_eq_rpow_re_of_pos hxp,Complex.neg_re,hs,Real.rpow_neg_one]
      simpa [one_div] using mul_le_mul_of_nonneg_right (χ.evalNat_norm_le_one ⌊x⌋₊)
        (inv_nonneg.mpr hxp.le)
    · simp; positivity
  have hh := (norm_sub_le_norm_sub_add_norm_sub (lemma121StrictPolynomial χ x s)
    (lemma82FinitePolynomial χ x s) (dirichletLFunction χ s)).trans
    (add_le_add hendpoint (lemma121_finite_polynomial_error χ hD hx hs hsn))
  apply hh.trans
  rw [← add_div,div_le_div_iff_of_pos_right hxp]
  have hd : (1:ℝ)≤D := by exact_mod_cast hD.le
  linarith

/-- Exact algebraic bridge for the high range d>A. It includes the strict
upper endpoint correction through the strict unweighted polynomial. -/
lemma lemma121_kernel_sum_exact {D : ℕ} (χ : RealPrimitiveCharacter D)
    {A B Q d : ℝ} (hA : 0<A) (hB : 0<B) (hd : A<d) (a b : ℂ) :
    (∑ n ∈ lemma82StrictCutoff (B/d),
      χ.evalNat n*lemma121Kernel A B Q b (d*(n:ℝ))/(n:ℂ)^(1-a)) =
    (((d/A:ℝ):ℂ)^(-b)/(Q:ℂ))*
      ((Real.log (B/A):ℂ)*lemma121StrictPolynomial χ (B/d) (1+b-a)-
        lemma82WeightedPolynomial χ (B/d) (1+b-a)) := by
  have hdp : 0<d := hA.trans hd
  have hxp : 0<B/d := div_pos hB hdp
  rw [← lemma82_strict_weighted_eq χ hxp]
  unfold lemma121StrictPolynomial lemma82StrictCutoff
  rw [Finset.mul_sum,← Finset.sum_sub_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hnp : 0<n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
  have hnR : (0:ℝ)<n := by exact_mod_cast hnp
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hnp
  have hnC : (n:ℂ)≠0 := by exact_mod_cast hnp.ne'
  have hdn : A<d*(n:ℝ) := hd.trans_le (le_mul_of_one_le_right hdp.le hn1)
  have hdnB : d*(n:ℝ)<B := by
    have hh := (lt_div_iff₀ hdp).mp (Finset.mem_filter.mp hn).2
    simpa only [mul_comm] using hh
  have hratio : ((d*(n:ℝ)/A:ℝ):ℂ)^(-b)=
      ((d/A:ℝ):ℂ)^(-b)*(n:ℂ)^(-b) := by
    have hh := lemma82_positive_ratio_cpow (div_pos hA hdp) hnR b
    have hi : ((d*(n:ℝ)/A:ℝ):ℂ)^(-b)=((A/d/(n:ℝ):ℝ):ℂ)^b := by
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (div_pos (mul_pos hdp hnR) hA).ne'),
        Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (div_pos (div_pos hA hdp) hnR).ne'),
        ← Complex.ofReal_log (div_pos (mul_pos hdp hnR) hA).le,
        ← Complex.ofReal_log (div_pos (div_pos hA hdp) hnR).le]
      rw [Real.log_div (mul_pos hdp hnR).ne' hA.ne',Real.log_mul hdp.ne' hnR.ne',
        Real.log_div (div_pos hA hdp).ne' hnR.ne',Real.log_div hA.ne' hdp.ne']
      push_cast
      congr 1
      ring
    rw [hi,hh,lemma82_positive_ratio_cpow hA hdp b,
      lemma82_positive_ratio_cpow hdp hA (-b)]
    simp only [neg_neg,Complex.ofReal_natCast]
    ring
  have hlog : Real.log (d*(n:ℝ)/A)=Real.log (B/A)-Real.log (B/d/(n:ℝ)) := by
    rw [Real.log_div (mul_pos hdp hnR).ne' hA.ne',Real.log_mul hdp.ne' hnR.ne',
      Real.log_div hB.ne' hA.ne',Real.log_div (div_pos hB hdp).ne' hnR.ne',
      Real.log_div hB.ne' hdp.ne']
    ring
  rw [lemma121Kernel,if_pos ⟨hdn,hdnB⟩,hratio,hlog,Complex.ofReal_sub,
    div_eq_mul_inv,← Complex.cpow_neg]
  have hpow : (n:ℂ)^(-b)*(n:ℂ)^(-(1-a))=(n:ℂ)^(-(1+b-a)) := by
    rw [← Complex.cpow_add _ _ hnC]
    congr 1
    ring
  calc
    _ = (((d/A:ℝ):ℂ)^(-b)/(Q:ℂ)) *
      (χ.evalNat n*((n:ℂ)^(-b)*(n:ℂ)^(-(1-a))) *
        ((Real.log (B/A):ℂ)-(Real.log (B/d/(n:ℝ)):ℂ))) := by ring
    _ = _ := by rw [hpow]; ring

end ZhangLS.Spec
