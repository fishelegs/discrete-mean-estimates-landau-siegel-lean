import ZhangLS.Spec.Lemma121ExactHigh

set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace ZhangLS.Spec
open Complex Finset
open scoped Real

lemma lemma121_strict_filter {x y : ℝ} (hx : 0≤x) (hxy : x≤y) :
    (lemma82StrictCutoff y).filter (fun n : ℕ => (n:ℝ)<x)=lemma82StrictCutoff x := by
  ext n
  rw [Finset.mem_filter,lemma82_mem_strictCutoff (hx.trans hxy),lemma82_mem_strictCutoff hx]
  constructor
  · rintro ⟨⟨hn,_⟩,hx⟩; exact ⟨hn,hx⟩
  · rintro ⟨hn,hx⟩; exact ⟨⟨hn,hx.trans_le hxy⟩,hx⟩

lemma lemma121_raw_kernel_term {A Q d : ℝ} (hA : 0<A) (hd : 0<d)
    {n : ℕ} (hn : 0<n) (v a b : ℂ) :
    v*((1/(Q:ℂ))*((d*(n:ℝ)/A:ℝ):ℂ)^(-b)*(Real.log (d*(n:ℝ)/A):ℂ))/(n:ℂ)^(1-a) =
      (((d/A:ℝ):ℂ)^(-b)/(Q:ℂ))*(v*(n:ℂ)^(-(1+b-a)))*(Real.log (d*(n:ℝ)/A):ℂ) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hnC : (n:ℂ)≠0 := by exact_mod_cast hn.ne'
  have he : ((d*(n:ℝ)/A:ℝ):ℂ)^(-b)=((d/A:ℝ):ℂ)^(-b)*(n:ℂ)^(-b) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (div_pos (mul_pos hd hnR) hA).ne'),
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (div_pos hd hA).ne'),
      Complex.cpow_def_of_ne_zero hnC,← Complex.exp_add,
      ← Complex.ofReal_log (div_pos (mul_pos hd hnR) hA).le,
      ← Complex.ofReal_log (div_pos hd hA).le,← Complex.ofReal_natCast,
      ← Complex.ofReal_log hnR.le,
      Real.log_div (mul_pos hd hnR).ne' hA.ne',Real.log_mul hd.ne' hnR.ne',
      Real.log_div hd.ne' hA.ne']
    push_cast
    congr 1
    ring
  rw [he,div_eq_mul_inv,← Complex.cpow_neg]
  have hp : (n:ℂ)^(-b)*(n:ℂ)^(-(1-a))=(n:ℂ)^(-(1+b-a)) := by
    rw [← Complex.cpow_add _ _ hnC]
    congr 1
    ring
  calc
    _ = (((d/A:ℝ):ℂ)^(-b)/(Q:ℂ))*(v*((n:ℂ)^(-b)*(n:ℂ)^(-(1-a))))*
        (Real.log (d*(n:ℝ)/A):ℂ) := by ring
    _ = _ := by rw [hp]

/-- The exact all-range decomposition. The lower weighted polynomial
cancels precisely the forbidden part below the strict lower endpoint. -/
lemma lemma121_kernel_sum_all_ranges {D : ℕ} (χ : RealPrimitiveCharacter D)
    {A B Q d : ℝ} (hA : 0<A) (hB : 0<B) (hAB : A≤B) (hd : 0<d) (a b : ℂ) :
    (∑ n ∈ lemma82StrictCutoff (B/d),
      χ.evalNat n*lemma121Kernel A B Q b (d*(n:ℝ))/(n:ℂ)^(1-a)) =
    (((d/A:ℝ):ℂ)^(-b)/(Q:ℂ))*
      ((Real.log (B/A):ℂ)*lemma121StrictPolynomial χ (B/d) (1+b-a)-
        lemma82WeightedPolynomial χ (B/d) (1+b-a)+
        lemma82WeightedPolynomial χ (A/d) (1+b-a)) := by
  have hxA : 0<A/d := div_pos hA hd
  have hxB : 0<B/d := div_pos hB hd
  have hxy : A/d≤B/d := div_le_div_of_nonneg_right hAB hd.le
  rw [← lemma82_strict_weighted_eq χ hxA,← lemma82_strict_weighted_eq χ hxB]
  change _= _*((Real.log (B/A):ℂ)*lemma121StrictPolynomial χ (B/d) (1+b-a)-
    (∑ n ∈ lemma82StrictCutoff (B/d), χ.evalNat n*(n:ℂ)^(-(1+b-a))*(Real.log (B/d/(n:ℝ)):ℂ))+
    (∑ n ∈ lemma82StrictCutoff (A/d), χ.evalNat n*(n:ℂ)^(-(1+b-a))*(Real.log (A/d/(n:ℝ)):ℂ)))
  rw [← lemma121_strict_filter hxA.le hxy,Finset.sum_filter]
  unfold lemma121StrictPolynomial
  rw [Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hm := (lemma82_mem_strictCutoff hxB.le n).mp hn
  have hnR : (0:ℝ)<n := by exact_mod_cast hm.1
  have hupper : d*(n:ℝ)<B := by
    simpa only [mul_comm] using (lt_div_iff₀ hd).mp hm.2
  have hlog : Real.log (d*(n:ℝ)/A)=Real.log (B/A)-Real.log (B/d/(n:ℝ)) := by
    rw [Real.log_div (mul_pos hd hnR).ne' hA.ne',Real.log_mul hd.ne' hnR.ne',
      Real.log_div hB.ne' hA.ne',Real.log_div hxB.ne' hnR.ne',Real.log_div hB.ne' hd.ne']
    ring
  have hneg : Real.log (A/d/(n:ℝ)) = -Real.log (d*(n:ℝ)/A) := by
    rw [Real.log_div hxA.ne' hnR.ne',Real.log_div hA.ne' hd.ne',
      Real.log_div (mul_pos hd hnR).ne' hA.ne',Real.log_mul hd.ne' hnR.ne']
    ring
  by_cases hlow : A<d*(n:ℝ)
  · have hnot : ¬(n:ℝ)<A/d := by
      intro hh
      have hh' := (lt_div_iff₀ hd).mp hh
      nlinarith only [hlow,hh']
    rw [lemma121Kernel,if_pos ⟨hlow,hupper⟩,lemma121_raw_kernel_term hA hd hm.1,
      if_neg hnot,hlog,Complex.ofReal_sub]
    ring
  · rw [lemma121Kernel,if_neg (fun hh => hlow hh.1)]
    simp only [mul_zero,zero_div]
    by_cases hnlo : (n:ℝ)<A/d
    · rw [if_pos hnlo,hneg,hlog,Complex.ofReal_neg,Complex.ofReal_sub]
      ring
    · rw [if_neg hnlo]
      have heq : d*(n:ℝ)=A := by
        have hh : A≤(n:ℝ)*d := (div_le_iff₀ hd).mp (le_of_not_gt hnlo)
        nlinarith only [le_of_not_gt hlow,hh]
      have hzero : Real.log (d*(n:ℝ)/A)=0 := by rw [heq,div_self hA.ne',Real.log_one]
      have he : (Real.log (B/A):ℂ)=(Real.log (B/d/(n:ℝ)):ℂ) := by
        have hr : Real.log (B/A)=Real.log (B/d/(n:ℝ)) := by linarith only [hlog,hzero]
        rw [hr]
      rw [he]
      ring

end ZhangLS.Spec
