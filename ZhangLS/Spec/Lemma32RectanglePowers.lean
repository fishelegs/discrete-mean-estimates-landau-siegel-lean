import ZhangLS.Spec.Lemma32LaurentCoefficients
import Mathlib.Analysis.Calculus.Deriv.ZPow
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Metric Set Filter
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def lemma32LaurentPrimitive (n : ℤ) (z : ℂ) : ℂ :=
  z^(n+1)/((n+1 : ℤ) : ℂ)

lemma lemma32_laurent_primitive_hasDerivAt (n : ℤ) (hn : n ≠ -1)
    (z : ℂ) (hz : z ≠ 0) : HasDerivAt (lemma32LaurentPrimitive n) (z^n) z := by
  have hden : ((n+1 : ℤ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : n+1 ≠ 0)
  unfold lemma32LaurentPrimitive
  convert (hasDerivAt_zpow (n+1) z (Or.inl hz)).div_const ((n+1 : ℤ) : ℂ) using 1
  simp only [add_sub_cancel_right]
  field_simp [hden]

lemma lemma32_horizontal_zpow_integral (n : ℤ) (hn : n ≠ -1)
    (c a b : ℝ) (hc : c ≠ 0) :
    (∫ x : ℝ in a..b, ((x : ℂ)+(c : ℂ)*I)^n) =
      lemma32LaurentPrimitive n ((b : ℂ)+(c : ℂ)*I)-
        lemma32LaurentPrimitive n ((a : ℂ)+(c : ℂ)*I) := by
  have hne (x : ℝ) : (x : ℂ)+(c : ℂ)*I ≠ 0 := by
    intro h;have hi := congrArg Complex.im h;norm_num at hi;exact hc hi
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    have hg : HasDerivAt (fun z : ℂ => z+(c : ℂ)*I) 1 (x : ℂ) :=
      (hasDerivAt_id (x : ℂ)).add_const _
    simpa only [mul_one,Function.comp_apply] using
      ((lemma32_laurent_primitive_hasDerivAt n hn _ (hne x)).comp (x : ℂ) hg).comp_ofReal
  · exact ((show Continuous (fun x : ℝ => (x : ℂ)+(c : ℂ)*I) by fun_prop).zpow₀
      n (fun x => Or.inl (hne x))).intervalIntegrable a b

lemma lemma32_vertical_zpow_integral (n : ℤ) (hn : n ≠ -1)
    (c a b : ℝ) (hc : c ≠ 0) :
    I*(∫ y : ℝ in a..b, ((c : ℂ)+(y : ℂ)*I)^n) =
      lemma32LaurentPrimitive n ((c : ℂ)+(b : ℂ)*I)-
        lemma32LaurentPrimitive n ((c : ℂ)+(a : ℂ)*I) := by
  have hne (y : ℝ) : (c : ℂ)+(y : ℂ)*I ≠ 0 := by
    intro h;have hr := congrArg Complex.re h;norm_num at hr;exact hc hr
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro y hy
    have hg : HasDerivAt (fun z : ℂ => (c : ℂ)+z*I) I (y : ℂ) := by
      simpa using ((hasDerivAt_id (y : ℂ)).mul_const I).const_add (c : ℂ)
    simpa only [mul_comm,Function.comp_apply] using
      ((lemma32_laurent_primitive_hasDerivAt n hn _ (hne y)).comp (y : ℂ) hg).comp_ofReal
  · exact (((show Continuous (fun y : ℝ => (c : ℂ)+(y : ℂ)*I) by fun_prop).zpow₀
      n (fun y => Or.inl (hne y))).const_mul I).intervalIntegrable a b

lemma lemma32_rectangle_zpow_zero (n : ℤ) (hn : n ≠ -1)
    (a b T : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hT : 0 < T) :
    lemma44GeneralRectangleBoundaryIntegral (fun w : ℂ => w^n) a b T = 0 := by
  have hbottom := lemma32_horizontal_zpow_integral n hn (-T) a b (neg_ne_zero.mpr hT.ne')
  have htop := lemma32_horizontal_zpow_integral n hn T a b hT.ne'
  have hright := lemma32_vertical_zpow_integral n hn b (-T) T hb
  have hleft := lemma32_vertical_zpow_integral n hn a (-T) T ha
  simp only [ofReal_neg,neg_mul,← sub_eq_add_neg] at hbottom hright hleft
  unfold lemma44GeneralRectangleBoundaryIntegral
  rw [hbottom,htop,hright,hleft]
  ring

end ZhangLS.Spec
