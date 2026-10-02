import ZhangLS.Spec.Lemma84NearOnePrimeProduct
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
set_option maxHeartbeats 1000000

noncomputable def lemma84UGrowthConstant : ℝ :=
  lemma83RegularProductBound+lemma83ExceptionalConstant+2

lemma lemma84_u_growth_constant_pos : 0 < lemma84UGrowthConstant := by
  unfold lemma84UGrowthConstant
  positivity [lemma83_regular_product_bound_pos,lemma83_exceptional_constant_pos]

/-- The actual U on the original left segment and horizontal connectors is
bounded by a fixed polynomial in log log D. No D-power estimate is used. -/
lemma lemma84_actual_u_contour_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (d r K : ℕ) (hd : 0 < d) (hr : 0 < r)
    (hL : 100 ≤ lemma23PaperL D) (hlog : 20*Real.log (lemma23PaperL D) ≤ lemma23PaperL D)
    (hcut : (d*r : ℝ) < lemma23PaperP D*lemma56PaperT D^(-2 : ℤ))
    (hK : 9*lemma84UGrowthConstant ≤ (K:ℝ)) (s : ℂ)
    (hs : 1-1/lemma23PaperL D ≤ s.re) :
    ‖lemma83EulerCorrection χ (lemma83PaperBeta D c) j d r s‖ ≤
      lemma84UGrowthConstant*Real.exp (lemma84UGrowthConstant/Real.log 2)*
        (1+20*Real.log (lemma23PaperL D))^K := by
  have hLp : 0 < lemma23PaperL D := by linarith
  have hsre : 9/10 < s.re := by
    have hi : 1/lemma23PaperL D ≤ (1:ℝ)/100 := one_div_le_one_div_of_le (by norm_num) hL
    linarith only [hi,hs]
  have hh := lemma83_uniform_growth χ (lemma83PaperBeta D c) (lemma83_beta_re D c) j d r
    lemma84UGrowthConstant
    (by unfold lemma84UGrowthConstant; linarith only [lemma83_exceptional_constant_pos])
    (by unfold lemma84UGrowthConstant; linarith only [lemma83_regular_product_bound_pos]) s hsre
  have hp := lemma84_paper_near_one_prime_product (d*r) (Nat.mul_pos hd hr) (lemma23PaperL D)
    s.re lemma84UGrowthConstant K (by linarith only [hL]) hlog hs
    lemma84_u_growth_constant_pos.le hK (lemma83_paper_cutoff_log hL hd hr hcut)
  apply hh.le.trans
  exact (mul_le_mul_of_nonneg_left hp lemma84_u_growth_constant_pos.le).trans_eq (by ring)

end ZhangLS.Spec
