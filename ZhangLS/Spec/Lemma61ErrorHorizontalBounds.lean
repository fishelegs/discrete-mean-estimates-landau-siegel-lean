import ZhangLS.Spec.Lemma61ErrorLineShift

/-! # Actual original-left Z error for Lemma 6.1

The actual Z difference has a removable regular part at zero. Its
vertical integrability, exact shift to the reflected short-polynomial
line and horizontal budgets prove the original-left error <= C E1.
The full Lemma61Target remains unproved: finite polynomial Gaussian
relation, full horizontal L edges and final constants/thresholds remain.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Real Topology
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

lemma lemma61_short_polynomial_norm_bound {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hL : 3 ≤ lemma23PaperL D) {z : ℂ} (hz : 0 ≤ z.re) :
    ‖lemma61ShortPolynomial D ψ z‖ ≤ 2 * lemma56PaperT D ^ 3 := by
  classical
  let S := (Finset.Icc 1 ⌈lemma56PaperT D ^ 3⌉₊).filter (fun (n : ℕ) => (n : ℝ) < lemma56PaperT D ^ 3)
  have h0 : 0 < lemma23PaperL D := by linarith
  have hT : 1 ≤ lemma56PaperT D := by
    unfold lemma56PaperT
    exact Real.one_le_exp_iff.mpr (Real.rpow_nonneg h0.le _)
  have ht3 : 1 ≤ lemma56PaperT D ^ 3 := one_le_pow₀ hT
  have hp (n : ℕ) (hn : n ∈ S) : ‖ψ (n : ZMod p) * exp (-z * (Real.log (n : ℝ) : ℂ))‖ ≤ 1 := by
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
    have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
    rw [norm_mul,norm_exp]
    simp only [mul_re,neg_re,ofReal_re,ofReal_im,mul_zero,sub_zero]
    have he : Real.exp (-z.re * Real.log (n : ℝ)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith only [hz,hlog])
    exact (mul_le_mul_of_nonneg_left he (norm_nonneg _)).trans (by simpa only [mul_one] using ψ.norm_le_one (n : ZMod p))
  have hc : S.card ≤ ⌈lemma56PaperT D ^ 3⌉₊ := by
    have h := Finset.card_filter_le (s := Finset.Icc 1 ⌈lemma56PaperT D ^ 3⌉₊)
      (p := fun (n : ℕ) => (n : ℝ) < lemma56PaperT D ^ 3)
    simpa only [Nat.card_Icc,Nat.add_sub_cancel] using h
  have hceil := (Nat.ceil_lt_add_one (show 0 ≤ lemma56PaperT D ^ 3 by positivity)).le
  unfold lemma61ShortPolynomial
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ S, (1 : ℝ) := Finset.sum_le_sum hp
    _ = (S.card : ℝ) := by simp
    _ ≤ (⌈lemma56PaperT D ^ 3⌉₊ : ℝ) := by exact_mod_cast hc
    _ ≤ _ := by linarith only [hceil,ht3]

lemma lemma61_model_Z_P4_factor {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (s w : ℂ) (hL : 3 ≤ lemma23PaperL D) :
    lemma23DirichletZ ψ s * ((lemma23PaperP D * lemma51PaperT0 D : ℝ) : ℂ) ^ (-w) *
      exp (w * (Real.log (lemma61PaperP4 D) : ℂ)) =
        lemma23DirichletZ ψ s * exp (-2 * (Real.log (lemma56PaperT D) : ℂ) * w) := by
  have h0 : 0 < lemma23PaperL D := by linarith
  have hbase : 0 < lemma23PaperP D * lemma51PaperT0 D := mul_pos (Real.exp_pos _) (pow_pos h0 519)
  have he : -(Real.log (lemma23PaperP D * lemma51PaperT0 D) : ℂ) * w +
      w * (Real.log (lemma61PaperP4 D) : ℂ) = -2 * (Real.log (lemma56PaperT D) : ℂ) * w := by
    rw [lemma61_P4_PT0_log_identity hL]
    push_cast
    ring
  rw [lemma61_positive_real_cpow_model hbase,mul_assoc,← Complex.exp_add,he]

lemma lemma61_actual_Z_original_norm_bound {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hL : 3 ≤ lemma23PaperL D) (hs : Lemma61InRegion D s) :
    ‖lemma23DirichletZ ψ s‖ ≤ Real.exp (1 + 4 * Real.pi) := by
  have h0 : 0 < lemma23PaperL D := by linarith
  have h := lemma61_actual_Z_P4_cancellation ψ hψ hL hs (w := 0)
    (by simp only [zero_re]; constructor <;> nlinarith only [pow_nonneg h0.le 9])
    (by simpa only [zero_im,abs_zero] using (pow_nonneg h0.le 20))
  simpa using h

lemma lemma61_actual_horizontal_Z_error_factor_bound {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : Lemma23InPsi (D := D) ψ)
    {s w : ℂ} (hL : 3 ≤ lemma23PaperL D) (hs : Lemma61InRegion D s)
    (hwre : -1 ≤ w.re ∧ w.re ≤ 1 - 2 * s.re)
    (hwim : |w.im| = lemma23PaperL D ^ 20) :
    ‖((lemma23DirichletZ ψ (s + w) - lemma23DirichletZ ψ s *
      ((lemma23PaperP D * lemma51PaperT0 D : ℝ) : ℂ) ^ (-w)) / w) *
        exp (w * (Real.log (lemma61PaperP4 D) : ℂ))‖ ≤
      2 * Real.exp (1 + 4 * Real.pi) * Real.exp (2 * Real.log (lemma56PaperT D)) := by
  have h0 : 0 < lemma23PaperL D := by linarith
  have hr := lemma61_region_real_parts hL hs
  have h9 : 1 ≤ lemma23PaperL D ^ 9 := one_le_pow₀ (by linarith : 1 ≤ lemma23PaperL D)
  have h20 : 1 ≤ lemma23PaperL D ^ 20 := one_le_pow₀ (by linarith : 1 ≤ lemma23PaperL D)
  have hw : -(lemma23PaperL D ^ 9) ≤ w.re ∧ w.re ≤ 2 := ⟨by linarith only [hwre.1,h9],by linarith only [hwre.2,hr.1]⟩
  have hz := lemma61_actual_Z_P4_cancellation ψ hψ hL hs hw hwim.le
  have hT0 : 0 ≤ Real.log (lemma56PaperT D) := by linarith [(lemma61_T_log_bounds hL).1]
  have he : -2 * w.re * Real.log (lemma56PaperT D) ≤ 2 * Real.log (lemma56PaperT D) :=
    by nlinarith only [hwre.1,hT0]
  have hz' := hz.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (Real.exp_nonneg _))
  have hm : ‖lemma23DirichletZ ψ s * ((lemma23PaperP D * lemma51PaperT0 D : ℝ) : ℂ) ^ (-w) *
      exp (w * (Real.log (lemma61PaperP4 D) : ℂ))‖ ≤
      Real.exp (1 + 4 * Real.pi) * Real.exp (2 * Real.log (lemma56PaperT D)) := by
    rw [lemma61_model_Z_P4_factor ψ s w hL,norm_mul,norm_exp]
    have heq : (-2 * (Real.log (lemma56PaperT D) : ℂ) * w).re = -2 * w.re * Real.log (lemma56PaperT D) := by simp [mul_re]; ring
    rw [heq]
    exact mul_le_mul (lemma61_actual_Z_original_norm_bound ψ hψ hL hs) (Real.exp_le_exp.mpr he) (Real.exp_nonneg _) (Real.exp_nonneg _)
  have hn : ‖w‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by
    have hi := Complex.abs_im_le_norm w
    rw [hwim] at hi
    linarith only [hi,h20])
  have hcalc : ((lemma23DirichletZ ψ (s + w) - lemma23DirichletZ ψ s *
      ((lemma23PaperP D * lemma51PaperT0 D : ℝ) : ℂ) ^ (-w)) / w) * exp (w * (Real.log (lemma61PaperP4 D) : ℂ)) =
      (lemma23DirichletZ ψ (s + w) * exp (w * (Real.log (lemma61PaperP4 D) : ℂ)) -
        lemma23DirichletZ ψ s * ((lemma23PaperP D * lemma51PaperT0 D : ℝ) : ℂ) ^ (-w) *
          exp (w * (Real.log (lemma61PaperP4 D) : ℂ))) / w := by rw [div_eq_mul_inv,div_eq_mul_inv]; ring
  rw [hcalc,norm_div,div_eq_mul_inv]
  have hb := norm_sub_le (lemma23DirichletZ ψ (s + w) * exp (w * (Real.log (lemma61PaperP4 D) : ℂ)))
    (lemma23DirichletZ ψ s * ((lemma23PaperP D * lemma51PaperT0 D : ℝ) : ℂ) ^ (-w) * exp (w * (Real.log (lemma61PaperP4 D) : ℂ)))
  apply (mul_le_mul_of_nonneg_left hn (norm_nonneg _)).trans
  simp only [mul_one]
  nlinarith only [hb,hz',hm]

lemma lemma61_actual_horizontal_Z_error_point_bound {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : Lemma23InPsi (D := D) ψ)
    {s w : ℂ} (hL : 3 ≤ lemma23PaperL D) (hs : Lemma61InRegion D s)
    (hwre : -1 ≤ w.re ∧ w.re ≤ 1 - 2 * s.re)
    (hwim : |w.im| = lemma23PaperL D ^ 20) :
    ‖lemma61ActualZErrorIntegrand (D := D) ψ s w‖ ≤
      (4 * Real.exp (2 + 4 * Real.pi)) * Real.exp (5 * lemma23PaperL D ^ 9 - lemma23PaperL D ^ 10 / 4) := by
  have h0 : 0 < lemma23PaperL D := by linarith
  have hr := lemma61_region_real_parts hL hs
  have h9 : 1 ≤ lemma23PaperL D ^ 9 := one_le_pow₀ (by linarith : 1 ≤ lemma23PaperL D)
  have hw : -(lemma23PaperL D ^ 9) ≤ w.re ∧ w.re ≤ 2 := ⟨by linarith only [hwre.1,h9],by linarith only [hwre.2,hr.1]⟩
  have hz := lemma61_actual_horizontal_Z_error_factor_bound ψ hψ hL hs hwre hwim
  have hp := lemma61_short_polynomial_norm_bound ψ⁻¹ hL (z := 1 - s - w)
    (by simp only [sub_re,one_re]; linarith only [hwre.2,hr.1])
  have ho := lemma61_large_shift_gaussian_bound hL hw
  have hgauss : w.im ^ 2 / (4 * lemma23PaperL D ^ 30) = lemma23PaperL D ^ 10 / 4 := by
    rw [← sq_abs w.im,hwim]
    field_simp
  rw [neg_div,hgauss] at ho
  have hT := lemma61_T_log_bounds hL
  have ht3 : lemma56PaperT D ^ 3 = Real.exp (3 * Real.log (lemma56PaperT D)) := by
    simpa only [Real.log_pow,Nat.cast_ofNat] using (Real.exp_log (pow_pos (Real.exp_pos _) 3)).symm
  unfold lemma61ActualZErrorIntegrand
  calc
    _ = ‖((lemma23DirichletZ ψ (s + w) - lemma23DirichletZ ψ s *
        ((lemma23PaperP D * lemma51PaperT0 D : ℝ) : ℂ) ^ (-w)) / w) * exp (w * (Real.log (lemma61PaperP4 D) : ℂ))‖ *
        ‖lemma61ShortPolynomial D ψ⁻¹ (1 - s - w)‖ * ‖lemma57OmegaOne D w‖ := by
      simp only [norm_mul,norm_div]
      ring
    _ ≤ (2 * Real.exp (1 + 4 * Real.pi) * Real.exp (2 * Real.log (lemma56PaperT D))) *
        (2 * lemma56PaperT D ^ 3) * (Real.exp 1 * Real.exp (-(lemma23PaperL D ^ 10 / 4))) := by
      gcongr <;> (rw [ht3]; positivity)
    _ = (4 * Real.exp (2 + 4 * Real.pi)) * Real.exp (5 * Real.log (lemma56PaperT D) - lemma23PaperL D ^ 10 / 4) := by
      rw [ht3,show 2 + 4 * Real.pi = (1 + 4 * Real.pi) + 1 by ring,
        show 5 * Real.log (lemma56PaperT D) - lemma23PaperL D ^ 10 / 4 =
          (2 * Real.log (lemma56PaperT D)) + (3 * Real.log (lemma56PaperT D)) + -(lemma23PaperL D ^ 10 / 4) by ring]
      simp only [Real.exp_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hT.2])) (by positivity)

lemma lemma61_actual_horizontal_Z_error_integral_bound {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hL : 64 ≤ lemma23PaperL D) (hs : Lemma61InRegion D s)
    {t : ℝ} (ht : |t| = lemma23PaperL D ^ 20) :
    ‖(2 * (Real.pi : ℂ) * I)⁻¹ * (∫ x : ℝ in (-1 : ℝ)..(1 - 2 * s.re),
      lemma61ActualZErrorIntegrand (D := D) ψ s ((x : ℂ) + (t : ℂ) * I))‖ ≤
      (8 * Real.exp (2 + 4 * Real.pi)) * Real.exp (-(lemma23PaperL D ^ 10) / 8) := by
  have h0 : 0 < lemma23PaperL D := by linarith
  have hr := lemma61_region_real_parts (by linarith) hs
  have hab : (-1 : ℝ) ≤ 1 - 2 * s.re := by linarith only [hr.2]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (-1 : ℝ)) (b := 1 - 2 * s.re)
    (f := fun x : ℝ => lemma61ActualZErrorIntegrand (D := D) ψ s ((x : ℂ) + (t : ℂ) * I))
    (C := (4 * Real.exp (2 + 4 * Real.pi)) * Real.exp (5 * lemma23PaperL D ^ 9 - lemma23PaperL D ^ 10 / 4))
    (by intro x hx; rw [uIoc_of_le hab] at hx
        apply lemma61_actual_horizontal_Z_error_point_bound ψ hψ (by linarith) hs
        · simpa using And.intro hx.1.le hx.2
        · simpa using ht)
  have hn := (mul_le_mul_of_nonneg_right lemma61_mellin_normalization_norm_le_one
    (norm_nonneg (∫ x : ℝ in (-1 : ℝ)..(1 - 2 * s.re),
      lemma61ActualZErrorIntegrand (D := D) ψ s ((x : ℂ) + (t : ℂ) * I)))).trans (by simpa only [one_mul] using hb)
  rw [← norm_mul] at hn
  apply hn.trans
  have he : 5 * lemma23PaperL D ^ 9 - lemma23PaperL D ^ 10 / 4 ≤ -(lemma23PaperL D ^ 10) / 8 := by
    nlinarith only [mul_le_mul_of_nonneg_right hL (pow_nonneg h0.le 9),pow_nonneg h0.le 9]
  calc
    _ ≤ ((4 * Real.exp (2 + 4 * Real.pi)) * Real.exp (5 * lemma23PaperL D ^ 9 - lemma23PaperL D ^ 10 / 4)) * 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [abs_of_nonneg (by linarith only [hr.2])]
      linarith only [hr.1]
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by positivity : 0 ≤ 8 * Real.exp (2 + 4 * Real.pi))
      nlinarith only [h]

end ZhangLS.Spec
