import ZhangLS.Spec.Lemma54EighthMellin

/-! # Eighth-order Mellin frequency tails

The original finite-height cancellation input is never applied outside its
range. Pointwise eighth-order decay gives a genuine H⁻⁷ tail, retaining
both the global amplitude and the central-window amplitude.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Topology

lemma lemma54_eighth_arctan_le_self {x : ℝ} (hx : 0≤x) : Real.arctan x≤x := by
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun y (_ : y∈uIcc (0:ℝ) x) => (Real.hasDerivAt_arctan' y).hasDerivWithinAt)
    (fun y (_ : y∈uIcc (0:ℝ) x) => (show ‖(1+y^2)⁻¹‖≤(1:ℝ) by
      rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg y])))
    (convex_uIcc (0:ℝ) x) left_mem_uIcc right_mem_uIcc
  simpa only [Real.arctan_zero,sub_zero,Real.norm_eq_abs,
    abs_of_nonneg (Real.arctan_nonneg.mpr hx),abs_of_nonneg hx,one_mul] using hb

lemma lemma54_eighth_positive_cauchy_tail {H : ℝ} (hH : 0<H) :
    (∫ t : ℝ in Ioi H, (1+t^2)⁻¹)≤H⁻¹ := by
  rw [integral_Ioi_inv_one_add_sq,←Real.arctan_inv_of_pos hH]
  exact lemma54_eighth_arctan_le_self (inv_nonneg.mpr hH.le)

lemma lemma54_eighth_negative_cauchy_tail {H : ℝ} (hH : 0<H) :
    (∫ t : ℝ in Iic (-H), (1+t^2)⁻¹)≤H⁻¹ := by
  rw [integral_Iic_inv_one_add_sq,Real.arctan_neg]
  have hh := lemma54_eighth_positive_cauchy_tail hH
  rw [integral_Ioi_inv_one_add_sq] at hh
  linarith

lemma lemma54_eighth_weight_le_cauchy (t : ℝ) :
    (1+t^2)^(-(4:ℤ)) ≤ (1+t^2)⁻¹ := by
  have hb : 1≤1+t^2 := by nlinarith [sq_nonneg t]
  have hh : (1+t^2)≤(1+t^2)^4 := by
    simpa using pow_le_pow_right₀ hb (show (1:ℕ)≤4 by norm_num)
  simpa only [zpow_neg,zpow_ofNat] using
    inv_anti₀ (by positivity : (0:ℝ)<1+t^2) hh

lemma lemma54_eighth_weight_tail_point {H t : ℝ} (hH : 0<H) (ht : H≤|t|) :
    (1+t^2)^(-(4:ℤ)) ≤ (H^6)⁻¹*(1+t^2)⁻¹ := by
  have hb : 0<1+t^2 := by positivity
  have hs : H^2≤1+t^2 := by nlinarith [sq_abs t]
  have hc := pow_le_pow_left₀ (sq_nonneg H) hs 3
  have hd : H^6*(1+t^2)≤(1+t^2)^4 := by
    have hh := mul_le_mul_of_nonneg_right hc hb.le
    simpa only [← pow_mul,show (2:ℕ)*3=6 by norm_num,← pow_succ] using hh
  have hi := inv_anti₀ (mul_pos (pow_pos hH 6) hb) hd
  simpa only [zpow_neg,zpow_ofNat,mul_inv_rev,mul_comm] using hi

lemma lemma54_eighth_bounded_weight_integrable (f : ℝ → ℂ) (hf : Continuous f)
    {B : ℝ} (hB : 0≤B) (hbound : ∀t, ‖f t‖≤B) :
    Integrable (fun t : ℝ => ‖f t‖*(1+t^2)^(-(4:ℤ))) := by
  have hwcont : Continuous (fun t : ℝ => (1+t^2)^(-(4:ℤ))) := by
    apply Continuous.zpow₀ (by fun_prop)
    intro t
    left
    positivity
  apply (integrable_inv_one_add_sq.const_mul B).mono'
    ((hf.norm).mul hwcont).aestronglyMeasurable
  apply ae_of_all
  intro t
  have hw : 0≤(1+t^2)^(-(4:ℤ)) := by positivity
  change ‖‖f t‖*(1+t^2)^(-(4:ℤ))‖ ≤ B*(1+t^2)⁻¹
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (norm_nonneg _) hw)]
  exact mul_le_mul (hbound t) (lemma54_eighth_weight_le_cauchy t) hw hB

/-- The central and outer heights are bounded separately; the tail keeps
its genuine H⁻⁷ saving before every outer arithmetic sum. -/
theorem lemma54_eighth_window_and_tail (f : ℝ → ℂ) (hf : Continuous f)
    {B C H : ℝ} (hB : 0≤B) (hC : 0≤C) (hH : 0<H)
    (hglobal : ∀t, ‖f t‖≤B) (hwindow : ∀t, |t|≤H → ‖f t‖≤C) :
    (∫ t : ℝ, ‖f t‖*(1+t^2)^(-(4:ℤ))) ≤ C*Real.pi+2*B/H^7 := by
  let w : ℝ → ℝ := fun t => (1+t^2)⁻¹
  let A := B*(H^6)⁻¹
  let v : ℝ → ℝ := fun t => C*w t+A*((Iic (-H)).indicator w t+(Ioi H).indicator w t)
  have hw : Integrable w := integrable_inv_one_add_sq
  have hwl := hw.indicator (s := Iic (-H)) measurableSet_Iic
  have hwr := hw.indicator (s := Ioi H) measurableSet_Ioi
  have hv : Integrable v := (hw.const_mul C).add ((hwl.add hwr).const_mul A)
  have hu := lemma54_eighth_bounded_weight_integrable f hf hB hglobal
  have hA : 0≤A := by dsimp [A]; positivity
  have hpoint (t : ℝ) : ‖f t‖*(1+t^2)^(-(4:ℤ)) ≤ v t := by
    have hw0 : 0≤w t := by dsimp [w]; positivity
    have hext (ht : H≤|t|) : ‖f t‖*(1+t^2)^(-(4:ℤ))≤A*w t := by
      have hh := mul_le_mul (hglobal t) (lemma54_eighth_weight_tail_point hH ht)
        (by positivity : 0≤(1+t^2)^(-(4:ℤ))) hB
      simpa only [A,w,mul_assoc] using hh
    by_cases hl : t≤-H
    · have hr : ¬H<t := by linarith
      have he := hext (by rw [abs_of_nonpos (by linarith : t≤0)]; linarith)
      dsimp [v]
      simp only [indicator_apply,mem_Iic,mem_Ioi,if_pos hl,if_neg hr,add_zero]
      nlinarith [mul_nonneg hC hw0]
    · by_cases hr : H<t
      · have he := hext (by rw [abs_of_pos (hH.trans hr)]; exact hr.le)
        dsimp [v]
        simp only [indicator_apply,mem_Iic,mem_Ioi,if_neg hl,if_pos hr,zero_add]
        nlinarith [mul_nonneg hC hw0]
      · have ht : |t|≤H := abs_le.mpr ⟨by linarith,by linarith⟩
        have he := mul_le_mul (hwindow t ht) (lemma54_eighth_weight_le_cauchy t)
          (by positivity : 0≤(1+t^2)^(-(4:ℤ))) hC
        dsimp [v]
        simp only [indicator_apply,mem_Iic,mem_Ioi,if_neg hl,if_neg hr,add_zero,mul_zero]
        exact he
  have hi := integral_mono_ae hu hv (ae_of_all _ hpoint)
  have hiv : (∫t : ℝ, v t)=C*Real.pi+A*((∫t : ℝ in Iic (-H), w t)+(∫t : ℝ in Ioi H, w t)) := by
    have hadd := integral_add (hw.const_mul C) ((hwl.add hwr).const_mul A)
    simp only [Pi.add_apply] at hadd
    dsimp only [v]
    rw [hadd,integral_const_mul,integral_const_mul]
    have hadd' := integral_add hwl hwr
    simp only [Pi.add_apply] at hadd'
    rw [hadd',integral_indicator measurableSet_Iic,integral_indicator measurableSet_Ioi]
    rw [show (∫t : ℝ, w t)=Real.pi from integral_univ_inv_one_add_sq]
  rw [hiv] at hi
  have ht := mul_le_mul_of_nonneg_left (add_le_add
    (lemma54_eighth_negative_cauchy_tail hH) (lemma54_eighth_positive_cauchy_tail hH)) hA
  have he : A*(H⁻¹+H⁻¹)=2*B/H^7 := by
    dsimp [A]
    field_simp
    ring
  rw [he] at ht
  exact hi.trans (by dsimp [w] at *; linarith)

end ZhangLS.Spec
