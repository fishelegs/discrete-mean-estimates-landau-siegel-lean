import ZhangLS.Spec.Lemma81RectangleWinding
import ZhangLS.Spec.Lemma32RectanglePowers
import ZhangLS.Spec.Lemma32BoundaryLinearity

/-! Generic contour comparison for two simple principal parts, one double
principal part, and a genuinely analytic remainder. Both contours have
positive (counterclockwise) orientation. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Set Metric MeasureTheory
open scoped Real Topology
set_option maxHeartbeats 2000000

lemma lemma84_rectangle_operator_eq (f : ℂ → ℂ) (a b T : ℝ) :
    lemma81RectangleIntegral f a b (-T) T =
      lemma44GeneralRectangleBoundaryIntegral f a b T := by
  simp only [lemma81RectangleIntegral, lemma44GeneralRectangleBoundaryIntegral,
    ofReal_neg, neg_mul, ← sub_eq_add_neg]

lemma lemma84_rectangle_translate (f : ℂ → ℂ) (w : ℂ) (a b lo hi : ℝ) :
    lemma81RectangleIntegral (fun z => f (z-w)) a b lo hi =
      lemma81RectangleIntegral f (a-w.re) (b-w.re) (lo-w.im) (hi-w.im) := by
  have he (x y : ℝ) : (x : ℂ)+(y : ℂ)*I-w =
      ((x-w.re : ℝ) : ℂ)+((y-w.im : ℝ) : ℂ)*I := by
    apply Complex.ext <;> simp
  have hhorizontal (y : ℝ) :
      (∫ x in a..b, f ((x : ℂ)+(y : ℂ)*I-w)) =
        ∫ x in (a-w.re)..(b-w.re), f ((x : ℂ)+((y-w.im : ℝ) : ℂ)*I) := by
    simp_rw [he]
    exact intervalIntegral.integral_comp_sub_right
      (fun x : ℝ => f ((x : ℂ)+((y-w.im : ℝ) : ℂ)*I)) w.re
  have hvertical (x : ℝ) :
      (∫ y in lo..hi, f ((x : ℂ)+(y : ℂ)*I-w)) =
        ∫ y in (lo-w.im)..(hi-w.im), f (((x-w.re : ℝ) : ℂ)+(y : ℂ)*I) := by
    simp_rw [he]
    exact intervalIntegral.integral_comp_sub_right
      (fun y : ℝ => f (((x-w.re : ℝ) : ℂ)+(y : ℂ)*I)) w.im
  unfold lemma81RectangleIntegral
  rw [hhorizontal lo, hhorizontal hi, hvertical b, hvertical a]

lemma lemma84_rectangle_zpow_zero (n : ℤ) (hn : n ≠ -1)
    (a b lo hi : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hlo : lo ≠ 0) (hhi : hi ≠ 0) :
    lemma81RectangleIntegral (fun z : ℂ => z^n) a b lo hi = 0 := by
  unfold lemma81RectangleIntegral
  rw [lemma32_horizontal_zpow_integral n hn lo a b hlo,
    lemma32_horizontal_zpow_integral n hn hi a b hhi,
    lemma32_vertical_zpow_integral n hn b lo hi hb,
    lemma32_vertical_zpow_integral n hn a lo hi ha]
  ring

/-- A shifted negative power other than the simple pole has zero integral.
The proof uses a genuine primitive after translating all four edges. -/
lemma lemma84_rectangle_shifted_zpow_zero (n : ℤ) (hn : n ≠ -1)
    {a b lo hi : ℝ} {w : ℂ} (hw : w ∈ Ioo a b ×ℂ Ioo lo hi) :
    lemma81RectangleIntegral (fun z : ℂ => (z-w)^n) a b lo hi = 0 := by
  rw [lemma84_rectangle_translate (fun z : ℂ => z^n) w]
  exact lemma84_rectangle_zpow_zero n hn _ _ _ _
    (sub_ne_zero.mpr hw.1.1.ne) (sub_ne_zero.mpr hw.1.2.ne')
    (sub_ne_zero.mpr hw.2.1.ne) (sub_ne_zero.mpr hw.2.2.ne')

lemma lemma84_rectangle_simple_pole {a b T : ℝ} {w : ℂ}
    (hw : w ∈ Ioo a b ×ℂ Ioo (-T) T) :
    lemma44GeneralRectangleBoundaryIntegral (fun z : ℂ => (z-w)⁻¹) a b T =
      2*(Real.pi : ℂ)*I := by
  rw [← lemma84_rectangle_operator_eq]
  exact lemma81_rectangle_simple_pole_winding hw

lemma lemma84_rectangle_double_pole {a b T : ℝ} {w : ℂ}
    (hw : w ∈ Ioo a b ×ℂ Ioo (-T) T) :
    lemma44GeneralRectangleBoundaryIntegral (fun z : ℂ => ((z-w)^2)⁻¹) a b T = 0 := by
  rw [← lemma84_rectangle_operator_eq]
  simpa using lemma84_rectangle_shifted_zpow_zero (-2) (by norm_num) hw

/-- The four closed edges, with no appeal to an abstract contour model. -/
def lemma84RectangleBoundary (a b T : ℝ) : Set ℂ :=
  {z | z ∈ lemma44ClosedRectangle a b T ∧
    (z.re = a ∨ z.re = b ∨ z.im = -T ∨ z.im = T)}

lemma lemma84_boundary_ne_pole {a b T : ℝ} {w z : ℂ}
    (hw : w ∈ Ioo a b ×ℂ Ioo (-T) T)
    (hz : z ∈ lemma84RectangleBoundary a b T) : z ≠ w := by
  intro h
  subst z
  rcases hz.2 with h | h | h | h
  · exact hw.1.1.ne' h
  · exact hw.1.2.ne h
  · exact hw.2.1.ne' h
  · exact hw.2.2.ne h

lemma lemma84_boundary_bottom {a b T : ℝ} (hab : a ≤ b) (hT : 0 ≤ T)
    {x : ℝ} (hx : x ∈ uIcc a b) :
    (x : ℂ)-(T : ℂ)*I ∈ lemma84RectangleBoundary a b T := by
  rw [uIcc_of_le hab] at hx
  constructor
  · change _ ∈ Icc a b ×ℂ Icc (-T) T
    simpa [mem_reProdIm] using And.intro hx (show -T ≤ -T ∧ -T ≤ T by constructor; rfl; linarith)
  · exact Or.inr (Or.inr (Or.inl (by simp)))

lemma lemma84_boundary_top {a b T : ℝ} (hab : a ≤ b) (hT : 0 ≤ T)
    {x : ℝ} (hx : x ∈ uIcc a b) :
    (x : ℂ)+(T : ℂ)*I ∈ lemma84RectangleBoundary a b T := by
  rw [uIcc_of_le hab] at hx
  constructor
  · change _ ∈ Icc a b ×ℂ Icc (-T) T
    simpa [mem_reProdIm] using And.intro hx (show -T ≤ T ∧ T ≤ T by constructor; linarith; rfl)
  · exact Or.inr (Or.inr (Or.inr (by simp)))

lemma lemma84_boundary_right {a b T : ℝ} (hab : a ≤ b) (hT : 0 ≤ T)
    {y : ℝ} (hy : y ∈ uIcc (-T) T) :
    (b : ℂ)+(y : ℂ)*I ∈ lemma84RectangleBoundary a b T := by
  rw [uIcc_of_le (by linarith : -T ≤ T)] at hy
  constructor
  · change _ ∈ Icc a b ×ℂ Icc (-T) T
    simpa [mem_reProdIm] using And.intro (show a ≤ b ∧ b ≤ b from ⟨hab, le_rfl⟩) hy
  · exact Or.inr (Or.inl (by simp))

lemma lemma84_boundary_left {a b T : ℝ} (hab : a ≤ b) (hT : 0 ≤ T)
    {y : ℝ} (hy : y ∈ uIcc (-T) T) :
    (a : ℂ)+(y : ℂ)*I ∈ lemma84RectangleBoundary a b T := by
  rw [uIcc_of_le (by linarith : -T ≤ T)] at hy
  constructor
  · change _ ∈ Icc a b ×ℂ Icc (-T) T
    simpa [mem_reProdIm] using And.intro (show a ≤ a ∧ a ≤ b from ⟨le_rfl, hab⟩) hy
  · exact Or.inl (by simp)

lemma lemma84_boundary_integral_congr {f g : ℂ → ℂ} {a b T : ℝ}
    (hab : a ≤ b) (hT : 0 ≤ T) (he : EqOn f g (lemma84RectangleBoundary a b T)) :
    lemma44GeneralRectangleBoundaryIntegral f a b T =
      lemma44GeneralRectangleBoundaryIntegral g a b T := by
  have hb := intervalIntegral.integral_congr (μ := volume)
    (fun x hx => he (lemma84_boundary_bottom hab hT hx))
  have ht := intervalIntegral.integral_congr (μ := volume)
    (fun x hx => he (lemma84_boundary_top hab hT hx))
  have hr := intervalIntegral.integral_congr (μ := volume)
    (fun y hy => he (lemma84_boundary_right hab hT hy))
  have hl := intervalIntegral.integral_congr (μ := volume)
    (fun y hy => he (lemma84_boundary_left hab hT hy))
  unfold lemma44GeneralRectangleBoundaryIntegral
  rw [hb, ht, hr, hl]

lemma lemma84_boundary_integrable_of_continuousOn {f : ℂ → ℂ} {a b T : ℝ}
    (hab : a ≤ b) (hT : 0 ≤ T) (hf : ContinuousOn f (lemma84RectangleBoundary a b T)) :
    lemma32BoundaryIntegrable f a b T := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (hf.comp (by fun_prop) (fun x hx => lemma84_boundary_bottom hab hT hx)).intervalIntegrable
  · exact (hf.comp (by fun_prop) (fun x hx => lemma84_boundary_top hab hT hx)).intervalIntegrable
  · exact (hf.comp (by fun_prop) (fun y hy => lemma84_boundary_right hab hT hy)).intervalIntegrable
  · exact (hf.comp (by fun_prop) (fun y hy => lemma84_boundary_left hab hT hy)).intervalIntegrable

lemma lemma84_boundary_integrable_add {f g : ℂ → ℂ} {a b T : ℝ}
    (hf : lemma32BoundaryIntegrable f a b T) (hg : lemma32BoundaryIntegrable g a b T) :
    lemma32BoundaryIntegrable (fun z => f z + g z) a b T :=
  ⟨hf.1.add hg.1, hf.2.1.add hg.2.1, hf.2.2.1.add hg.2.2.1, hf.2.2.2.add hg.2.2.2⟩

lemma lemma84_boundary_integrable_const_mul (c : ℂ) {f : ℂ → ℂ} {a b T : ℝ}
    (hf : lemma32BoundaryIntegrable f a b T) :
    lemma32BoundaryIntegrable (fun z => c * f z) a b T :=
  ⟨hf.1.const_mul c, hf.2.1.const_mul c, hf.2.2.1.const_mul c, hf.2.2.2.const_mul c⟩


lemma lemma84_closedBall_subset_rectangle {a b T R : ℝ}
    (ha : R ≤ -a) (hb : R ≤ b) (hT : R ≤ T) :
    closedBall (0 : ℂ) R ⊆ lemma44ClosedRectangle a b T := by
  intro z hz
  have hn : ‖z‖ ≤ R := by simpa [mem_closedBall, dist_eq_norm] using hz
  have hr := abs_le.mp (Complex.abs_re_le_norm z)
  have hi := abs_le.mp (Complex.abs_im_le_norm z)
  change (a ≤ z.re ∧ z.re ≤ b) ∧ (-T ≤ z.im ∧ z.im ≤ T)
  constructor <;> constructor <;> linarith

lemma lemma84_pole_inside_rectangle {a b T R : ℝ} {w : ℂ}
    (ha : R ≤ -a) (hb : R ≤ b) (hT : R ≤ T) (hw : ‖w‖ < R) :
    w ∈ Ioo a b ×ℂ Ioo (-T) T := by
  have hr := abs_le.mp (Complex.abs_re_le_norm w)
  have hi := abs_le.mp (Complex.abs_im_le_norm w)
  constructor <;> constructor <;> linarith

lemma lemma84_sphere_ne_pole {R : ℝ} {w z : ℂ} (hw : ‖w‖ < R)
    (hz : z ∈ sphere (0 : ℂ) R) : z ≠ w := by
  have hn : ‖z‖ = R := by simpa [mem_sphere, dist_eq_norm] using hz
  intro he
  rw [he] at hn
  exact hw.ne hn

lemma lemma84_boundary_simple_continuous {a b T : ℝ} {w : ℂ}
    (hw : w ∈ Ioo a b ×ℂ Ioo (-T) T) :
    ContinuousOn (fun z : ℂ => (z-w)⁻¹) (lemma84RectangleBoundary a b T) :=
  (continuousOn_id.sub continuousOn_const).inv₀
    (fun _z hz => sub_ne_zero.mpr (lemma84_boundary_ne_pole hw hz))

lemma lemma84_circle_simple_continuous {R : ℝ} {w : ℂ} (hw : ‖w‖ < R) :
    ContinuousOn (fun z : ℂ => (z-w)⁻¹) (sphere (0 : ℂ) R) :=
  (continuousOn_id.sub continuousOn_const).inv₀
    (fun _z hz => sub_ne_zero.mpr (lemma84_sphere_ne_pole hw hz))

lemma lemma84_circle_double_pole (w : ℂ) (R : ℝ) :
    circleIntegral (fun z : ℂ => ((z-w)^2)⁻¹) 0 R = 0 := by
  simpa using circleIntegral.integral_sub_zpow_of_ne (n := -2) (by norm_num) 0 w R

/-- Explicit rectangle residue calculation from a genuine boundary decomposition.
Only the analytic remainder is required to extend across the enclosed poles. -/
theorem lemma84_rectangle_principal_parts (F H : ℂ → ℂ) (c₁ c₂ c₃ : ℂ)
    {a b T : ℝ} {w₁ w₂ : ℂ}
    (hw₁ : w₁ ∈ Ioo a b ×ℂ Ioo (-T) T)
    (hw₂ : w₂ ∈ Ioo a b ×ℂ Ioo (-T) T)
    (hH : DifferentiableOn ℂ H (lemma44ClosedRectangle a b T))
    (hboundary : EqOn F
      (fun z => c₁*(z-w₁)⁻¹+c₂*(z-w₂)⁻¹+c₃*((z-w₂)^2)⁻¹+H z)
      (lemma84RectangleBoundary a b T)) :
    lemma44GeneralRectangleBoundaryIntegral F a b T = (2*(Real.pi : ℂ)*I)*(c₁+c₂) := by
  have hab : a ≤ b := hw₁.1.1.le.trans hw₁.1.2.le
  have hT : 0 ≤ T := by have hl := hw₁.2.1; have hu := hw₁.2.2; linarith
  have hs₁ := lemma84_boundary_simple_continuous hw₁
  have hs₂ := lemma84_boundary_simple_continuous hw₂
  have hd₂ : ContinuousOn (fun z : ℂ => ((z-w₂)^2)⁻¹)
      (lemma84RectangleBoundary a b T) := by simpa only [inv_pow] using hs₂.pow 2
  have hHc : ContinuousOn H (lemma84RectangleBoundary a b T) :=
    hH.continuousOn.mono (fun z hz => hz.1)
  have hi₁ := lemma84_boundary_integrable_of_continuousOn hab hT (hs₁.const_mul c₁)
  have hi₂ := lemma84_boundary_integrable_of_continuousOn hab hT (hs₂.const_mul c₂)
  have hi₃ := lemma84_boundary_integrable_of_continuousOn hab hT (hd₂.const_mul c₃)
  have hiH := lemma84_boundary_integrable_of_continuousOn hab hT hHc
  rw [lemma84_boundary_integral_congr hab hT hboundary,
    lemma32_boundary_integral_add _ _ _ _ _
      (lemma84_boundary_integrable_add (lemma84_boundary_integrable_add hi₁ hi₂) hi₃) hiH,
    lemma32_boundary_integral_add _ _ _ _ _ (lemma84_boundary_integrable_add hi₁ hi₂) hi₃,
    lemma32_boundary_integral_add _ _ _ _ _ hi₁ hi₂,
    lemma32_boundary_integral_const_mul, lemma32_boundary_integral_const_mul,
    lemma32_boundary_integral_const_mul,
    lemma84_rectangle_simple_pole hw₁, lemma84_rectangle_simple_pole hw₂,
    lemma84_rectangle_double_pole hw₂,
    lemma44_local_rectangle_cauchy H hab hT hH]
  ring

/-- Explicit positive circle residue calculation for the same principal parts. -/
theorem lemma84_circle_principal_parts (F H : ℂ → ℂ) (c₁ c₂ c₃ : ℂ)
    {R : ℝ} {w₁ w₂ : ℂ} (hw₁ : ‖w₁‖ < R) (hw₂ : ‖w₂‖ < R)
    (hH : DifferentiableOn ℂ H (closedBall (0 : ℂ) R))
    (hcircle : EqOn F
      (fun z => c₁*(z-w₁)⁻¹+c₂*(z-w₂)⁻¹+c₃*((z-w₂)^2)⁻¹+H z)
      (sphere (0 : ℂ) R)) :
    circleIntegral F 0 R = (2*(Real.pi : ℂ)*I)*(c₁+c₂) := by
  have hR : 0 ≤ R := (norm_nonneg w₁).trans hw₁.le
  have hs₁ := lemma84_circle_simple_continuous hw₁
  have hs₂ := lemma84_circle_simple_continuous hw₂
  have hd₂ : ContinuousOn (fun z : ℂ => ((z-w₂)^2)⁻¹) (sphere (0 : ℂ) R) := by
    simpa only [inv_pow] using hs₂.pow 2
  have hHc := hH.continuousOn.mono sphere_subset_closedBall
  have hi₁ := (hs₁.const_mul c₁).circleIntegrable hR
  have hi₂ := (hs₂.const_mul c₂).circleIntegrable hR
  have hi₃ := (hd₂.const_mul c₃).circleIntegrable hR
  have hiH := hHc.circleIntegrable hR
  have hH0 : circleIntegral H 0 R = 0 := by
    apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hR countable_empty
      hH.continuousOn
    intro z hz
    exact hH.differentiableAt (closedBall_mem_nhds_of_mem hz.1)
  have hw₁b : w₁ ∈ ball (0 : ℂ) R := by simpa [mem_ball, dist_eq_norm] using hw₁
  have hw₂b : w₂ ∈ ball (0 : ℂ) R := by simpa [mem_ball, dist_eq_norm] using hw₂
  rw [circleIntegral.integral_congr hR hcircle,
    circleIntegral.integral_add ((hi₁.fun_add hi₂).fun_add hi₃) hiH,
    circleIntegral.integral_add (hi₁.fun_add hi₂) hi₃,
    circleIntegral.integral_add hi₁ hi₂,
    circleIntegral.integral_const_mul, circleIntegral.integral_const_mul,
    circleIntegral.integral_const_mul,
    circleIntegral.integral_sub_inv_of_mem_ball hw₁b,
    circleIntegral.integral_sub_inv_of_mem_ball hw₂b,
    lemma84_circle_double_pole, hH0]
  ring

/-- Generic bridge for the actual Lemma 8.4 integrand. The strict containment,
boundary decomposition and analytic remainder are the only hypotheses; all
winding, integrability and pole avoidance are proved above. -/
theorem lemma84_rectangle_circle_bridge (F H : ℂ → ℂ) (c₁ c₂ c₃ : ℂ)
    {a b T R : ℝ} {w₁ w₂ : ℂ}
    (ha : R < -a) (hb : R < b) (hT : R < T)
    (hw₁ : ‖w₁‖ < R) (hw₂ : ‖w₂‖ < R)
    (hH : DifferentiableOn ℂ H (lemma44ClosedRectangle a b T))
    (hboundary : EqOn F
      (fun z => c₁*(z-w₁)⁻¹+c₂*(z-w₂)⁻¹+c₃*((z-w₂)^2)⁻¹+H z)
      (lemma84RectangleBoundary a b T))
    (hcircle : EqOn F
      (fun z => c₁*(z-w₁)⁻¹+c₂*(z-w₂)⁻¹+c₃*((z-w₂)^2)⁻¹+H z)
      (sphere (0 : ℂ) R)) :
    lemma44GeneralRectangleBoundaryIntegral F a b T = circleIntegral F 0 R := by
  rw [lemma84_rectangle_principal_parts F H c₁ c₂ c₃
      (lemma84_pole_inside_rectangle ha.le hb.le hT.le hw₁)
      (lemma84_pole_inside_rectangle ha.le hb.le hT.le hw₂) hH hboundary,
    lemma84_circle_principal_parts F H c₁ c₂ c₃ hw₁ hw₂
      (hH.mono (lemma84_closedBall_subset_rectangle ha.le hb.le hT.le)) hcircle]


/-- The boundary decomposition also proves actual integrability of F. -/
theorem lemma84_principal_parts_boundary_integrable (F H : ℂ → ℂ) (c₁ c₂ c₃ : ℂ)
    {a b T : ℝ} {w₁ w₂ : ℂ}
    (hw₁ : w₁ ∈ Ioo a b ×ℂ Ioo (-T) T)
    (hw₂ : w₂ ∈ Ioo a b ×ℂ Ioo (-T) T)
    (hH : ContinuousOn H (lemma44ClosedRectangle a b T))
    (hboundary : EqOn F
      (fun z => c₁*(z-w₁)⁻¹+c₂*(z-w₂)⁻¹+c₃*((z-w₂)^2)⁻¹+H z)
      (lemma84RectangleBoundary a b T)) :
    lemma32BoundaryIntegrable F a b T := by
  have hab : a ≤ b := hw₁.1.1.le.trans hw₁.1.2.le
  have hT : 0 ≤ T := by have hl := hw₁.2.1; have hu := hw₁.2.2; linarith
  have hs₁ := lemma84_boundary_simple_continuous hw₁
  have hs₂ := lemma84_boundary_simple_continuous hw₂
  have hd₂ : ContinuousOn (fun z : ℂ => ((z-w₂)^2)⁻¹)
      (lemma84RectangleBoundary a b T) := by simpa only [inv_pow] using hs₂.pow 2
  have hHc : ContinuousOn H (lemma84RectangleBoundary a b T) :=
    hH.mono (fun _z hz => hz.1)
  apply lemma84_boundary_integrable_of_continuousOn hab hT
  exact ((((hs₁.const_mul c₁).add (hs₂.const_mul c₂)).add (hd₂.const_mul c₃)).add hHc).congr hboundary

/-- The circle decomposition proves actual integrability of F on the circle. -/
theorem lemma84_principal_parts_circle_integrable (F H : ℂ → ℂ) (c₁ c₂ c₃ : ℂ)
    {R : ℝ} {w₁ w₂ : ℂ} (hw₁ : ‖w₁‖ < R) (hw₂ : ‖w₂‖ < R)
    (hH : ContinuousOn H (sphere (0 : ℂ) R))
    (hcircle : EqOn F
      (fun z => c₁*(z-w₁)⁻¹+c₂*(z-w₂)⁻¹+c₃*((z-w₂)^2)⁻¹+H z)
      (sphere (0 : ℂ) R)) : CircleIntegrable F 0 R := by
  have hR : 0 ≤ R := (norm_nonneg w₁).trans hw₁.le
  have hs₁ := lemma84_circle_simple_continuous hw₁
  have hs₂ := lemma84_circle_simple_continuous hw₂
  have hd₂ : ContinuousOn (fun z : ℂ => ((z-w₂)^2)⁻¹) (sphere (0 : ℂ) R) := by
    simpa only [inv_pow] using hs₂.pow 2
  apply ContinuousOn.circleIntegrable hR
  exact ((((hs₁.const_mul c₁).add (hs₂.const_mul c₂)).add (hd₂.const_mul c₃)).add hH).congr hcircle

/-- A single pole-removed decomposition on the closed rectangle supplies both
boundary decompositions; strict containment keeps both actual poles off both
contours. This is the convenient bridge for the actual dslope calculation. -/
theorem lemma84_rectangle_circle_bridge_of_decomposition (F H : ℂ → ℂ) (c₁ c₂ c₃ : ℂ)
    {a b T R : ℝ} {w₁ w₂ : ℂ}
    (ha : R < -a) (hb : R < b) (hT : R < T)
    (hw₁ : ‖w₁‖ < R) (hw₂ : ‖w₂‖ < R)
    (hH : DifferentiableOn ℂ H (lemma44ClosedRectangle a b T))
    (he : ∀ z ∈ lemma44ClosedRectangle a b T, z ≠ w₁ → z ≠ w₂ →
      F z = c₁/(z-w₁)+c₂/(z-w₂)+c₃/(z-w₂)^2+H z) :
    lemma44GeneralRectangleBoundaryIntegral F a b T = circleIntegral F 0 R := by
  have hi₁ := lemma84_pole_inside_rectangle ha.le hb.le hT.le hw₁
  have hi₂ := lemma84_pole_inside_rectangle ha.le hb.le hT.le hw₂
  apply lemma84_rectangle_circle_bridge F H c₁ c₂ c₃ ha hb hT hw₁ hw₂ hH
  · intro z hz
    simpa only [div_eq_mul_inv] using he z hz.1
      (lemma84_boundary_ne_pole hi₁ hz) (lemma84_boundary_ne_pole hi₂ hz)
  · intro z hz
    simpa only [div_eq_mul_inv] using
      he z (lemma84_closedBall_subset_rectangle ha.le hb.le hT.le (sphere_subset_closedBall hz))
        (lemma84_sphere_ne_pole hw₁ hz) (lemma84_sphere_ne_pole hw₂ hz)

/-- Normalization agrees exactly, with the positive +2πi orientation. -/
theorem lemma84_normalized_rectangle_circle_bridge (F H : ℂ → ℂ) (c₁ c₂ c₃ : ℂ)
    {a b T R : ℝ} {w₁ w₂ : ℂ}
    (ha : R < -a) (hb : R < b) (hT : R < T)
    (hw₁ : ‖w₁‖ < R) (hw₂ : ‖w₂‖ < R)
    (hH : DifferentiableOn ℂ H (lemma44ClosedRectangle a b T))
    (he : ∀ z ∈ lemma44ClosedRectangle a b T, z ≠ w₁ → z ≠ w₂ →
      F z = c₁/(z-w₁)+c₂/(z-w₂)+c₃/(z-w₂)^2+H z) :
    (2*(Real.pi : ℂ)*I)⁻¹ * lemma44GeneralRectangleBoundaryIntegral F a b T =
      (2*(Real.pi : ℂ)*I)⁻¹ * circleIntegral F 0 R := by
  rw [lemma84_rectangle_circle_bridge_of_decomposition F H c₁ c₂ c₃ ha hb hT hw₁ hw₂ hH he]

/-- Reversing the horizontal orientation reverses the whole rectangle integral. -/
lemma lemma84_rectangle_reverse_horizontal (f : ℂ → ℂ) (a b lo hi : ℝ) :
    lemma81RectangleIntegral f b a lo hi = -lemma81RectangleIntegral f a b lo hi := by
  unfold lemma81RectangleIntegral
  rw [intervalIntegral.integral_symm (a := b) (b := a),
    intervalIntegral.integral_symm (a := b) (b := a)]
  ring

end ZhangLS.Spec
