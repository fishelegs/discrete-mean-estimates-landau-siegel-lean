import ZhangLS.Spec.Lemma84Section8SmoothingBridge
import ZhangLS.Spec.Lemma84RightTailBounds
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Finset
set_option maxHeartbeats 2000000

/-- A direct bound on the genuine ξ sum from its proved Perron integral. There
is no T<x requirement and no contour shift: it includes x=1. -/
theorem lemma84_boundary_xi_perron_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (c : ℝ) (j : Fin 3) (μ d r : ℕ) (hd : 0<d) (hr : 0<r)
    {b x : ℝ} (hb : 0<b) (hx : 0<x) :
    ‖lemma84XiSum χ c j μ d r x‖≤
      lemma84RightLineMajorant b d r*Real.exp (b*Real.log x)/(2*b) := by
  let f := fun t : ℝ => lemma84AnalyticCircleIntegrand χ
    (lemma83PaperBeta D c (j+1)) (lemma83PaperBeta D c (j+2)) (lemma84SmoothingBeta D μ)
    (lemma83EulerCorrection χ (lemma83PaperBeta D c) j d r) x ((b:ℂ)+I*(t:ℂ))
  have hi : Integrable f := lemma84_actual_right_line_integrable χ hD c j μ d r hb hx
  have hKi := (lemma84_log_kernel_integrable hb (Real.log x) (lemma84SmoothingBeta D μ).im).norm
  have hM := lemma84_right_line_majorant_nonneg hb d r
  have hbnd : ‖∫ t : ℝ, f t‖≤lemma84RightLineMajorant b d r*
      (Real.exp (b*Real.log x)*Real.pi/b) := by
    apply (norm_integral_le_integral_norm _).trans
    have hh := integral_mono hi.norm (hKi.const_mul (lemma84RightLineMajorant b d r))
      (fun t => lemma84_actual_integrand_right_bound χ c j μ d r hb hx t)
    simpa only [integral_const_mul,lemma84_log_kernel_norm_integral hb] using hh
  rw [lemma84_actual_xi_perron_factored χ c j μ d r hd hr hb hx,norm_mul,norm_inv]
  have hp : ‖(2*Real.pi:ℂ)‖=2*Real.pi := by
    rw [norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  rw [hp]
  calc
    _ ≤ (2*Real.pi)⁻¹*(lemma84RightLineMajorant b d r*(Real.exp (b*Real.log x)*Real.pi/b)) :=
      mul_le_mul_of_nonneg_left hbnd (by positivity)
    _ = _ := by field_simp <;> ring

noncomputable def lemma84BoundaryXiExponent : ℕ := ⌈3*lemma84UGrowthConstant⌉₊
noncomputable def lemma84BoundaryXiConstant : ℝ :=
  4*Real.exp 1*lemma84UGrowthConstant*Real.exp (lemma84UGrowthConstant/Real.log 2)

lemma lemma84_boundary_xi_constant_pos : 0<lemma84BoundaryXiConstant := by
  unfold lemma84BoundaryXiConstant
  positivity [lemma84_u_growth_constant_pos]

/-- The true right-line U bound yields only a fixed polylogarithmic arithmetic
loss, even at b=1/log T; b does not appear inside the fixed constant. -/
theorem lemma84_boundary_right_majorant {b y : ℝ} (hb : 0<b) (hy : 1<y)
    {d r : ℕ} (hd : 0<d) (hr : 0<r) (hlog : Real.log (d*r:ℕ)≤y) :
    lemma84RightLineMajorant b d r≤(1+b⁻¹)^3*
      (lemma84UGrowthConstant*Real.exp (lemma84UGrowthConstant/Real.log 2)*
        (1+Real.log y)^lemma84BoundaryXiExponent) := by
  have hprod : (∏ q∈(d*r).primeFactors, (1+lemma84UGrowthConstant*(q:ℝ)^(-(1+b))))≤
      ∏ q∈(d*r).primeFactors, (1+lemma84UGrowthConstant/(q:ℝ)) := by
    apply prod_le_prod (fun _ _ => by positivity [lemma84_u_growth_constant_pos])
    intro q hq
    have hq1 : (1:ℝ)≤q := by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).one_lt.le
    have hh := Real.rpow_le_rpow_of_exponent_le hq1 (show -(1+b)≤(-1:ℝ) by linarith)
    rw [Real.rpow_neg_one] at hh
    simpa only [div_eq_mul_inv] using add_le_add_right
      (mul_le_mul_of_nonneg_left hh lemma84_u_growth_constant_pos.le) 1
  have hpoly := lemma83_prime_product_uniform_le (d*r) (Nat.mul_pos hd hr) y
    lemma84UGrowthConstant lemma84BoundaryXiExponent hy hlog lemma84_u_growth_constant_pos.le
    (Nat.le_ceil _)
  unfold lemma84RightLineMajorant
  calc
    _ ≤ (1+b⁻¹)^3*(lemma84UGrowthConstant*
      (Real.exp (lemma84UGrowthConstant/Real.log 2)*(1+Real.log y)^lemma84BoundaryXiExponent)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hprod.trans hpoly)
          lemma84_u_growth_constant_pos.le) (by positivity)
    _ = _ := by ring

/-- Actual ξ bound on the closed small-cutoff interval 1≤x≤T. This neither
uses the original Lemma 8.4 estimate outside its range nor assumes coefficients. -/
theorem lemma84_boundary_xi_small_x {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (hL : 1<lemma23PaperL D) (c : ℝ) (j : Fin 3) (μ d r : ℕ)
    (hd : 0<d) (hr : 0<r) (hlog : Real.log (d*r:ℕ)≤lemma23PaperL D^9)
    {x : ℝ} (hx : 1≤x) (hxT : x≤lemma56PaperT D) :
    ‖lemma84XiSum χ c j μ d r x‖≤lemma84BoundaryXiConstant*
      (1+9*Real.log (lemma23PaperL D))^lemma84BoundaryXiExponent*
      (Real.log (lemma56PaperT D))^4 := by
  let H := Real.log (lemma56PaperT D)
  have hLp : 0<lemma23PaperL D := by linarith
  have hH : 1≤H := by
    dsimp [H]
    rw [lemma56PaperT,Real.log_exp]
    exact Real.one_le_rpow hL.le (by norm_num)
  have hHp : 0<H := by linarith
  have hb := inv_pos.mpr hHp
  have hx0 : 0<x := by linarith
  have hxl : Real.log x≤H := Real.log_le_log hx0 hxT
  have hxp : Real.exp (H⁻¹*Real.log x)≤Real.exp 1 := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hxl hb.le
    rwa [inv_mul_cancel₀ hHp.ne'] at hh
  have hy : 1<lemma23PaperL D^9 := one_lt_pow₀ hL (by norm_num)
  have hmaj := lemma84_boundary_right_majorant hb hy hd hr hlog
  rw [inv_inv,Real.log_pow] at hmaj
  norm_num only [Nat.cast_ofNat] at hmaj
  have hp := lemma84_boundary_xi_perron_bound χ hD c j μ d r hd hr hb hx0
  have hpoly0 : 0≤(1+9*Real.log (lemma23PaperL D))^lemma84BoundaryXiExponent := by
    positivity [Real.log_nonneg hL.le]
  calc
    _ ≤ ((1+H)^3*(lemma84UGrowthConstant*Real.exp (lemma84UGrowthConstant/Real.log 2)*
        (1+9*Real.log (lemma23PaperL D))^lemma84BoundaryXiExponent))*Real.exp 1/(2*H⁻¹) := by
      apply hp.trans
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul hmaj hxp (Real.exp_pos _).le (by positivity [lemma84_u_growth_constant_pos])
    _ ≤ _ := by
      have hh : (1+H)^3≤8*H^3 := by nlinarith [sq_nonneg (H-1)]
      have hh' := mul_le_mul_of_nonneg_right hh (show 0≤
        lemma84UGrowthConstant*Real.exp (lemma84UGrowthConstant/Real.log 2)*
          (1+9*Real.log (lemma23PaperL D))^lemma84BoundaryXiExponent*Real.exp 1*H/2 by
          positivity [lemma84_u_growth_constant_pos])
      dsimp [lemma84BoundaryXiConstant]
      have he : ((1+H)^3*(lemma84UGrowthConstant*Real.exp (lemma84UGrowthConstant/Real.log 2)*
        (1+9*Real.log (lemma23PaperL D))^lemma84BoundaryXiExponent))*Real.exp 1/(2*H⁻¹)=
        (1+H)^3*(lemma84UGrowthConstant*Real.exp (lemma84UGrowthConstant/Real.log 2)*
          (1+9*Real.log (lemma23PaperL D))^lemma84BoundaryXiExponent*Real.exp 1*H/2) := by
        field_simp
      rw [he]
      convert hh' using 1 <;> dsimp [H] <;> ring

end ZhangLS.Spec
