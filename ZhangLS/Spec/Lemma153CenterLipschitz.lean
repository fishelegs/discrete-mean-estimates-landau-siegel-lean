import ZhangLS.Spec.Lemma153CenterReduction
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex
set_option maxHeartbeats 3000000

/-- A denominator-free Lipschitz bound retaining the two q⁻¹ gains at the
center. The mixed ratio's deviation from one is the needed first-order
cancellation; replacing it by an arbitrary bounded coefficient would lose
summability of the shift error. -/
lemma lemma153_reduced_center_lipschitz (f f₀ A y y₀ t t₀ z : ℂ) (u : ℝ)
    (hu0 : 0 ≤ u) (hu : u ≤ 1/2) (hz : ‖z‖ = u)
    (hy : ‖y‖ ≤ u) (hy₀ : ‖y₀‖ ≤ u) (hA : ‖A‖ ≤ 2)
    (ht : ‖t‖ ≤ 1) (ht₀ : ‖t₀‖ ≤ 1)
    (hf₀ : ‖f₀‖ ≤ 10000) (hf₀1 : ‖f₀-1‖ ≤ 30000*u) :
    ‖lemma153ReducedCorrection f A y t z-lemma153ReducedCorrection f₀ A y₀ t₀ z‖ ≤
      200000*(u*‖f-f₀‖+u*‖y-y₀‖+u^2*‖t-t₀‖) := by
  let df := ‖f-f₀‖
  let dy := ‖y-y₀‖
  let dt := ‖t-t₀‖
  have hdf : 0≤df := norm_nonneg _
  have hdy : 0≤dy := norm_nonneg _
  have hdt : 0≤dt := norm_nonneg _
  have ht2 : ‖t^2‖ ≤ 1 := by rw [norm_pow]; nlinarith [norm_nonneg t]
  have ht2₀ : ‖t₀^2‖ ≤ 1 := by rw [norm_pow]; nlinarith [norm_nonneg t₀]
  have h1t : ‖1-t‖ ≤ 2 := by have := norm_sub_le (1:ℂ) t; rw [norm_one] at this; linarith
  have ht21 : ‖t^2-1‖ ≤ 2 := by have := norm_sub_le (t^2) (1:ℂ); rw [norm_one] at this; linarith
  have htd : ‖t^2-t₀^2‖ ≤ 2*dt := lemma153_norm_square_difference t t₀ ht ht₀
  have hF₀ : ‖f₀*A*y₀‖ ≤ 20000*u := by
    simp only [norm_mul]
    calc
      _ ≤ 10000*2*u := by gcongr
      _ = _ := by ring
  have hF : ‖f*A*y-f₀*A*y₀‖ ≤ 2*u*df+20000*dy := by
    rw [show f*A*y-f₀*A*y₀ = (f-f₀)*A*y+f₀*A*(y-y₀) by ring]
    apply (norm_add_le _ _).trans
    simp only [norm_mul]
    change df*‖A‖*‖y‖+‖f₀‖*‖A‖*dy ≤ _
    calc
      _ ≤ df*2*u+10000*2*dy := by gcongr
      _ = _ := by ring
  have hL₁ : ‖t*(f-1)-t₀*(f₀-1)‖ ≤ df+30000*u*dt := by
    have hh := lemma153_norm_mul_difference t (f-1) t₀ (f₀-1)
    rw [show (f-1)-(f₀-1) = f-f₀ by ring] at hh
    apply hh.trans
    have h1 := mul_le_mul_of_nonneg_right ht hdf
    have h2 := mul_le_mul_of_nonneg_left hf₀1 hdt
    dsimp [df,dt] at *
    nlinarith
  have hL₂ : ‖f*A*y*(1-t)-f₀*A*y₀*(1-t₀)‖ ≤
      4*u*df+40000*dy+20000*u*dt := by
    rw [mul_comm (f*A*y),mul_comm (f₀*A*y₀)]
    have hh := lemma153_norm_mul_difference (1-t) (f*A*y) (1-t₀) (f₀*A*y₀)
    rw [show (1-t)-(1-t₀) = -(t-t₀) by ring,norm_neg] at hh
    apply hh.trans
    have h1 := mul_le_mul h1t hF (norm_nonneg _) (by norm_num : (0:ℝ)≤2)
    have h2 := mul_le_mul_of_nonneg_left hF₀ hdt
    dsimp [dt] at *
    nlinarith
  have hL : ‖(t*(f-1)+f*A*y*(1-t))-(t₀*(f₀-1)+f₀*A*y₀*(1-t₀))‖ ≤
      3*df+40000*dy+50000*u*dt := by
    rw [show (t*(f-1)+f*A*y*(1-t))-(t₀*(f₀-1)+f₀*A*y₀*(1-t₀)) =
      (t*(f-1)-t₀*(f₀-1))+(f*A*y*(1-t)-f₀*A*y₀*(1-t₀)) by ring]
    apply (norm_add_le _ _).trans
    have hmul := mul_le_mul_of_nonneg_right hu hdf
    nlinarith only [hL₁,hL₂,hmul]
  have hQ₁ : ‖t^2*(1-f)-t₀^2*(1-f₀)‖ ≤ df+60000*u*dt := by
    have hh := lemma153_norm_mul_difference (t^2) (1-f) (t₀^2) (1-f₀)
    rw [show (1-f)-(1-f₀) = -(f-f₀) by ring,norm_neg,norm_sub_rev (1:ℂ) f₀] at hh
    apply hh.trans
    have h1 := mul_le_mul_of_nonneg_right ht2 hdf
    have h2 := mul_le_mul htd hf₀1 (norm_nonneg _) (by positivity : 0≤2*dt)
    dsimp [df] at *
    nlinarith
  have hQ₂ : ‖f*t-f₀*t₀‖ ≤ df+10000*dt := by
    rw [mul_comm f t,mul_comm f₀ t₀]
    apply (lemma153_norm_mul_difference t f t₀ f₀).trans
    have h1 := mul_le_mul_of_nonneg_right ht hdf
    have h2 := mul_le_mul_of_nonneg_left hf₀ hdt
    dsimp [df,dt] at *
    nlinarith
  have hQ₃ : ‖f*A*y*(t^2-1)-f₀*A*y₀*(t₀^2-1)‖ ≤
      4*u*df+40000*dy+40000*u*dt := by
    rw [mul_comm (f*A*y),mul_comm (f₀*A*y₀)]
    have hh := lemma153_norm_mul_difference (t^2-1) (f*A*y) (t₀^2-1) (f₀*A*y₀)
    rw [show (t^2-1)-(t₀^2-1) = t^2-t₀^2 by ring] at hh
    apply hh.trans
    have h1 := mul_le_mul ht21 hF (norm_nonneg _) (by norm_num : (0:ℝ)≤2)
    have h2 := mul_le_mul htd hF₀ (norm_nonneg _) (by positivity : 0≤2*dt)
    nlinarith
  have hQ : ‖(t^2*(1-f)-f*t+f*A*y*(t^2-1))-
      (t₀^2*(1-f₀)-f₀*t₀+f₀*A*y₀*(t₀^2-1))‖ ≤ 4*df+40000*dy+60000*dt := by
    rw [show (t^2*(1-f)-f*t+f*A*y*(t^2-1))-
      (t₀^2*(1-f₀)-f₀*t₀+f₀*A*y₀*(t₀^2-1)) =
        (t^2*(1-f)-t₀^2*(1-f₀))-(f*t-f₀*t₀)+
          (f*A*y*(t^2-1)-f₀*A*y₀*(t₀^2-1)) by ring]
    apply (norm_add_le _ _).trans
    apply (add_le_add (norm_sub_le _ _) le_rfl).trans
    have hmulF := mul_le_mul_of_nonneg_right hu hdf
    have hmulT := mul_le_mul_of_nonneg_right hu hdt
    nlinarith only [hQ₁,hQ₂,hQ₃,hmulF,hmulT]
  unfold lemma153ReducedCorrection
  rw [show 1+2*(t*(f-1)+f*A*y*(1-t))*z+(t^2*(1-f)-f*t+f*A*y*(t^2-1))*z^2-
      (1+2*(t₀*(f₀-1)+f₀*A*y₀*(1-t₀))*z+(t₀^2*(1-f₀)-f₀*t₀+f₀*A*y₀*(t₀^2-1))*z^2) =
    2*((t*(f-1)+f*A*y*(1-t))-(t₀*(f₀-1)+f₀*A*y₀*(1-t₀)))*z+
      ((t^2*(1-f)-f*t+f*A*y*(t^2-1))-(t₀^2*(1-f₀)-f₀*t₀+f₀*A*y₀*(t₀^2-1)))*z^2 by ring]
  apply (norm_add_le _ _).trans
  simp only [norm_mul,norm_pow,hz]
  norm_num only [norm_ofNat]
  have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL (by norm_num : (0:ℝ)≤2)) hu0
  have h2 := mul_le_mul_of_nonneg_right hQ (sq_nonneg u)
  have hFsmall := mul_le_mul_of_nonneg_right hu (mul_nonneg hu0 hdf)
  have hYsmall := mul_le_mul_of_nonneg_right hu (mul_nonneg hu0 hdy)
  have h3 := mul_nonneg hu0 hdf
  have h4 := mul_nonneg hu0 hdy
  have h5 := mul_nonneg (sq_nonneg u) hdt
  dsimp [df,dy,dt] at *
  nlinarith only [h1,h2,hFsmall,hYsmall,h3,h4,h5]

end ZhangLS.Spec
