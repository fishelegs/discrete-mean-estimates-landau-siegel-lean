import ZhangLS.Spec.Proposition71GammaLineBound
import ZhangLS.Spec.Lemma54GaussianConcentration

/-! # Genuine all-height Γω mass and original-contour exterior decay

The polynomial Γ bound and actual Gaussian density supply both integrability
and a quantitative tail beyond the original ±L^405 segment.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set Filter
open scoped Topology
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

noncomputable def proposition71GammaOmegaKernel (D : ℕ) (t : ℝ) : ℂ :=
  lemma53PaperThetaStar ((3/2 : ℂ)+(t : ℂ)*I)*
    lemma53PaperOmega D ((3/2 : ℂ)+(t : ℂ)*I)

lemma proposition71_gamma_omega_integrable {D : ℕ} (hD : 1<D) :
    Integrable (proposition71GammaOmegaKernel D) := by
  have hi := lemma53_mellin_integrand_integrable hD (by norm_num : (0:ℝ)<1)
  have he : lemma53MellinIntegrand D 1=proposition71GammaOmegaKernel D := by
    funext t
    simp [lemma53MellinIntegrand,proposition71GammaOmegaKernel]
  rw [he] at hi
  exact hi

lemma proposition71_omega_gamma_line_density {D : ℕ} (hD : 1<D) (t : ℝ) :
    ‖lemma53PaperOmega D ((3/2 : ℂ)+(t : ℂ)*I)‖=
      (2*Real.pi)*Real.exp (1/(4*lemma53PaperScale D^2))*
        lemma54GaussianDensity (2*Real.pi*lemma53PaperScale D) (lemma23PaperCenter D).im t := by
  have hB := lemma53_scale_pos hD
  have hω := lemma53_omega_norm_vertical hD (3/2) t
  norm_num only [Complex.ofReal_div,Complex.ofReal_ofNat,
    show (3/2 : ℝ)-1/2=1 by norm_num,one_pow] at hω
  rw [hω,lemma54_gaussian_density_factor]
  have he : (1-(t-(lemma23PaperCenter D).im)^2)/(4*lemma53PaperScale D^2)=
      1/(4*lemma53PaperScale D^2)-(Real.pi/(2*Real.pi*lemma53PaperScale D))^2*
        (t-(lemma23PaperCenter D).im)^2 := by field_simp; ring
  rw [he,sub_eq_add_neg,Real.exp_add]
  field_simp

lemma proposition71_gamma_omega_density_bound {D : ℕ} (hD : 1<D)
    (hL : 3≤lemma23PaperL D) (t : ℝ) :
    ‖proposition71GammaOmegaKernel D t‖≤(16*Real.pi*Real.exp 1)*
      ((1+t^2)*lemma54GaussianDensity (2*Real.pi*lemma53PaperScale D) (lemma23PaperCenter D).im t) := by
  have hB := lemma53_scale_pos hD
  have hB1 : 1≤lemma53PaperScale D := one_le_pow₀ (by linarith : 1≤lemma23PaperL D)
  have hE : Real.exp (1/(4*lemma53PaperScale D^2))≤Real.exp 1 := by
    apply Real.exp_le_exp.mpr
    apply (div_le_iff₀ (by positivity : 0<4*lemma53PaperScale D^2)).mpr
    nlinarith only [hB1]
  have htheta : ‖lemma53PaperThetaStar ((3/2 : ℂ)+(t : ℂ)*I)‖≤8*(1+t^2) := by
    apply (proposition71_theta_star_three_halves_bound t).trans
    nlinarith only [sq_nonneg (|t|-1),sq_abs t,sq_nonneg t]
  have hρ : 0≤lemma54GaussianDensity (2*Real.pi*lemma53PaperScale D) (lemma23PaperCenter D).im t :=
    (lemma54_gaussian_density_pos (by positivity) _ _).le
  unfold proposition71GammaOmegaKernel
  rw [norm_mul,proposition71_omega_gamma_line_density hD]
  calc
    _≤(8*(1+t^2))*((2*Real.pi)*Real.exp 1*
        lemma54GaussianDensity (2*Real.pi*lemma53PaperScale D) (lemma23PaperCenter D).im t) := by
      gcongr
    _=_ := by ring

lemma proposition71_gamma_omega_mass_bound {D : ℕ} (hD : 1<D) (hL : 3≤lemma23PaperL D) :
    (∫ t : ℝ, ‖proposition71GammaOmegaKernel D t‖)≤
      (64*Real.pi*Real.exp 1)*(1+(lemma23PaperCenter D).im^2)*(1+8*lemma53PaperScale D^2) := by
  have hB := lemma53_scale_pos hD
  have hB' : 0<2*Real.pi*lemma53PaperScale D := by positivity
  have hi := (lemma54_gaussian_quadratic_integrable hB' (lemma23PaperCenter D).im).const_mul (16*Real.pi*Real.exp 1)
  calc
    _≤∫ t : ℝ, (16*Real.pi*Real.exp 1)*
        ((1+t^2)*lemma54GaussianDensity (2*Real.pi*lemma53PaperScale D) (lemma23PaperCenter D).im t) :=
      integral_mono ((proposition71_gamma_omega_integrable hD).norm) hi (proposition71_gamma_omega_density_bound hD hL)
    _=(16*Real.pi*Real.exp 1)*(∫ t : ℝ,
        (1+t^2)*lemma54GaussianDensity (2*Real.pi*lemma53PaperScale D) (lemma23PaperCenter D).im t) := integral_const_mul _ _
    _≤(16*Real.pi*Real.exp 1)*(4*(1+(lemma23PaperCenter D).im^2)*
        (1+2*(2*Real.pi*lemma53PaperScale D)^2/Real.pi^2)) :=
      mul_le_mul_of_nonneg_left (lemma54_gaussian_quadratic_integral_bound hB' _) (by positivity)
    _=_ := by field_simp; ring

/-- The full exterior of the original J(1) height window, not only two boundary points. -/
theorem proposition71_gamma_omega_exterior_bound {D : ℕ} (hD : 1<D)
    (hL : 3≤lemma23PaperL D) {S : Set ℝ} (hS : MeasurableSet S)
    (hgap : ∀t∈S, lemma23PaperL D^405≤|t-(lemma23PaperCenter D).im|) :
    (∫ t : ℝ in S, ‖proposition71GammaOmegaKernel D t‖)≤
      (128*Real.pi*Real.exp 1)*(1+(lemma23PaperCenter D).im^2)*(1+32*lemma53PaperScale D^2)*
        Real.exp (-lemma23PaperL D^10/8) := by
  have hB := lemma53_scale_pos hD
  have hB' : 0<2*Real.pi*lemma53PaperScale D := by positivity
  have hLp : 0<lemma23PaperL D := by linarith
  have hi := (lemma54_gaussian_quadratic_integrable hB' (lemma23PaperCenter D).im).const_mul (16*Real.pi*Real.exp 1)
  have hmass := lemma54_gaussian_exterior_quadratic_mass hB' (pow_nonneg hLp.le 405) hS hgap
  have he : ((Real.pi*lemma23PaperL D^405/(2*Real.pi*lemma53PaperScale D))^2)/2=
      lemma23PaperL D^10/8 := by
    unfold lemma53PaperScale
    field_simp
    ring
  calc
    _≤∫ t : ℝ in S, (16*Real.pi*Real.exp 1)*
        ((1+t^2)*lemma54GaussianDensity (2*Real.pi*lemma53PaperScale D) (lemma23PaperCenter D).im t) := by
      apply setIntegral_mono_on (proposition71_gamma_omega_integrable hD).norm.integrableOn hi.integrableOn hS
      exact fun t ht => proposition71_gamma_omega_density_bound hD hL t
    _=(16*Real.pi*Real.exp 1)*(∫ t : ℝ in S,
        (1+t^2)*lemma54GaussianDensity (2*Real.pi*lemma53PaperScale D) (lemma23PaperCenter D).im t) := integral_const_mul _ _
    _≤(16*Real.pi*Real.exp 1)*((8*(1+(lemma23PaperCenter D).im^2)*
        (1+8*(2*Real.pi*lemma53PaperScale D)^2/Real.pi^2))*
          Real.exp (-((Real.pi*lemma23PaperL D^405/(2*Real.pi*lemma53PaperScale D))^2)/2)) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _=_ := by rw [neg_div,he]; field_simp; ring

end ZhangLS.Spec
