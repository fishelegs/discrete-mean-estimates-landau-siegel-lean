import ZhangLS.Spec.Proposition71ReciprocalGamma
import ZhangLS.Spec.Lemma53MellinConvergence
import Mathlib.Analysis.Real.Pi.Bounds

/-! # A genuine polynomial bound for the original Γ kernel on Re s=3/2

Reflection and the Γ recurrence supply the actual all-height norm. No
Stirling estimate is assumed, and negative heights remain included.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex ComplexConjugate
set_option maxHeartbeats 2500000

lemma proposition71_gamma_half_norm_square (t : ℝ) :
    ‖Gamma ((1/2 : ℂ)+(t : ℂ)*I)‖^2=Real.pi/Real.cosh (Real.pi*t) := by
  let z : ℂ := (1/2 : ℂ)+(t : ℂ)*I
  have hconj : 1-z=conj z := by dsimp [z]; apply Complex.ext <;> simp <;> ring
  have hsin : Complex.sin ((Real.pi : ℂ)*z)=(Real.cosh (Real.pi*t) : ℂ) := by
    have he : (Real.pi : ℂ)*z=(Real.pi : ℂ)/2+((Real.pi*t : ℝ) : ℂ)*I := by dsimp [z]; push_cast; ring
    rw [he,Complex.sin_add_mul_I,Complex.sin_pi_div_two,Complex.cos_pi_div_two]
    simp only [one_mul,zero_mul,add_zero,←Complex.ofReal_cosh]
  have hh := Complex.Gamma_mul_Gamma_one_sub z
  rw [hconj,Complex.Gamma_conj,Complex.mul_conj,Complex.normSq_eq_norm_sq,hsin] at hh
  exact_mod_cast hh

lemma proposition71_gamma_three_halves_norm_square (t : ℝ) :
    ‖Gamma ((3/2 : ℂ)+(t : ℂ)*I)‖^2=(t^2+1/4)*Real.pi/Real.cosh (Real.pi*t) := by
  let z : ℂ := (1/2 : ℂ)+(t : ℂ)*I
  have hz : z≠0 := by intro h; have := congrArg Complex.re h; norm_num [z] at this
  have he : (3/2 : ℂ)+(t : ℂ)*I=z+1 := by dsimp [z]; ring
  rw [he,Complex.Gamma_add_one z hz,norm_mul,mul_pow]
  have hn : ‖z‖^2=t^2+1/4 := by rw [Complex.sq_norm,Complex.normSq_apply]; simp [z]; ring
  rw [hn,show ‖Gamma z‖^2=Real.pi/Real.cosh (Real.pi*t) from proposition71_gamma_half_norm_square t]
  ring

lemma proposition71_exp_div_cosh_le_two (t : ℝ) : Real.exp t/Real.cosh t≤2 := by
  apply (div_le_iff₀ (Real.cosh_pos t)).mpr
  rw [Real.cosh_eq]
  have he := Real.exp_pos (-t)
  linarith

/-- The actual Θ*(1-s) kernel, under the repository's argument convention,
is bounded at every height by 4(1+|t|). -/
theorem proposition71_theta_star_three_halves_bound (t : ℝ) :
    ‖lemma53PaperThetaStar ((3/2 : ℂ)+(t : ℂ)*I)‖≤4*(1+|t|) := by
  have hg : ‖Gamma ((3/2 : ℂ)+(t : ℂ)*I)‖^2*Real.exp (Real.pi*t)≤8*(1+t^2) := by
    calc
      _=(t^2+1/4)*Real.pi*(Real.exp (Real.pi*t)/Real.cosh (Real.pi*t)) := by
        rw [proposition71_gamma_three_halves_norm_square]; ring
      _≤(1+t^2)*4*2 := by
        have ht : t^2+1/4≤1+t^2 := by linarith
        exact mul_le_mul (mul_le_mul ht Real.pi_lt_four.le Real.pi_pos.le (by positivity))
          (proposition71_exp_div_cosh_le_two _) (by positivity) (by positivity)
      _=_ := by ring
  have hc : (2*Real.pi)^(-3/2 : ℝ)≤1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by norm_num)
  have hc0 : 0≤(2*Real.pi)^(-3/2 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hc2 : ((2*Real.pi)^(-3/2 : ℝ))^2≤1 := by nlinarith only [hc,hc0]
  have he : (Real.exp (Real.pi*t/2))^2=Real.exp (Real.pi*t) := by
    rw [←Real.exp_nat_mul]
    congr 1
    ring
  have hsq : ‖lemma53PaperThetaStar ((3/2 : ℂ)+(t : ℂ)*I)‖^2≤8*(1+t^2) := by
    have hθ := lemma53_theta_star_norm_vertical (3/2) t
    norm_num only [Complex.ofReal_div,Complex.ofReal_ofNat] at hθ
    rw [hθ,mul_pow,mul_pow,he]
    calc
      _=((2*Real.pi)^(-3/2 : ℝ))^2*(‖Gamma ((3/2 : ℂ)+(t : ℂ)*I)‖^2*Real.exp (Real.pi*t)) := by ring
      _≤1*(8*(1+t^2)) := mul_le_mul hc2 hg (by positivity) (by norm_num)
      _=_ := by ring
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  have ht := sq_abs t
  have ha := abs_nonneg t
  nlinarith only [hsq,ht,ha,sq_nonneg t]

end ZhangLS.Spec
