import ZhangLS.Spec.Proposition71DeltaOneDoubleSeries
import ZhangLS.Spec.Proposition71FrontCoefficientBounds
import ZhangLS.Spec.Proposition71ReciprocalGammaNorm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # The actual reciprocal-Z integrand and its exact parity error

Long and short coefficients are independent of the primitive character in the
functional equation. The true conductor N, Gauss factor and short-index weights
are retained before every norm estimate.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Finset Set
open scoped Classical
set_option maxHeartbeats 3000000

noncomputable def proposition71FrontActualIntegrand {N : ℕ} [NeZero N] (D : ℕ)
    (θ : DirichletCharacter ℂ N) (c : ℕ → ℂ) (S : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  (lemma23DirichletZ θ ((3/2 : ℂ)+(t : ℂ)*I))⁻¹*
    LSeries c ((3/2 : ℂ)+(t : ℂ)*I)*
    (∑n∈S, a n*(n : ℂ)^(((3/2 : ℂ)+(t : ℂ)*I)-1))*
    lemma53PaperOmega D ((3/2 : ℂ)+(t : ℂ)*I)

noncomputable def proposition71FrontGaussIntegrand {N : ℕ} [NeZero N] (D : ℕ)
    (θ : DirichletCharacter ℂ N) (c : ℕ → ℂ) (S : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  gaussSum θ⁻¹ ZMod.stdAddChar*proposition71FrontDominantIntegrand D c S a (N : ℝ) t

lemma proposition71_front_actual_factorization {N : ℕ} [NeZero N] (D : ℕ)
    (θ : DirichletCharacter ℂ N) (hθ : θ.IsPrimitive) (hN : N≠1)
    (c : ℕ → ℂ) (S : Finset ℕ) (a : ℕ → ℂ) {t : ℝ} (ht : t≠0) :
    proposition71FrontActualIntegrand D θ c S a t=
      proposition71FrontGaussIntegrand D θ c S a t*
        (1+θ (-1)*Complex.exp ((Real.pi : ℂ)*I*((3/2 : ℂ)+(t : ℂ)*I))) := by
  have hs : ((3/2 : ℂ)+(t : ℂ)*I).im≠0 := by simpa using ht
  unfold proposition71FrontActualIntegrand proposition71FrontGaussIntegrand
    proposition71FrontDominantIntegrand proposition71GammaOmegaKernel
  rw [proposition71_reciprocal_Z_exact θ hθ hN hs]
  simp only [Complex.ofReal_natCast]
  ring

lemma proposition71_front_error_exact {N : ℕ} [NeZero N] (D : ℕ)
    (θ : DirichletCharacter ℂ N) (hθ : θ.IsPrimitive) (hN : N≠1)
    (c : ℕ → ℂ) (S : Finset ℕ) (a : ℕ → ℂ) {t : ℝ} (ht : t≠0) :
    proposition71FrontActualIntegrand D θ c S a t-
      proposition71FrontGaussIntegrand D θ c S a t=
      proposition71FrontGaussIntegrand D θ c S a t*
        θ (-1)*Complex.exp ((Real.pi : ℂ)*I*((3/2 : ℂ)+(t : ℂ)*I)) := by
  rw [proposition71_front_actual_factorization D θ hθ hN c S a ht]
  ring

lemma proposition71_front_error_norm {N : ℕ} [NeZero N] (D : ℕ)
    (θ : DirichletCharacter ℂ N) (hθ : θ.IsPrimitive) (hN : N≠1)
    (c : ℕ → ℂ) (S : Finset ℕ) (a : ℕ → ℂ) {t : ℝ} (ht : t≠0) :
    ‖proposition71FrontActualIntegrand D θ c S a t-
      proposition71FrontGaussIntegrand D θ c S a t‖=
      ‖proposition71FrontGaussIntegrand D θ c S a t‖*Real.exp (-Real.pi*t) := by
  rw [proposition71_front_error_exact D θ hθ hN c S a ht,norm_mul,norm_mul,
    proposition71_character_neg_one_norm,mul_one,Complex.norm_exp]
  congr 2
  simp [Complex.mul_re,Complex.mul_im]

lemma proposition71_front_gauss_integrable {D N : ℕ} [NeZero N] (hD : 1<D)
    (θ : DirichletCharacter ℂ N) (c : ℕ → ℂ) (hseries : LSeriesSummable c (3/2 : ℂ))
    (S : Finset ℕ) (hS : ∀n∈S, 0<n) (a : ℕ → ℂ) :
    Integrable (proposition71FrontGaussIntegrand D θ c S a) := by
  have hNp : 0<(N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  exact ((proposition71_actual_delta_one_double_series hD c hseries S hS a hNp).1).const_mul _

lemma proposition71_front_gauss_norm_bound {D N : ℕ} [NeZero N]
    (θ : DirichletCharacter ℂ N) (hθ : θ.IsPrimitive) (hN : N≠1)
    {B : ℝ} (hB : 0≤B) (c : ℕ → ℂ) (hc : ∀n, 0<n → ‖c n‖≤B*(lemma34Tau 5 n : ℝ))
    (S : Finset ℕ) (hS : ∀n∈S, 0<n) (a : ℕ → ℂ) (t : ℝ) :
    ‖proposition71FrontGaussIntegrand D θ c S a t‖≤
      ((N : ℝ)*B*proposition71TauFiveThreeHalvesMass*proposition71ShortCoefficientMass S a)*
        ‖proposition71GammaOmegaKernel D t‖ := by
  have hi : θ⁻¹.IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def,DirichletCharacter.conductor_inv]
    exact (DirichletCharacter.isPrimitive_def θ).mp hθ
  have hs : ((3/2 : ℂ)+(t : ℂ)*I).re=(3/2 : ℝ) := by norm_num
  have hpow : ‖((N : ℝ) : ℂ)^(((3/2 : ℂ)+(t : ℂ)*I)-1)‖=Real.sqrt (N : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)),
      Complex.sub_re,hs,Complex.one_re]
    norm_num only [show (3/2 : ℝ)-1=1/2 by norm_num]
    rw [←Real.sqrt_eq_rpow]
  have hM := proposition71_tau_three_halves_mass_pos.le
  have ha0 := proposition71_short_coefficient_mass_nonneg S a
  unfold proposition71FrontGaussIntegrand proposition71FrontDominantIntegrand
  simp only [norm_mul]
  rw [proposition71_primitive_gauss_norm θ⁻¹ hi hN,hpow]
  calc
    _≤Real.sqrt (N : ℝ)*(Real.sqrt (N : ℝ)*(B*proposition71TauFiveThreeHalvesMass)*
        proposition71ShortCoefficientMass S a*‖proposition71GammaOmegaKernel D t‖) := by
      gcongr
      · exact proposition71_front_lseries_norm_bound hB c hc hs
      · exact proposition71_short_polynomial_norm S hS a hs
    _=((Real.sqrt (N : ℝ))^2)*B*proposition71TauFiveThreeHalvesMass*
        proposition71ShortCoefficientMass S a*‖proposition71GammaOmegaKernel D t‖ := by ring
    _=_ := by rw [Real.sq_sqrt (Nat.cast_nonneg N)]

/-- The actual Z integrand is integrable on every positive-height closed segment.
No assertion about the parity error at negative height is used. -/
lemma proposition71_front_actual_interval_integrable {D N : ℕ} [NeZero N] (hD : 1<D)
    (θ : DirichletCharacter ℂ N) (hθ : θ.IsPrimitive) (hN : N≠1)
    (c : ℕ → ℂ) (hseries : LSeriesSummable c (3/2 : ℂ))
    (S : Finset ℕ) (hS : ∀n∈S, 0<n) (a : ℕ → ℂ)
    {A B : ℝ} (hA : 0<A) (hAB : A≤B) :
    IntervalIntegrable (proposition71FrontActualIntegrand D θ c S a) volume A B := by
  have hI := (proposition71_front_gauss_integrable hD θ c hseries S hS a).intervalIntegrable (a := A) (b := B)
  have hcont : Continuous (fun t : ℝ =>
      (1 : ℂ)+θ (-1)*Complex.exp ((Real.pi : ℂ)*I*((3/2 : ℂ)+(t : ℂ)*I))) := by fun_prop
  apply (hI.mul_continuousOn hcont.continuousOn).congr
  intro t ht
  rw [uIoc_of_le hAB] at ht
  exact (proposition71_front_actual_factorization D θ hθ hN c S a (ne_of_gt (hA.trans ht.1))).symm

end ZhangLS.Spec
