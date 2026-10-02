import ZhangLS.Spec.Proposition71FrontIntegrands

/-! # Exact segment-to-full-line comparison for the original front end

The error consists of the actual parity term on a positive-height segment and
the actual exterior of the dominant Gamma integral. No averaged estimate is
an input.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set Filter
open scoped Classical
set_option maxHeartbeats 3000000

lemma proposition71_integral_segment_complement (g : ℝ → ℂ) (hg : Integrable g)
    {A B : ℝ} (hAB : A≤B) :
    ‖(∫ t in A..B, g t)-(∫t : ℝ, g t)‖=‖∫t : ℝ in (Ioc A B)ᶜ, g t‖ := by
  rw [intervalIntegral.integral_of_le hAB,setIntegral_compl measurableSet_Ioc hg,norm_sub_rev]

lemma proposition71_front_parity_segment_bound {D N : ℕ} [NeZero N] (hD : 1<D)
    (θ : DirichletCharacter ℂ N) (hθ : θ.IsPrimitive) (hN : N≠1)
    {B₀ : ℝ} (hB₀ : 0≤B₀) (c : ℕ → ℂ)
    (hc : ∀n, 0<n → ‖c n‖≤B₀*(lemma34Tau 5 n : ℝ))
    (S : Finset ℕ) (hS : ∀n∈S, 0<n) (a : ℕ → ℂ)
    {A B : ℝ} (hA : 0<A) (hAB : A≤B) :
    ‖(∫t in A..B, proposition71FrontActualIntegrand D θ c S a t)-
      (∫t in A..B, proposition71FrontGaussIntegrand D θ c S a t)‖≤
      ((N : ℝ)*B₀*proposition71TauFiveThreeHalvesMass*proposition71ShortCoefficientMass S a)*
        Real.exp (-Real.pi*A)*(∫t : ℝ, ‖proposition71GammaOmegaKernel D t‖) := by
  let K := (N : ℝ)*B₀*proposition71TauFiveThreeHalvesMass*proposition71ShortCoefficientMass S a
  have hK : 0≤K := by
    dsimp [K]
    exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg N) hB₀)
      proposition71_tau_three_halves_mass_pos.le) (proposition71_short_coefficient_mass_nonneg S a)
  have hs := proposition71_front_coefficient_summable hB₀ c hc (by norm_num : (1 : ℝ)<(3/2 : ℂ).re)
  have hactual := proposition71_front_actual_interval_integrable hD θ hθ hN c hs S hS a hA hAB
  have hgauss := proposition71_front_gauss_integrable hD θ c hs S hS a
  have hkernel := (proposition71_gamma_omega_integrable hD).norm
  rw [←intervalIntegral.integral_sub hactual hgauss.intervalIntegrable,intervalIntegral.integral_of_le hAB]
  calc
    _≤∫t : ℝ in Ioc A B, K*Real.exp (-Real.pi*A)*‖proposition71GammaOmegaKernel D t‖ := by
      apply MeasureTheory.norm_integral_le_of_norm_le (hkernel.const_mul _).integrableOn
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [proposition71_front_error_norm D θ hθ hN c S a (ne_of_gt (hA.trans ht.1))]
      have he : Real.exp (-Real.pi*t)≤Real.exp (-Real.pi*A) := by
        apply Real.exp_le_exp.mpr
        nlinarith only [ht.1.le,Real.pi_pos]
      calc
        _≤(K*‖proposition71GammaOmegaKernel D t‖)*Real.exp (-Real.pi*A) :=
          mul_le_mul (proposition71_front_gauss_norm_bound θ hθ hN hB₀ c hc S hS a t)
            he (Real.exp_pos _).le (mul_nonneg hK (norm_nonneg _))
        _=_ := by ring
    _=(K*Real.exp (-Real.pi*A))*(∫t : ℝ in Ioc A B, ‖proposition71GammaOmegaKernel D t‖) := integral_const_mul _ _
    _≤(K*Real.exp (-Real.pi*A))*(∫t : ℝ, ‖proposition71GammaOmegaKernel D t‖) := by
      apply mul_le_mul_of_nonneg_left (setIntegral_le_integral hkernel (Eventually.of_forall (fun t => norm_nonneg _)))
      positivity

lemma proposition71_front_exterior_bound {D N : ℕ} [NeZero N] (hD : 1<D)
    (θ : DirichletCharacter ℂ N) (hθ : θ.IsPrimitive) (hN : N≠1)
    {B₀ : ℝ} (hB₀ : 0≤B₀) (c : ℕ → ℂ)
    (hc : ∀n, 0<n → ‖c n‖≤B₀*(lemma34Tau 5 n : ℝ))
    (S : Finset ℕ) (hS : ∀n∈S, 0<n) (a : ℕ → ℂ)
    {A B : ℝ} (hAB : A≤B) :
    ‖(∫t in A..B, proposition71FrontGaussIntegrand D θ c S a t)-
      (∫t : ℝ, proposition71FrontGaussIntegrand D θ c S a t)‖≤
      ((N : ℝ)*B₀*proposition71TauFiveThreeHalvesMass*proposition71ShortCoefficientMass S a)*
        (∫t : ℝ in (Ioc A B)ᶜ, ‖proposition71GammaOmegaKernel D t‖) := by
  have hs := proposition71_front_coefficient_summable hB₀ c hc (by norm_num : (1 : ℝ)<(3/2 : ℂ).re)
  rw [proposition71_integral_segment_complement _ (proposition71_front_gauss_integrable hD θ c hs S hS a) hAB]
  calc
    _≤∫t : ℝ in (Ioc A B)ᶜ,
        ((N : ℝ)*B₀*proposition71TauFiveThreeHalvesMass*proposition71ShortCoefficientMass S a)*
          ‖proposition71GammaOmegaKernel D t‖ := by
      apply MeasureTheory.norm_integral_le_of_norm_le ((proposition71_gamma_omega_integrable hD).norm.const_mul _).integrableOn
      exact Eventually.of_forall (fun t => proposition71_front_gauss_norm_bound θ hθ hN hB₀ c hc S hS a t)
    _=_ := integral_const_mul _ _

/-- The actual infinite double series is the full dominant integral, with the
Gauss factor divided by the true conductor and each short index divided by n. -/
theorem proposition71_front_gauss_full_integral {D N : ℕ} [NeZero N] (hD : 1<D)
    (θ : DirichletCharacter ℂ N) (c : ℕ → ℂ) (hs : LSeriesSummable c (3/2 : ℂ))
    (S : Finset ℕ) (hS : ∀n∈S, 0<n) (a : ℕ → ℂ) :
    (((1/(2*Real.pi) : ℝ) : ℂ))*(∫t : ℝ, proposition71FrontGaussIntegrand D θ c S a t)=
      (gaussSum θ⁻¹ ZMod.stdAddChar/(N : ℂ))*
        (∑' m, proposition71DeltaOneDoubleTerm D c S a (N : ℝ) m) := by
  have hNp : 0<(N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have he := (proposition71_actual_delta_one_double_series hD c hs S hS a hNp).2.2
  unfold proposition71FrontGaussIntegrand
  rw [integral_const_mul]
  calc
    _=gaussSum θ⁻¹ ZMod.stdAddChar*
        ((((1/(2*Real.pi) : ℝ) : ℂ))*(∫t : ℝ, proposition71FrontDominantIntegrand D c S a (N : ℝ) t)) := by ring
    _=_ := by rw [he]; simp only [Complex.ofReal_natCast]; ring

end ZhangLS.Spec
