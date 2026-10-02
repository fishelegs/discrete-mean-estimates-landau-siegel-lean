import ZhangLS.Spec.Proposition71FrontSegment

/-! # The actual original J(1) to Δ₁ transformation

The interval is exactly the paper's center ±L^405. The true reciprocal-Z
factor is transformed into the infinite-long/finite-short Δ₁ series, with an
explicit Gaussian error and no hypothesis asserting the desired transform.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Classical
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

noncomputable def proposition71FrontSegmentIntegral {N : ℕ} [NeZero N] (D : ℕ)
    (θ : DirichletCharacter ℂ N) (c : ℕ → ℂ) (S : Finset ℕ) (a : ℕ → ℂ) : ℂ :=
  (((1/(2*Real.pi) : ℝ) : ℂ)) *
    (∫u in -(lemma23PaperL D^405)..lemma23PaperL D^405,
      proposition71FrontActualIntegrand D θ c S a (u+(lemma23PaperCenter D).im))

lemma proposition71_original_front_lower_height {D : ℕ} (hL : 3≤lemma23PaperL D) :
    0<lemma23PaperL D^519 ∧
      lemma23PaperL D^519≤(lemma23PaperCenter D).im-lemma23PaperL D^405 := by
  have hL1 : 1≤lemma23PaperL D := by linarith
  have hLp : 0<lemma23PaperL D := by linarith
  have hH : lemma23PaperL D^405≤lemma23PaperL D^519 :=
    pow_le_pow_right₀ hL1 (by norm_num)
  have hT : 0<lemma23PaperL D^519 := pow_pos hLp _
  refine ⟨hT,?_⟩
  change lemma23PaperL D^519≤2*Real.pi*lemma23PaperL D^519-lemma23PaperL D^405
  nlinarith only [hH,hT,Real.pi_gt_three]

lemma proposition71_original_front_parity_decay {D : ℕ} (hL : 3≤lemma23PaperL D) :
    Real.exp (-Real.pi*((lemma23PaperCenter D).im-lemma23PaperL D^405))≤
      Real.exp (-lemma23PaperL D^10/8) := by
  have hT := proposition71_original_front_lower_height hL
  have hpow : lemma23PaperL D^10≤lemma23PaperL D^519 :=
    pow_le_pow_right₀ (by linarith : 1≤lemma23PaperL D) (by norm_num)
  apply Real.exp_le_exp.mpr
  nlinarith only [hT.1,hT.2,hpow,Real.pi_gt_three]

lemma proposition71_original_front_exterior_gap {D : ℕ} (t : ℝ)
    (ht : t∈(Ioc ((lemma23PaperCenter D).im-lemma23PaperL D^405)
      ((lemma23PaperCenter D).im+lemma23PaperL D^405))ᶜ) :
    lemma23PaperL D^405≤|t-(lemma23PaperCenter D).im| := by
  simp only [mem_compl_iff,mem_Ioc,not_and_or,not_lt,not_le] at ht
  rcases ht with h|h
  · exact le_abs.mpr (Or.inr (by linarith))
  · exact le_abs.mpr (Or.inl (by linarith))

/-- A fully quantitative actual-object version of the shared analytic front end.
The short polynomial may be any finite positive-index polynomial; its exact
weighted coefficient mass is retained. -/
theorem proposition71_original_front_transform {D N : ℕ} [NeZero N] (hD : 1<D)
    (hL : 3≤lemma23PaperL D) (θ : DirichletCharacter ℂ N)
    (hθ : θ.IsPrimitive) (hN : N≠1) {B : ℝ} (hB : 0≤B)
    (c : ℕ → ℂ) (hc : ∀n, 0<n → ‖c n‖≤B*(lemma34Tau 5 n : ℝ))
    (S : Finset ℕ) (hS : ∀n∈S, 0<n) (a : ℕ → ℂ) :
    Summable (proposition71DeltaOneDoubleTerm D c S a (N : ℝ)) ∧
      ‖proposition71FrontSegmentIntegral D θ c S a-
        (gaussSum θ⁻¹ ZMod.stdAddChar/(N : ℂ))*
          (∑' m, proposition71DeltaOneDoubleTerm D c S a (N : ℝ) m)‖≤
      (128*Real.exp 1)*(1+(lemma23PaperCenter D).im^2)*(1+32*lemma53PaperScale D^2)*
        ((N : ℝ)*B*proposition71TauFiveThreeHalvesMass*proposition71ShortCoefficientMass S a)*
        Real.exp (-lemma23PaperL D^10/8) := by
  let A := (lemma23PaperCenter D).im-lemma23PaperL D^405
  let Z := (lemma23PaperCenter D).im+lemma23PaperL D^405
  let K := (N : ℝ)*B*proposition71TauFiveThreeHalvesMass*proposition71ShortCoefficientMass S a
  let M := (128*Real.pi*Real.exp 1)*(1+(lemma23PaperCenter D).im^2)*(1+32*lemma53PaperScale D^2)
  let E := Real.exp (-lemma23PaperL D^10/8)
  have hK : 0≤K := by
    dsimp [K]
    exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg N) hB)
      proposition71_tau_three_halves_mass_pos.le) (proposition71_short_coefficient_mass_nonneg S a)
  have hM : 0≤M := by dsimp [M]; positivity
  have hE : 0≤E := (Real.exp_pos _).le
  have hA : 0<A := (proposition71_original_front_lower_height hL).1.trans_le
    (proposition71_original_front_lower_height hL).2
  have hAZ : A≤Z := by dsimp [A,Z]; have : 0≤lemma23PaperL D^405 := pow_nonneg (by linarith) _; linarith
  have hs := proposition71_front_coefficient_summable hB c hc (by norm_num : (1 : ℝ)<(3/2 : ℂ).re)
  have hNp : 0<(N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  refine ⟨(proposition71_actual_delta_one_double_series hD c hs S hS a hNp).2.1,?_⟩
  have hm : (∫t : ℝ, ‖proposition71GammaOmegaKernel D t‖)≤M := by
    apply (proposition71_gamma_omega_mass_bound hD hL).trans
    dsimp [M]
    gcongr <;> norm_num
  have hext : (∫t : ℝ in (Ioc A Z)ᶜ, ‖proposition71GammaOmegaKernel D t‖)≤M*E :=
    proposition71_gamma_omega_exterior_bound hD hL measurableSet_Ioc.compl
      (fun t ht => proposition71_original_front_exterior_gap t ht)
  have hp : ‖(∫t in A..Z, proposition71FrontActualIntegrand D θ c S a t)-
      (∫t in A..Z, proposition71FrontGaussIntegrand D θ c S a t)‖≤K*M*E := by
    apply (proposition71_front_parity_segment_bound hD θ hθ hN hB c hc S hS a hA hAZ).trans
    calc
      _≤K*E*M := by
        gcongr
        exact proposition71_original_front_parity_decay hL
      _=_ := by ring
  have ht : ‖(∫t in A..Z, proposition71FrontGaussIntegrand D θ c S a t)-
      (∫t : ℝ, proposition71FrontGaussIntegrand D θ c S a t)‖≤K*M*E := by
    apply (proposition71_front_exterior_bound hD θ hθ hN hB c hc S hS a hAZ).trans
    exact (mul_le_mul_of_nonneg_left hext hK).trans_eq (by ring)
  have htot : ‖(∫t in A..Z, proposition71FrontActualIntegrand D θ c S a t)-
      (∫t : ℝ, proposition71FrontGaussIntegrand D θ c S a t)‖≤2*K*M*E := by
    have htri := dist_triangle (∫t in A..Z, proposition71FrontActualIntegrand D θ c S a t)
      (∫t in A..Z, proposition71FrontGaussIntegrand D θ c S a t)
      (∫t : ℝ, proposition71FrontGaussIntegrand D θ c S a t)
    simp only [dist_eq_norm] at htri
    exact htri.trans ((add_le_add hp ht).trans_eq (by ring))
  rw [←proposition71_front_gauss_full_integral hD θ c hs S hS a]
  unfold proposition71FrontSegmentIntegral
  rw [intervalIntegral.integral_comp_add_right]
  have hleft : -lemma23PaperL D^405+(lemma23PaperCenter D).im=A := by dsimp [A]; ring
  have hright : lemma23PaperL D^405+(lemma23PaperCenter D).im=Z := by dsimp [Z]; ring
  rw [hleft,hright,←mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (by positivity : 0<(1/(2*Real.pi) : ℝ))]
  calc
    _≤(1/(2*Real.pi))*(2*K*M*E) := mul_le_mul_of_nonneg_left htot (by positivity)
    _=_ := by dsimp [K,M,E]; field_simp

end ZhangLS.Spec
