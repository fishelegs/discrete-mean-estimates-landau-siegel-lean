import ZhangLS.Spec.Proposition71SmallConductorKernel
import ZhangLS.Spec.Proposition71ConductorWeights
import ZhangLS.Spec.Proposition71CoefficientEnergy

/-! # The actual truncated Section 7 σ at small conductor

The p sum, actual κ*a coefficients, character values and coprime l support
are retained. The l>P² tail is a separate, still outstanding analytic step.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 3000000

noncomputable def proposition71SigmaTruncated {r : ℕ}
    (D : ℕ) (c b : ℝ) (a : ℕ → ℂ) (h d : ℕ) (θ : DirichletCharacter ℂ r) : ℂ :=
  ∑ l∈(Icc 1 ⌊lemma23PaperP D^2⌋₊).filter (fun l => l.Coprime h),
    (lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a) (d*l)*θ (l : ZMod r)*
      ∑ p∈lemma56PaperPrimes D, (p : ℂ)^(I*(b : ℂ))*θ⁻¹ (p : ZMod r)*
        lemma53PaperDelta D ((l : ℝ)/((p : ℝ)*(h : ℝ)*(r : ℝ)))

/-- Uniform small-conductor bound for the actual truncated σ. Every arithmetic
factor and the complete-height 1/D cost are explicit. -/
theorem proposition71_actual_small_sigma_bound :
    ∃ C : ℝ, 0<C ∧ ∃ D₀ : ℕ, ∀ {D r : ℕ} [NeZero r]
      (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ r),
      D₀≤D → 1<D → 2000≤lemma23PaperL D → NormalizedAssumptionA χ →
      θ.IsPrimitive → 1<r → r<D → ∀ c b B : ℝ, 0≤B →
        |b|≤(D : ℝ)/2 → ∀ a : ℕ → ℂ, (∀n, ‖a n‖≤B) →
          ∀ h d : ℕ, 0<h → 0<d →
            ‖proposition71SigmaTruncated D c b a h d θ‖≤
              C*B*(lemma34Tau 5 d : ℝ)*(h : ℝ)*(r : ℝ)*
                lemma56PrimeMass D/(D : ℝ)*lemma23PaperL D^3245 := by
  obtain ⟨C,hC,D₀,hkernel⟩ := proposition71_small_primitive_delta_sum
  refine ⟨C*3^5,by positivity,D₀,?_⟩
  intro D r _ χ θ hDN hD hL hA hθ hr1 hrD c b B hB hb a ha h d hh hd
  have hθi : θ⁻¹.IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def,DirichletCharacter.conductor_inv]
    exact hθ
  have hDp : 0<(D : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hD
  have hhp : 0<(h : ℝ) := by exact_mod_cast hh
  have hrp : 0<(r : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hr1
  have hLp : 0≤lemma23PaperL D := by linarith
  have hM := lemma56_prime_mass_nonneg D
  let K : ℝ := C*B*(lemma34Tau 5 d : ℝ)*(h : ℝ)*(r : ℝ)*lemma56PrimeMass D/(D : ℝ)*lemma23PaperL D^3200
  have hK : 0≤K := by dsimp [K]; positivity
  have hterm (l : ℕ) (hl : l∈(Icc 1 ⌊lemma23PaperP D^2⌋₊).filter (fun l => l.Coprime h)) :
      ‖(lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a) (d*l)*θ (l : ZMod r)*
        (∑ p∈lemma56PaperPrimes D, (p : ℂ)^(I*(b : ℂ))*θ⁻¹ (p : ZMod r)*
          lemma53PaperDelta D ((l : ℝ)/((p : ℝ)*(h : ℝ)*(r : ℝ))))‖≤
            K*((lemma34Tau 5 l : ℝ)/(l : ℝ)) := by
    have hlp : 0<(l : ℝ) := by exact_mod_cast (mem_Icc.mp (mem_filter.mp hl).1).1
    have hk := hkernel χ θ⁻¹ hDN hD hL hA hθi hr1 hrD b (h : ℝ) (l : ℝ) hb hhp hlp
    have hc₀ := proposition71_actual_convolution_le_tau_five (lemma83PaperBeta D c)
      (lemma83_beta_re D c) hB a ha (d*l)
    have hτ : (lemma34Tau 5 (d*l) : ℝ)≤(lemma34Tau 5 d : ℝ)*(lemma34Tau 5 l : ℝ) := by
      exact_mod_cast proposition71_tau_submultiplicative 5 d l
    have hc : ‖(lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a) (d*l)‖≤
        B*((lemma34Tau 5 d : ℝ)*(lemma34Tau 5 l : ℝ)) := hc₀.trans (mul_le_mul_of_nonneg_left hτ hB)
    rw [norm_mul,norm_mul]
    calc
      _≤(B*((lemma34Tau 5 d : ℝ)*(lemma34Tau 5 l : ℝ)))*1*
          (C*lemma23PaperL D^3200*((h : ℝ)*(r : ℝ)/(l : ℝ))*lemma56PrimeMass D/(D : ℝ)) := by
        gcongr
        exact θ.norm_le_one _
      _=_ := by dsimp [K]; ring
  have hP1 : 1≤lemma23PaperP D := by
    apply Real.one_le_exp_iff.mpr
    exact pow_nonneg hLp 9
  have hX : 1≤⌊lemma23PaperP D^2⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using one_le_pow₀ (n := 2) hP1)
  have hlog : Real.log (⌊lemma23PaperP D^2⌋₊ : ℝ)≤2*lemma23PaperL D^9 := by
    have hh' := Real.log_le_log (by exact_mod_cast hX : (0:ℝ)<⌊lemma23PaperP D^2⌋₊)
      (Nat.floor_le (sq_nonneg (lemma23PaperP D)))
    simpa [Real.log_pow,lemma23PaperP] using hh'
  have hlog0 : 0≤1+Real.log (⌊lemma23PaperP D^2⌋₊ : ℝ) := by
    have := Real.log_nonneg (by exact_mod_cast hX : (1:ℝ)≤⌊lemma23PaperP D^2⌋₊)
    linarith
  have hpower : (1+Real.log (⌊lemma23PaperP D^2⌋₊ : ℝ))^5≤3^5*lemma23PaperL D^45 := by
    have hp9 : 1≤lemma23PaperL D^9 := one_le_pow₀ (by linarith)
    have hh' := pow_le_pow_left₀ hlog0 (show 1+Real.log (⌊lemma23PaperP D^2⌋₊ : ℝ)≤3*lemma23PaperL D^9 by linarith) 5
    simpa only [mul_pow,←pow_mul] using hh'
  unfold proposition71SigmaTruncated
  calc
    _≤∑ l∈(Icc 1 ⌊lemma23PaperP D^2⌋₊).filter (fun l => l.Coprime h),
        K*((lemma34Tau 5 l : ℝ)/(l : ℝ)) := (norm_sum_le _ _).trans (sum_le_sum hterm)
    _≤∑ l∈Icc 1 ⌊lemma23PaperP D^2⌋₊, K*((lemma34Tau 5 l : ℝ)/(l : ℝ)) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
    _=K*∑ l∈Icc 1 ⌊lemma23PaperP D^2⌋₊, (lemma34Tau 5 l : ℝ)/(l : ℝ) := by rw [mul_sum]
    _≤K*(1+Real.log (⌊lemma23PaperP D^2⌋₊ : ℝ))^5 :=
      mul_le_mul_of_nonneg_left (proposition71_tau_harmonic_bound 5 _ hX) hK
    _≤K*(3^5*lemma23PaperL D^45) := mul_le_mul_of_nonneg_left hpower hK
    _=_ := by dsimp [K]; ring

end ZhangLS.Spec
