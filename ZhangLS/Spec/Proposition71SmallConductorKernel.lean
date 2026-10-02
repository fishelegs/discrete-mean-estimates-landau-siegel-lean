import ZhangLS.Spec.Proposition71SmallConductorIntegral
import ZhangLS.Spec.Proposition71MellinPrimeBound

/-! # Actual small-conductor Δ sum, with the entire Mellin-height tail retained -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Finset
open scoped Classical
set_option maxHeartbeats 2000000

/-- A primitive small modulus is automatically distinct from χ. The hypotheses
are the true primitive/nonprincipal conductor conditions, not an assumed sum bound. -/
theorem proposition71_small_primitive_weighted_integral :
    ∃ C : ℝ, 0<C ∧ ∃ D₀ : ℕ, ∀ {D r : ℕ} [NeZero r]
      (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ r),
      D₀≤D → 1<D → 1≤lemma23PaperL D → NormalizedAssumptionA χ →
      θ.IsPrimitive → 1<r → r<D → ∀ b : ℝ, |b|≤(D : ℝ)/2 →
        (∫ t : ℝ, ‖lemma56PrimeSum D θ (t+b)‖/(1+t^2))≤
          C*lemma56PrimeMass D/(D : ℝ) := by
  obtain ⟨C,hC,D₀,hprime⟩ := lemma56_uniform_primitive_prime_window_normalized_bound
  refine ⟨C*Real.pi+4,by positivity,D₀,?_⟩
  intro D r _ χ θ hDN hD hL hA hθ hr1 hrD b hb
  have hDp : 0<(D : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hD
  have hm := lemma56_prime_mass_nonneg D
  have hsmall : 0≤C*lemma56PrimeMass D*lemma56Decay D :=
    mul_nonneg (mul_nonneg hC.le hm) (lemma56_decay_pos D).le
  have hh := proposition71_cauchy_window_and_tail
    (fun t : ℝ => lemma56PrimeSum D θ (t+b))
    (proposition71_actual_prime_sum_continuous D θ b)
    hm hsmall (show 0<(D : ℝ)/2 by positivity)
    (fun t => proposition71_actual_prime_sum_trivial_bound D θ (t+b))
    (fun t ht => hprime χ θ hDN hD hA hθ hr1
      (proposition71_small_conductor_lt_T (by omega) hL hrD)
      (proposition71_small_primitive_distinct χ θ hθ hrD) (t+b)
      ((abs_add_le t b).trans (by linarith)))
  have hd := proposition71_decay_le_inverse_modulus (by omega) hL
  have hmul := mul_le_mul_of_nonneg_left hd
    (by positivity : 0≤C*lemma56PrimeMass D*Real.pi)
  apply hh.trans
  rw [show 2*lemma56PrimeMass D/((D : ℝ)/2)=4*lemma56PrimeMass D/(D : ℝ) by field_simp; ring]
  simp only [div_eq_mul_inv]
  nlinarith only [hmul]

/-- Exact conversion of the imaginary β weight to the shifted prime frequency. -/
lemma proposition71_prime_shift_polynomial {q : ℕ} (D : ℕ)
    (θ : DirichletCharacter ℂ q) (b t : ℝ) :
    (∑ p∈lemma56PaperPrimes D,
      ((p : ℂ)^(I*(b : ℂ))*θ (p : ZMod q))*(p : ℂ)^((1 : ℂ)+(t : ℂ)*I))=
        lemma56PrimeSum D θ (t+b) := by
  unfold lemma56PrimeSum
  apply sum_congr rfl
  intro p hp
  have hp0 : (p : ℂ)≠0 := Nat.cast_ne_zero.mpr
    ((lemma56_mem_paper_primes D p).mp hp).1.ne_zero
  calc
    _=θ (p : ZMod q)*((p : ℂ)^(I*(b : ℂ))*(p : ℂ)^((1 : ℂ)+(t : ℂ)*I)) := by ring
    _=θ (p : ZMod q)*(p : ℂ)^((I*(b : ℂ))+((1 : ℂ)+(t : ℂ)*I)) := by rw [←Complex.cpow_add _ _ hp0]
    _=_ := by congr 2; push_cast; ring

/-- Actual Δ-weighted prime sum for a primitive conductor r<D, with every
Mellin height included. The ℒ^3200 loss is explicit for outer summation. -/
theorem proposition71_small_primitive_delta_sum :
    ∃ C : ℝ, 0<C ∧ ∃ D₀ : ℕ, ∀ {D r : ℕ} [NeZero r]
      (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ r),
      D₀≤D → 1<D → 2000≤lemma23PaperL D → NormalizedAssumptionA χ →
      θ.IsPrimitive → 1<r → r<D → ∀ b h l : ℝ,
        |b|≤(D : ℝ)/2 → 0<h → 0<l →
        ‖∑ p∈lemma56PaperPrimes D, (p : ℂ)^(I*(b : ℂ))*θ (p : ZMod r)*
          lemma53PaperDelta D (l/((p : ℝ)*h*(r : ℝ)))‖≤
            C*lemma23PaperL D^3200*(h*(r : ℝ)/l)*lemma56PrimeMass D/(D : ℝ) := by
  obtain ⟨C,hC,D₀,hprime⟩ := proposition71_small_primitive_weighted_integral
  have hCM := lemma54_mellin_strip_constant_pos
  refine ⟨(lemma54MellinStripConstant/(2*Real.pi))*C,by positivity,D₀,?_⟩
  intro D r _ χ θ hDN hD hL hA hθ hr1 hrD b h l hb hh hl
  have hrp : 0<(r : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hr1
  have hbound := proposition71_actual_mellin_prime_bound hD hL hh hrp hl
    (lemma56PaperPrimes D) (fun p hp => ((lemma56_mem_paper_primes D p).mp hp).1.pos)
    (fun p => (p : ℂ)^(I*(b : ℂ))*θ (p : ZMod r))
  simp_rw [proposition71_prime_shift_polynomial] at hbound
  have hpr := hprime χ θ hDN hD (by linarith) hA hθ hr1 hrD b hb
  apply hbound.trans
  have hfactor : 0≤(lemma54MellinStripConstant/(2*Real.pi))*lemma23PaperL D^3200*(h*(r : ℝ)/l) := by
    positivity
  have hh' := mul_le_mul_of_nonneg_left hpr hfactor
  convert hh' using 1 <;> ring

end ZhangLS.Spec
