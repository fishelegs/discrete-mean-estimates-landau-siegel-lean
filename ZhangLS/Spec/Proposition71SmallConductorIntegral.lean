import ZhangLS.Spec.Proposition71Conductor
import ZhangLS.Spec.Proposition71WeightedHeightTail

/-! # The actual small-conductor prime integral, including both height tails

Only the proved nonprincipal Lemma5.6 is used, after the actual primitive
inducer's conductor and distinction from χ have been proved. No extension
of its original |τ|≤D window is assumed.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Finset
open scoped Classical Topology
set_option maxHeartbeats 2000000

lemma proposition71_actual_prime_sum_continuous {q : ℕ} [NeZero q]
    (D : ℕ) (θ : DirichletCharacter ℂ q) (b : ℝ) :
    Continuous (fun t : ℝ => lemma56PrimeSum D θ (t+b)) := by
  unfold lemma56PrimeSum
  apply continuous_finsetSum
  intro p hp
  apply continuous_const.mul
  have hpp := ((lemma56_mem_paper_primes D p).mp hp).1.pos
  exact Continuous.const_cpow (by fun_prop)
    (Or.inl (Nat.cast_ne_zero.mpr hpp.ne'))

/-- The complete prime sum has the actual prime mass as an unconditional
absolute majorant, including arbitrarily large heights. -/
theorem proposition71_actual_prime_sum_trivial_bound {q : ℕ} [NeZero q]
    (D : ℕ) (θ : DirichletCharacter ℂ q) (t : ℝ) :
    ‖lemma56PrimeSum D θ t‖≤lemma56PrimeMass D := by
  unfold lemma56PrimeSum lemma56PrimeMass
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro p hp
  have hpp : 0<(p : ℝ) := by exact_mod_cast ((lemma56_mem_paper_primes D p).mp hp).1.pos
  rw [norm_mul,←Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos hpp]
  have hn : (1+I*(t : ℂ)).re=1 := by simp
  rw [hn,Real.rpow_one]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (θ.norm_le_one _) hpp.le

/-- The actual primitive inducer admits a complete Cauchy-weighted Mellin
integral bound. The explicit 4/D term is the cost of the two height tails. -/
theorem proposition71_actual_inducer_weighted_prime_integral :
    ∃ C : ℝ, 0<C ∧ ∃ D₀ : ℕ, ∀ {D k : ℕ} [NeZero k]
      (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ k),
      D₀≤D → 1<D → 1≤lemma23PaperL D → NormalizedAssumptionA χ →
      θ≠1 → θ.conductor<D → ∀ b : ℝ, |b|≤(D : ℝ)/2 →
        (∫ t : ℝ, ‖lemma56PrimeSum D θ.primitiveCharacter (t+b)‖/(1+t^2)) ≤
          C*Real.pi*lemma56PrimeMass D*lemma56Decay D+4*lemma56PrimeMass D/(D : ℝ) := by
  obtain ⟨C,hC,D₀,hprime⟩ := proposition71_small_actual_inducer_prime_bound
  refine ⟨C,hC,D₀,?_⟩
  intro D k _ χ θ hDN hD hL hA hθ hr b hb
  letI : NeZero θ.conductor := ⟨θ.conductor_ne_zero⟩
  have hDp : 0<(D : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hD
  have hm := lemma56_prime_mass_nonneg D
  have hsmall : 0≤C*lemma56PrimeMass D*lemma56Decay D :=
    mul_nonneg (mul_nonneg hC.le hm) (lemma56_decay_pos D).le
  have hh := proposition71_cauchy_window_and_tail
    (fun t : ℝ => lemma56PrimeSum D θ.primitiveCharacter (t+b))
    (proposition71_actual_prime_sum_continuous D θ.primitiveCharacter b)
    hm hsmall (show 0<(D : ℝ)/2 by positivity)
    (fun t => proposition71_actual_prime_sum_trivial_bound D θ.primitiveCharacter (t+b))
    (fun t ht => hprime χ θ hDN hD hL hA hθ hr (t+b)
      ((abs_add_le t b).trans (by linarith)))
  convert hh using 1 <;> ring

/-- The proved exponential decay is smaller than D⁻¹ already for ℒ≥1. -/
lemma proposition71_decay_le_inverse_modulus {D : ℕ} (hD : 0<D)
    (hL : 1≤lemma23PaperL D) : lemma56Decay D≤(D : ℝ)⁻¹ := by
  have hp : lemma23PaperL D≤lemma23PaperL D^(9/2 : ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hL
      (by norm_num : (1:ℝ)≤9/2)
  have hh := Real.exp_le_exp.mpr (neg_le_neg hp)
  simpa [lemma56Decay,Real.exp_neg,lemma23PaperL,Real.exp_log (by exact_mod_cast hD : 0<(D : ℝ))] using hh

/-- A genuine O(primeMass/D) individual-conductor bound. This still has to be
summed with the original conductor/totient weights; no such aggregate is assumed. -/
theorem proposition71_actual_inducer_weighted_prime_integral_inverse_D :
    ∃ C : ℝ, 0<C ∧ ∃ D₀ : ℕ, ∀ {D k : ℕ} [NeZero k]
      (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ k),
      D₀≤D → 1<D → 1≤lemma23PaperL D → NormalizedAssumptionA χ →
      θ≠1 → θ.conductor<D → ∀ b : ℝ, |b|≤(D : ℝ)/2 →
        (∫ t : ℝ, ‖lemma56PrimeSum D θ.primitiveCharacter (t+b)‖/(1+t^2)) ≤
          C*lemma56PrimeMass D/(D : ℝ) := by
  obtain ⟨C,hC,D₀,hbound⟩ := proposition71_actual_inducer_weighted_prime_integral
  refine ⟨C*Real.pi+4,by positivity,D₀,?_⟩
  intro D k _ χ θ hDN hD hL hA hθ hr b hb
  apply (hbound χ θ hDN hD hL hA hθ hr b hb).trans
  have hm := lemma56_prime_mass_nonneg D
  have hd := proposition71_decay_le_inverse_modulus (by omega) hL
  have hh := mul_le_mul_of_nonneg_left hd (by positivity : 0≤C*Real.pi*lemma56PrimeMass D)
  simp only [div_eq_mul_inv]
  nlinarith only [hh]

end ZhangLS.Spec
