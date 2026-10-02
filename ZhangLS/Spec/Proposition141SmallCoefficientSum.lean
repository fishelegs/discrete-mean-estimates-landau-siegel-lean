import ZhangLS.Spec.Proposition141SmallKernel
import ZhangLS.Spec.Proposition141Objects
import ZhangLS.Spec.Proposition71DivisorWeights

/-! # The finite l-sum at small conductor, retaining all divisor factors

The arbitrary Section14 κ* is not identified with the Section7 convolution.
Its τ₅ bound is combined with genuine submultiplicativity, and the original
D₁,d factors remain explicit before the outer sums.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical ComplexConjugate

/-- The coefficient at D₁*d*l retains BOTH outer divisor factors. -/
theorem proposition141_kappa_three_factor_bound {B : ℝ} (hB : 0≤B)
    {κ : ℕ → ℂ} (hκ : Proposition141KappaBound B κ)
    {D₁ d l : ℕ} (hD₁ : 0<D₁) (hd : 0<d) (hl : 0<l) :
    ‖κ (D₁*d*l)‖ ≤ B*(lemma34Tau 5 D₁:ℝ)*(lemma34Tau 5 d:ℝ)*(lemma34Tau 5 l:ℝ) := by
  have h1 := proposition71_tau_submultiplicative 5 (D₁*d) l
  have h2 := proposition71_tau_submultiplicative 5 D₁ d
  have h3 : lemma34Tau 5 (D₁*d*l) ≤ lemma34Tau 5 D₁*lemma34Tau 5 d*lemma34Tau 5 l :=
    h1.trans (Nat.mul_le_mul_right _ h2)
  have hh := mul_le_mul_of_nonneg_left (by exact_mod_cast h3 :
    (lemma34Tau 5 (D₁*d*l):ℝ) ≤ (lemma34Tau 5 D₁:ℝ)*(lemma34Tau 5 d:ℝ)*(lemma34Tau 5 l:ℝ)) hB
  exact (hκ _ (Nat.mul_pos (Nat.mul_pos hD₁ hd) hl)).trans (by simpa only [mul_assoc] using hh)

/-- Actual κ* harmonic sum over any filtered positive finite interval. -/
theorem proposition141_kappa_finite_harmonic_bound {B : ℝ} (hB : 0≤B)
    {κ : ℕ → ℂ} (hκ : Proposition141KappaBound B κ) {D₁ d X : ℕ}
    (hD₁ : 0<D₁) (hd : 0<d) (hX : 1≤X) (S : Finset ℕ) (hS : S⊆Icc 1 X) :
    (∑ l ∈ S, ‖κ (D₁*d*l)‖/(l:ℝ)) ≤
      B*(lemma34Tau 5 D₁:ℝ)*(lemma34Tau 5 d:ℝ)*(1+Real.log (X:ℝ))^5 := by
  have hH : 0≤(harmonic X:ℝ) := by
    simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
    exact sum_nonneg (fun _ _ => by positivity)
  have ht : (∑ l ∈ Icc 1 X, (lemma34Tau 5 l:ℝ)/(l:ℝ))≤(1+Real.log (X:ℝ))^5 := by
    simpa only [div_eq_mul_inv] using
      (lemma34_tau_weighted_sum_le_harmonic_pow 5 X hX).trans
        (pow_le_pow_left₀ hH (harmonic_le_one_add_log X) 5)
  have hcoef : 0≤B*(lemma34Tau 5 D₁:ℝ)*(lemma34Tau 5 d:ℝ) := by positivity
  calc
    _ ≤ ∑ l ∈ S, (B*(lemma34Tau 5 D₁:ℝ)*(lemma34Tau 5 d:ℝ))*
        ((lemma34Tau 5 l:ℝ)/(l:ℝ)) := by
      apply sum_le_sum
      intro l hl
      have hlpos := (mem_Icc.mp (hS hl)).1
      have hh := div_le_div_of_nonneg_right
        (proposition141_kappa_three_factor_bound hB hκ hD₁ hd hlpos) (Nat.cast_nonneg l)
      simpa only [mul_div_assoc] using hh
    _ = (B*(lemma34Tau 5 D₁:ℝ)*(lemma34Tau 5 d:ℝ))*
        ∑ l ∈ S, (lemma34Tau 5 l:ℝ)/(l:ℝ) := by rw [mul_sum]
    _ ≤ (B*(lemma34Tau 5 D₁:ℝ)*(lemma34Tau 5 d:ℝ))*
        ∑ l ∈ Icc 1 X, (lemma34Tau 5 l:ℝ)/(l:ℝ) := by
      apply mul_le_mul_of_nonneg_left _ hcoef
      exact sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left ht hcoef

/-- The finite inner sum obtained in (14.8), before its l-tail is removed. -/
noncomputable def proposition141FiniteSmallCharacterSum {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ N) (β : ℂ)
    (κ : ℕ → ℂ) (D₁ d : ℕ) (h r : ℝ) (S : Finset ℕ) : ℂ :=
  ∑ l ∈ S, κ (D₁*d*l)*θ (l:ZMod N)*
    proposition141ActualShiftedPrimeKernel χ θ β h r l

/-- Small-conductor finite coefficient estimate. All τ₅(D₁),τ₅(d),h,r,
coefficient and logarithmic factors are retained; no outer sum is assumed. -/
theorem proposition141_uniform_finite_small_character_sum_bound :
    ∃ C : ℝ, 0<C ∧ ∃ D₀ : ℕ, 2≤D₀ ∧
      ∀ {D N : ℕ} [NeZero N] (χ : RealPrimitiveCharacter D)
      (hDN : D∣N) (θ : DirichletCharacter ℂ N),
      D₀≤D → NormalizedAssumptionA χ → (N:ℝ)≤lemma23PaperP D →
      θ≠1 → θ≠χ.chi.changeLevel hDN → θ.conductor<D^3 →
      ∀ β : ℂ, ‖β‖<5*lemma44PaperAlpha D → ∀ B : ℝ, 0≤B →
      ∀ κ : ℕ → ℂ, Proposition141KappaBound B κ →
      ∀ D₁ d X : ℕ, 0<D₁ → 0<d → 1≤X → ∀ h r : ℝ, 0<h → 0<r →
      ∀ S : Finset ℕ, S⊆Icc 1 X →
        ‖proposition141FiniteSmallCharacterSum χ θ β κ D₁ d h r S‖ ≤
          C*B*(lemma34Tau 5 D₁:ℝ)*(lemma34Tau 5 d:ℝ)*lemma23PaperL D^7200*
            (h*r)*lemma56PrimeMass D*(lemma56Decay D+(D:ℝ)^(-(7:ℤ)))*(1+Real.log (X:ℝ))^5 := by
  obtain ⟨C,hC,D₀,hD₀,hbound⟩ := proposition141_uniform_small_shifted_prime_kernel_bound
  refine ⟨C,hC,D₀,hD₀,?_⟩
  intro D N _ χ hDN θ hlarge hA hNP hθ hne hcond β hβ B hB κ hκ D₁ d X hD₁ hd hX h r hh hr S hS
  let K := C*lemma23PaperL D^7200*(h*r)*lemma56PrimeMass D*(lemma56Decay D+(D:ℝ)^(-(7:ℤ)))
  have hM := lemma56_prime_mass_nonneg D
  have hdec := (lemma56_decay_pos D).le
  have hK : 0≤K := by dsimp [K]; positivity
  have hpoint (l : ℕ) (hl : l∈S) :
      ‖κ (D₁*d*l)*θ (l:ZMod N)*proposition141ActualShiftedPrimeKernel χ θ β h r l‖ ≤
        K*(‖κ (D₁*d*l)‖/(l:ℝ)) := by
    have hlpos := (mem_Icc.mp (hS hl)).1
    have hb := hbound χ hDN θ hlarge hA hNP hθ hne hcond β hβ h r l hh hr
      (by exact_mod_cast hlpos)
    have hbe : ‖proposition141ActualShiftedPrimeKernel χ θ β h r l‖≤K/(l:ℝ) := by
      convert hb using 1 <;> dsimp [K] <;> ring
    have hchar : ‖κ (D₁*d*l)*θ (l:ZMod N)‖≤‖κ (D₁*d*l)‖ := by
      rw [norm_mul]
      simpa using mul_le_mul_of_nonneg_left (θ.norm_le_one _) (norm_nonneg _)
    rw [norm_mul]
    have hh' := mul_le_mul hchar hbe (norm_nonneg _) (norm_nonneg _)
    convert hh' using 1 <;> ring
  have hf := proposition141_kappa_finite_harmonic_bound hB hκ hD₁ hd hX S hS
  calc
    _ ≤ ∑ l ∈ S, K*(‖κ (D₁*d*l)‖/(l:ℝ)) :=
      (norm_sum_le _ _).trans (sum_le_sum hpoint)
    _ = K*∑ l ∈ S, ‖κ (D₁*d*l)‖/(l:ℝ) := by rw [mul_sum]
    _ ≤ K*(B*(lemma34Tau 5 D₁:ℝ)*(lemma34Tau 5 d:ℝ)*(1+Real.log (X:ℝ))^5) :=
      mul_le_mul_of_nonneg_left hf hK
    _ = _ := by dsimp [K]; ring

end ZhangLS.Spec
