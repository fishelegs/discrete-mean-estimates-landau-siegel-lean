import ZhangLS.Spec.Proposition141OffDiagonalKernel
import ZhangLS.Spec.Proposition141SmallCoefficientSum

/-! # The actual off-diagonal finite κ* sum

The χ-induced term is impossible because D does not divide the true modulus.
The product character and all-height Mellin bounds are those already proved,
not a hypothetical full form of Lemma5.6 at conductor one.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical ComplexConjugate

/-- Small-conductor finite coefficient estimate. All τ₅(D₁),τ₅(d),h,r,
coefficient and logarithmic factors are retained; no outer sum is assumed. -/
theorem proposition141_uniform_off_diagonal_finite_sum_bound :
    ∃ C : ℝ, 0<C ∧ ∃ D₀ : ℕ, 2≤D₀ ∧
      ∀ {D N : ℕ} [NeZero N] (χ : RealPrimitiveCharacter D)
      (θ : DirichletCharacter ℂ N),
      D₀≤D → NormalizedAssumptionA χ → ((D*N:ℕ):ℝ)≤lemma23PaperP D →
      ¬D∣N → θ≠1 → θ.conductor<D^3 →
      ∀ β : ℂ, ‖β‖<5*lemma44PaperAlpha D → ∀ B : ℝ, 0≤B →
      ∀ κ : ℕ → ℂ, Proposition141KappaBound B κ →
      ∀ D₁ d X : ℕ, 0<D₁ → 0<d → 1≤X → ∀ h r : ℝ, 0<h → 0<r →
      ∀ S : Finset ℕ, S⊆Icc 1 X →
        ‖proposition141FiniteSmallCharacterSum χ θ β κ D₁ d h r S‖ ≤
          C*B*(lemma34Tau 5 D₁:ℝ)*(lemma34Tau 5 d:ℝ)*lemma23PaperL D^7200*
            (h*r)*lemma56PrimeMass D*(lemma56Decay D+(D:ℝ)^(-(7:ℤ)))*(1+Real.log (X:ℝ))^5 := by
  obtain ⟨C,hC,D₀,hD₀,hbound⟩ := proposition141_uniform_off_diagonal_small_kernel_bound
  refine ⟨C,hC,D₀,hD₀,?_⟩
  intro D N _ χ θ hlarge hA hNP hne hθ hcond β hβ B hB κ hκ D₁ d X hD₁ hd hX h r hh hr S hS
  let K := C*lemma23PaperL D^7200*(h*r)*lemma56PrimeMass D*(lemma56Decay D+(D:ℝ)^(-(7:ℤ)))
  have hM := lemma56_prime_mass_nonneg D
  have hdec := (lemma56_decay_pos D).le
  have hK : 0≤K := by dsimp [K]; positivity
  have hpoint (l : ℕ) (hl : l∈S) :
      ‖κ (D₁*d*l)*θ (l:ZMod N)*proposition141ActualShiftedPrimeKernel χ θ β h r l‖ ≤
        K*(‖κ (D₁*d*l)‖/(l:ℝ)) := by
    have hlpos := (mem_Icc.mp (hS hl)).1
    have hb := hbound χ θ hlarge hA hNP hne hθ hcond β hβ h r l hh hr
      (by exact_mod_cast hlpos)
    have hbe : ‖proposition141ActualShiftedPrimeKernel χ θ β h r l‖≤K/(l:ℝ) := by
      convert hb using 1; dsimp [K]; ring
    have hchar : ‖κ (D₁*d*l)*θ (l:ZMod N)‖≤‖κ (D₁*d*l)‖ := by
      rw [norm_mul]
      simpa using mul_le_mul_of_nonneg_left (θ.norm_le_one _) (norm_nonneg _)
    rw [norm_mul]
    have hh' := mul_le_mul hchar hbe (norm_nonneg _) (norm_nonneg _)
    convert hh' using 1; ring
  have hf := proposition141_kappa_finite_harmonic_bound hB hκ hD₁ hd hX S hS
  calc
    _ ≤ ∑ l ∈ S, K*(‖κ (D₁*d*l)‖/(l:ℝ)) :=
      (norm_sum_le _ _).trans (sum_le_sum hpoint)
    _ = K*∑ l ∈ S, ‖κ (D₁*d*l)‖/(l:ℝ) := by rw [mul_sum]
    _ ≤ K*(B*(lemma34Tau 5 D₁:ℝ)*(lemma34Tau 5 d:ℝ)*(1+Real.log (X:ℝ))^5) :=
      mul_le_mul_of_nonneg_left hf hK
    _ = _ := by dsimp [K]; ring

end ZhangLS.Spec
