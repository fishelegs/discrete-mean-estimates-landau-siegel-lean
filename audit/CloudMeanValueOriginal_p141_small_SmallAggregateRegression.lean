import ZhangLS.Spec.Proposition141SmallConductorAggregate
set_option autoImplicit false
open ZhangLS.Spec Finset
open scoped Classical
example {D r:ℕ} (χ:RealPrimitiveCharacter D) (θ:DirichletCharacter ℂ r)
    (β:ℂ) (κ:ℕ→ℂ) (D₁ d h:ℕ) (S:Finset ℕ) :
    proposition141PrimitiveFiniteCharacterSum χ θ β κ D₁ d h S =
    ∑l∈S.filter (fun l=>l.Coprime h),κ (D₁*d*l)*θ (l:ZMod r)*
      proposition141ActualShiftedPrimeKernel χ θ β h r l := rfl
example {D:ℕ} (χ:RealPrimitiveCharacter D) (h r:ℕ) :
    proposition141SmallPrimitiveFamily χ h r =
      univ.filter (fun θ:DirichletCharacter ℂ r=>θ.IsPrimitive ∧ ∀hDN:D∣r*h,
        θ.changeLevel (r.dvd_mul_right h)≠χ.chi.changeLevel hDN) := rfl
example (D h:ℕ) : proposition141SmallSupportedModuli D h =
    ((Icc 1 (D^3)).filter (fun r=>1<r ∧ r<D^3 ∧ D∣h*r)).filter
      (fun r=>((r*h:ℕ):ℝ)≤lemma23PaperP D) := rfl
#print axioms ZhangLS.Spec.proposition141PrimitiveFiniteCharacterSum
#print axioms ZhangLS.Spec.proposition141_prime_coprime_extra_factor
#print axioms ZhangLS.Spec.proposition141_primitive_lifted_finite_sum
#print axioms ZhangLS.Spec.proposition141_primitive_lift_nonprincipal
#print axioms ZhangLS.Spec.proposition141_uniform_primitive_small_character_sum_bound
#print axioms ZhangLS.Spec.proposition141_primitive_subfamily_card
#print axioms ZhangLS.Spec.proposition141_counted_row_scalar
#print axioms ZhangLS.Spec.proposition141_uniform_small_conductor_row_bound
#print axioms ZhangLS.Spec.proposition141SmallSupportedModuli
#print axioms ZhangLS.Spec.proposition141SmallPrimitiveFamily
#print axioms ZhangLS.Spec.proposition141_small_supported_mem
#print axioms ZhangLS.Spec.proposition141FiniteSmallConductorAggregate
#print axioms ZhangLS.Spec.proposition141_small_supported_weight_sum
#print axioms ZhangLS.Spec.proposition141_uniform_finite_small_conductor_aggregate
