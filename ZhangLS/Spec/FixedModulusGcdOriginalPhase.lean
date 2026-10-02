import ZhangLS.Spec.FixedModulusGcdSourceIndex

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex
open scoped Classical ComplexConjugate

/-- The divisor selected by the equivalence is the actual gcd. -/
theorem fixedDGcd_inverse_divisor (D : ℕ) (l : ℕ+) :
    (((fixedDGcdEquiv D).symm l).1.val:ℕ) = Nat.gcd (l:ℕ) D := by
  rw [← fixedDGcd_lift_gcd]
  exact congrArg (fun n : ℕ+ => Nat.gcd (n:ℕ) D) ((fixedDGcdEquiv D).apply_symm_apply l)

/-- The rescaled positive index is exactly l/gcd(l,D). -/
theorem fixedDGcd_inverse_quotient (D : ℕ) (l : ℕ+) :
    (((fixedDGcdEquiv D).symm l).2.val:ℕ) = (l:ℕ)/Nat.gcd (l:ℕ) D := by
  let i := (fixedDGcdEquiv D).symm l
  have he : fixedDGcdLift i = l := (fixedDGcdEquiv D).apply_symm_apply l
  have hd : (i.1.val:ℕ)=Nat.gcd (l:ℕ) D := fixedDGcd_inverse_divisor D l
  change (i.2.val:ℕ) = _
  rw [← hd, ← he]
  change (i.2.val:ℕ) = ((i.1.val:ℕ)*(i.2.val:ℕ))/(i.1.val:ℕ)
  exact (Nat.mul_div_right (i.2.val:ℕ) i.1.val.property).symm

/-- Exact attachment to the original Delta kernel and D*k inverse phase. -/
theorem fixedDGcd_original_delta_phase {D k p : ℕ} [NeZero D] [NeZero k]
    (i : fixedDGcdIndex D) (hp : Nat.Coprime p (D*k)) :
    letI : NeZero (D*k) := ⟨Nat.mul_ne_zero (NeZero.ne D) (NeZero.ne k)⟩
    letI : NeZero ((D/(i.1.val:ℕ))*k) :=
      ⟨Nat.mul_ne_zero (Nat.ne_of_gt (fixedDGcd_quotient_pos
        (Nat.pos_of_ne_zero (NeZero.ne D)) i)) (NeZero.ne k)⟩
    lemma53PaperDelta D ((fixedDGcdLift i:ℝ)/((D:ℝ)*(p:ℝ)*(k:ℝ))) *
      ZMod.stdAddChar (-((fixedDGcdLift i:ℕ):ZMod (D*k))*(p:ZMod (D*k))⁻¹) =
    lemma53PaperDelta D ((i.2.val:ℝ)/(((D/(i.1.val:ℕ):ℕ):ℝ)*(p:ℝ)*(k:ℝ))) *
      ZMod.stdAddChar (-((i.2.val:ℕ):ZMod ((D/(i.1.val:ℕ))*k)) *
        (p:ZMod ((D/(i.1.val:ℕ))*k))⁻¹) := by
  letI : NeZero (i.1.val:ℕ) := ⟨Nat.ne_of_gt i.1.val.property⟩
  letI : NeZero (D*k) := ⟨Nat.mul_ne_zero (NeZero.ne D) (NeZero.ne k)⟩
  letI : NeZero ((D/(i.1.val:ℕ))*k) :=
    ⟨Nat.mul_ne_zero (Nat.ne_of_gt (fixedDGcd_quotient_pos
      (Nat.pos_of_ne_zero (NeZero.ne D)) i)) (NeZero.ne k)⟩
  simp only [fixedDGcdLift, PNat.mul_coe]
  rw [fixedDGcd_scaled_kernel_argument i.1.property,
    fixedDGcd_divisor_inverse_phase i.1.property hp]

/-- Additive reciprocity followed by the genuine gcd reduction attaches
DeltaOne directly to the quotient Delta phase without a nonunit assumption. -/
theorem fixedDGcd_original_deltaOne_phase {D k p : ℕ} [NeZero D] [NeZero k] [NeZero p]
    (i : fixedDGcdIndex D) (hp : Nat.Coprime p (D*k)) :
    letI : NeZero (D*k) := ⟨Nat.mul_ne_zero (NeZero.ne D) (NeZero.ne k)⟩
    letI : NeZero ((D/(i.1.val:ℕ))*k) :=
      ⟨Nat.mul_ne_zero (Nat.ne_of_gt (fixedDGcd_quotient_pos
        (Nat.pos_of_ne_zero (NeZero.ne D)) i)) (NeZero.ne k)⟩
    lemma53PaperDeltaOne D ((fixedDGcdLift i:ℝ)/(((D*k:ℕ):ℝ)*(p:ℝ))) *
      ZMod.stdAddChar (((fixedDGcdLift i:ℕ):ZMod p)*((D*k:ℕ):ZMod p)⁻¹) =
    lemma53PaperDelta D ((i.2.val:ℝ)/(((D/(i.1.val:ℕ):ℕ):ℝ)*(p:ℝ)*(k:ℝ))) *
      ZMod.stdAddChar (-((i.2.val:ℕ):ZMod ((D/(i.1.val:ℕ))*k)) *
        (p:ZMod ((D/(i.1.val:ℕ))*k))⁻¹) := by
  letI : NeZero (D*k) := ⟨Nat.mul_ne_zero (NeZero.ne D) (NeZero.ne k)⟩
  letI : NeZero ((D/(i.1.val:ℕ))*k) :=
    ⟨Nat.mul_ne_zero (Nat.ne_of_gt (fixedDGcd_quotient_pos
      (Nat.pos_of_ne_zero (NeZero.ne D)) i)) (NeZero.ne k)⟩
  rw [additiveReciprocity_delta hp.symm]
  have harg : (((D*k:ℕ):ℝ)*(p:ℝ)) = (D:ℝ)*(p:ℝ)*(k:ℝ) := by push_cast; ring
  rw [harg]
  exact fixedDGcd_original_delta_phase i hp

end ZhangLS.Spec
