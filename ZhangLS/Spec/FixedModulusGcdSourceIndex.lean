import ZhangLS.Spec.FixedModulusGcdAttachment
import ZhangLS.Spec.AdditiveReciprocity

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex
open scoped Classical ComplexConjugate

/-- The exact arithmetic index of the displayed fixed-D source decomposition. -/
abbrev fixedDCoprimeGcdIndex (D k : ℕ) : Type :=
  Σ d : {d : ℕ+ // (d:ℕ) ∣ D ∧ Nat.Coprime (d:ℕ) k},
    {l : ℕ+ // Nat.Coprime (l:ℕ) ((D/(d.val:ℕ))*k)}

def fixedDCoprimeGcdForget {D k : ℕ} (i : fixedDCoprimeGcdIndex D k) : fixedDGcdIndex D :=
  ⟨⟨i.1.val,i.1.property.1⟩,⟨i.2.val,(Nat.coprime_mul_iff_right.mp i.2.property).1⟩⟩

def fixedDCoprimeGcdLift {D k : ℕ} (i : fixedDCoprimeGcdIndex D k) :
    {l : ℕ+ // Nat.Coprime (l:ℕ) k} :=
  ⟨i.1.val*i.2.val, i.1.property.2.mul_left (Nat.coprime_mul_iff_right.mp i.2.property).2⟩

theorem fixedDCoprimeGcd_lift_gcd {D k : ℕ} (i : fixedDCoprimeGcdIndex D k) :
    Nat.gcd ((fixedDCoprimeGcdLift i).val:ℕ) D = (i.1.val:ℕ) :=
  fixedDGcd_lift_gcd (fixedDCoprimeGcdForget i)

theorem fixedDCoprimeGcd_lift_injective (D k : ℕ) :
    Function.Injective (@fixedDCoprimeGcdLift D k) := by
  intro x y he
  have hv := congrArg Subtype.val he
  have hd : x.1=y.1 := by
    apply Subtype.ext
    apply PNat.eq
    rw [← fixedDCoprimeGcd_lift_gcd x, ← fixedDCoprimeGcd_lift_gcd y, hv]
  rcases x with ⟨d,⟨l,hl⟩⟩
  rcases y with ⟨e,⟨m,hm⟩⟩
  change d=e at hd
  subst e
  change d.val*l=d.val*m at hv
  have hlm : l=m := mul_left_cancel hv
  subst m
  rfl

theorem fixedDCoprimeGcd_lift_surjective (D k : ℕ) :
    Function.Surjective (@fixedDCoprimeGcdLift D k) := by
  intro l
  obtain ⟨i,hi⟩ := fixedDGcd_lift_surjective D l.val
  have hc : Nat.Coprime (fixedDGcdLift i:ℕ) k := by rw [hi]; exact l.property
  have hparts := (fixedDGcd_coprime_iff i k).mp hc
  refine ⟨⟨⟨i.1.val, i.1.property, hparts.1⟩,
    ⟨i.2.val, i.2.property.mul_right hparts.2⟩⟩,?_⟩
  apply Subtype.ext
  exact hi

noncomputable def fixedDCoprimeGcdEquiv (D k : ℕ) :
    fixedDCoprimeGcdIndex D k ≃ {l : ℕ+ // Nat.Coprime (l:ℕ) k} :=
  Equiv.ofBijective fixedDCoprimeGcdLift
    ⟨fixedDCoprimeGcd_lift_injective D k,fixedDCoprimeGcd_lift_surjective D k⟩

/-- Exactly the paper's coprime positive-index decomposition. -/
theorem fixedDCoprimeGcd_tsum_reindex {A : Type*} [NormedAddCommGroup A] [CompleteSpace A]
    (D k : ℕ) (F : {l : ℕ+ // Nat.Coprime (l:ℕ) k} → A) :
    (∑' l, F l) = ∑' i : fixedDCoprimeGcdIndex D k, F (fixedDCoprimeGcdLift i) :=
  ((fixedDCoprimeGcdEquiv D k).tsum_eq F).symm

/-- The character inserted after the unit restriction supplies the zero
extension; no additive exponential is incorrectly set to zero. -/
theorem fixedDGcd_character_zero_extension {N : ℕ} [NeZero N]
    (θ : DirichletCharacter ℂ N) (l p : ℕ) :
    (if Nat.Coprime l N then
      gaussSum θ⁻¹ ZMod.stdAddChar * θ (-(l:ZMod N)) * conj (θ (p:ZMod N)) else 0) =
      gaussSum θ⁻¹ ZMod.stdAddChar * θ (-(l:ZMod N)) * conj (θ (p:ZMod N)) := by
  by_cases hl : Nat.Coprime l N
  · rw [if_pos hl]
  · rw [if_neg hl]
    exact (proposition141_nonunit_character_phase_zero θ _ _
      (fun hu => hl ((ZMod.isUnit_iff_coprime l N).mp hu))).symm

/-- Cancellation in the original Delta kernel keeps the full quotient scale. -/
theorem fixedDGcd_scaled_kernel_argument {D d : ℕ} [NeZero d] (hd : d ∣ D)
    (l : ℕ) (p k : ℝ) :
    ((d*l:ℕ):ℝ)/((D:ℝ)*p*k) = (l:ℝ)/(((D/d:ℕ):ℝ)*p*k) := by
  have hD : (D:ℝ) = (d:ℝ)*(D/d:ℕ) := by
    exact_mod_cast (Nat.mul_div_cancel' hd).symm
  have hd' : (d:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  rw [hD]
  push_cast
  field_simp

end ZhangLS.Spec
