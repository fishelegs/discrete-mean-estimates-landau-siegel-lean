import ZhangLS.Spec.Lemma44CharacterProduct
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

/-! # Genuine finite character-family reindexing by primitive conductor

Level-N characters are put in bijection with actual primitive characters at
divisors r | N using changeLevel. Injectivity is proved through conductor
invariance and changeLevel injectivity; surjectivity uses the actual inducer.
The principal branch is exactly r=1, including N=1.
-/
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace ZhangLS.Spec
open Complex DirichletCharacter Finset
open scoped Classical

def primitiveConductorFamilyIndex (N:ℕ) : Type :=
  Σr:{r:ℕ // r∈N.divisors}, {θ:DirichletCharacter ℂ r.val // θ.IsPrimitive}

noncomputable instance primitiveConductorFamilyFintype (N:ℕ) : Fintype (primitiveConductorFamilyIndex N) :=
  inferInstanceAs (Fintype (Σr:{r:ℕ // r∈N.divisors}, {θ:DirichletCharacter ℂ r.val // θ.IsPrimitive}))

noncomputable def primitiveConductorFamilyLift (N:ℕ) (i:primitiveConductorFamilyIndex N) :
    DirichletCharacter ℂ N :=
  i.2.val.changeLevel (Nat.mem_divisors.mp i.1.property).1

lemma primitiveConductorFamily_index_pos {N:ℕ} (i:primitiveConductorFamilyIndex N) : 0 < (i.1).val :=
  Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp i.1.property).1
    (Nat.pos_of_ne_zero (Nat.mem_divisors.mp i.1.property).2)

/-- The index r is the actual conductor of the induced character. -/
theorem primitiveConductorFamily_lift_conductor {N:ℕ} [NeZero N]
    (i:primitiveConductorFamilyIndex N) : (primitiveConductorFamilyLift N i).conductor=i.1.val := by
  letI : NeZero i.1.val := ⟨(primitiveConductorFamily_index_pos i).ne'⟩
  rw [primitiveConductorFamilyLift,lemma44_conductor_changeLevel i.2.val]
  exact i.2.property

theorem primitiveConductorFamily_lift_injective {N:ℕ} [NeZero N] :
    Function.Injective (primitiveConductorFamilyLift N) := by
  intro x y he
  have hc : x.1.val=y.1.val := by
    rw [←primitiveConductorFamily_lift_conductor x,←primitiveConductorFamily_lift_conductor y,he]
  rcases x with ⟨⟨r,hr⟩,⟨φ,hφ⟩⟩
  rcases y with ⟨⟨s,hs⟩,⟨ψ,hψ⟩⟩
  change r=s at hc
  subst s
  have hp : φ=ψ := DirichletCharacter.changeLevel_injective (Nat.mem_divisors.mp hr).1 he
  subst ψ
  rfl

theorem primitiveConductorFamily_lift_surjective {N:ℕ} [NeZero N] :
    Function.Surjective (primitiveConductorFamilyLift N) := by
  intro θ
  refine ⟨⟨⟨θ.conductor,Nat.mem_divisors.mpr ⟨θ.conductor_dvd_level,NeZero.ne N⟩⟩,
    ⟨θ.primitiveCharacter,θ.primitiveCharacter_isPrimitive⟩⟩,?_⟩
  exact θ.changeLevel_primitiveCharacter

/-- Actual finite conductor decomposition, with no guessed primitive names. -/
noncomputable def primitiveConductorFamilyEquiv (N:ℕ) [NeZero N] :
    primitiveConductorFamilyIndex N ≃ DirichletCharacter ℂ N :=
  Equiv.ofBijective (primitiveConductorFamilyLift N)
    ⟨primitiveConductorFamily_lift_injective,primitiveConductorFamily_lift_surjective⟩

/-- Exact character sum reindexed over every primitive conductor divisor. -/
theorem primitiveConductorFamily_sum {N:ℕ} [NeZero N] {A:Type*} [AddCommMonoid A]
    (F:DirichletCharacter ℂ N→A) :
    (∑θ:DirichletCharacter ℂ N,F θ)=
      ∑i:primitiveConductorFamilyIndex N,F (primitiveConductorFamilyLift N i) := by
  symm
  exact Fintype.sum_equiv (primitiveConductorFamilyEquiv N) _ _ (fun _=>rfl)

/-- The same exact decomposition as an explicit divisor/primitive double sum. -/
theorem primitiveConductorFamily_sum_divisors {N:ℕ} [NeZero N] {A:Type*} [AddCommMonoid A]
    (F:DirichletCharacter ℂ N→A) :
    (∑θ:DirichletCharacter ℂ N,F θ)=
      ∑r:{r:ℕ // r∈N.divisors}, ∑φ:{φ:DirichletCharacter ℂ r.val // φ.IsPrimitive},
        F (φ.val.changeLevel (Nat.mem_divisors.mp r.property).1) := by
  rw [primitiveConductorFamily_sum]
  exact Fintype.sum_sigma _

/-- Reindexing preserves arbitrary actual exclusions or weights. -/
theorem primitiveConductorFamily_filtered_sum {N:ℕ} [NeZero N] {A:Type*} [AddCommMonoid A]
    (P:DirichletCharacter ℂ N→Prop) (F:DirichletCharacter ℂ N→A) :
    (∑θ∈(univ:Finset (DirichletCharacter ℂ N)).filter P,F θ)=
      ∑i:primitiveConductorFamilyIndex N,
        if P (primitiveConductorFamilyLift N i) then F (primitiveConductorFamilyLift N i) else 0 := by
  rw [sum_filter]
  exact primitiveConductorFamily_sum (fun θ=>if P θ then F θ else 0)

/-- The principal induced character occurs precisely at primitive modulus1. -/
theorem primitiveConductorFamily_principal_iff {N:ℕ} [NeZero N]
    (i:primitiveConductorFamilyIndex N) : primitiveConductorFamilyLift N i=1 ↔ i.1.val=1 := by
  rw [DirichletCharacter.eq_one_iff_conductor_eq_one,primitiveConductorFamily_lift_conductor]

/-- The two removals in Section14 become r>1 and inequality with the actual
χ-induced level-N character. The modulus1 branch is never sent to 5.6. -/
theorem primitiveConductorFamily_two_exclusions_sum {N:ℕ} [NeZero N] {A:Type*} [AddCommMonoid A]
    (η:DirichletCharacter ℂ N) (F:DirichletCharacter ℂ N→A) :
    (∑θ∈(univ:Finset (DirichletCharacter ℂ N)).filter (fun θ=>θ≠1 ∧ θ≠η),F θ)=
      ∑i:primitiveConductorFamilyIndex N,
        if 1 < (i.1).val ∧ primitiveConductorFamilyLift N i≠η then
          F (primitiveConductorFamilyLift N i) else 0 := by
  rw [sum_filter,primitiveConductorFamily_sum]
  apply sum_congr rfl
  intro i hi
  have hp := primitiveConductorFamily_index_pos i
  have hn : primitiveConductorFamilyLift N i≠1 ↔ 1 < (i.1).val := by
    constructor
    · intro h
      have hn : (i.1).val≠1 := fun he=>h ((primitiveConductorFamily_principal_iff i).mpr he)
      omega
    · intro hr he
      have hn := (primitiveConductorFamily_principal_iff i).mp he
      omega
  simp only [hn]

end ZhangLS.Spec
