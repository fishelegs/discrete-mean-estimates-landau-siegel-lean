import ZhangLS.Spec.PrimitiveConductorFamily

/-! Exact single-principal exclusion and explicit primitive-divisor sums.
The excluded branch is conductor one, including at original modulus one. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset
open scoped Classical
set_option maxHeartbeats 2000000

theorem primitiveConductor_nonprincipal_sum {N : ℕ} [NeZero N]
    {E : Type*} [AddCommMonoid E] (F : DirichletCharacter ℂ N → E) :
    (∑θ∈(univ : Finset (DirichletCharacter ℂ N)).erase 1,F θ)=
      ∑i : primitiveConductorFamilyIndex N,
        if 1<(i.1).val then F (primitiveConductorFamilyLift N i) else 0 := by
  have hset : (univ : Finset (DirichletCharacter ℂ N)).erase 1=
      univ.filter (fun θ => θ≠1) := by ext θ; simp
  rw [hset,sum_filter]
  rw [primitiveConductorFamily_sum (fun θ : DirichletCharacter ℂ N => if θ≠1 then F θ else 0)]
  apply sum_congr rfl
  intro i hi
  have hp := primitiveConductorFamily_index_pos i
  have hn : primitiveConductorFamilyLift N i≠1 ↔ 1<(i.1).val := by
    rw [ne_eq,primitiveConductorFamily_principal_iff]
    omega
  simp only [hn]

/-- Convert the dependent genuine primitive family to the literal natural
r-divisor and primitive-character filtered sums. -/
theorem primitiveConductor_gt_one_divisor_sum {N : ℕ}
    {E : Type*} [AddCommMonoid E]
    (F : (r : ℕ) → DirichletCharacter ℂ r → E) :
    (∑i : primitiveConductorFamilyIndex N, if 1<(i.1).val then F (i.1).val (i.2).val else 0)=
      ∑r∈N.divisors, if 1<r then
        ∑θ∈(univ : Finset (DirichletCharacter ℂ r)).filter (fun θ => θ.IsPrimitive),F r θ else 0 := by
  change (∑i : Σr : {r : ℕ // r∈N.divisors}, {θ : DirichletCharacter ℂ r.val // θ.IsPrimitive},
    if 1<(i.1).val then F (i.1).val (i.2).val else 0)=_
  rw [Fintype.sum_sigma]
  calc
    _=∑r : {r : ℕ // r∈N.divisors}, if 1<r.val then
        ∑θ∈(univ : Finset (DirichletCharacter ℂ r.val)).filter (fun θ => θ.IsPrimitive),F r.val θ else 0 := by
      apply sum_congr rfl
      intro r hr
      by_cases hp : 1<r.val
      · simp only [if_pos hp]
        exact (Finset.sum_subtype (p := fun θ : DirichletCharacter ℂ r.val => θ.IsPrimitive) ((univ : Finset (DirichletCharacter ℂ r.val)).filter (fun θ => θ.IsPrimitive))
          (fun θ => by simp) (F r.val)).symm
      · simp only [if_neg hp,sum_const_zero]
    _=_ := Finset.sum_coe_sort N.divisors (fun r : ℕ => if 1<r then
      ∑θ∈(univ : Finset (DirichletCharacter ℂ r)).filter (fun θ => θ.IsPrimitive),F r θ else 0)

end ZhangLS.Spec
