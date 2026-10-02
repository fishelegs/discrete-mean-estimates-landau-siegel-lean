import ZhangLS.Spec.PrimitiveConductorFamily
import ZhangLS.Spec.InducedGaussConductor

/-! # Actual primitive-conductor reindexing with Gauss amplitudes

These are positive arithmetic bounds for genuine level-N sums. The actual
inducer and its conductor control the Gauss norm, with no guessed primitive
character replacement. Principal r=1 is explicit and removable separately.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex DirichletCharacter Finset
open scoped Classical

theorem primitiveConductorFamily_gauss_bound {N:ℕ} [NeZero N]
    (G:DirichletCharacter ℂ N→ℝ) (hG:∀θ,0≤G θ) :
    (∑θ:DirichletCharacter ℂ N,‖gaussSum θ⁻¹ ZMod.stdAddChar‖*G θ) ≤
      ∑i:primitiveConductorFamilyIndex N,Real.sqrt (i.1.val:ℝ)*G (primitiveConductorFamilyLift N i) := by
  rw [primitiveConductorFamily_sum]
  apply sum_le_sum
  intro i hi
  have hb := inducedGauss_inverse_norm_le_sqrt_conductor (primitiveConductorFamilyLift N i)
  rw [primitiveConductorFamily_lift_conductor] at hb
  exact mul_le_mul_of_nonneg_right hb (hG _)

/-- Nonprincipal terms correspond exactly to primitive levels r>1. -/
theorem primitiveConductorFamily_nonprincipal_gauss_bound {N:ℕ} [NeZero N]
    (G:DirichletCharacter ℂ N→ℝ) (hG:∀θ,0≤G θ) :
    (∑θ∈(univ:Finset (DirichletCharacter ℂ N)).filter (fun θ=>θ≠1),
      ‖gaussSum θ⁻¹ ZMod.stdAddChar‖*G θ) ≤
    ∑i:primitiveConductorFamilyIndex N,
      if 1 < (i.1).val then Real.sqrt (i.1.val:ℝ)*G (primitiveConductorFamilyLift N i) else 0 := by
  rw [sum_filter,primitiveConductorFamily_sum]
  apply sum_le_sum
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
  split_ifs with hr
  · have hb := inducedGauss_inverse_norm_le_sqrt_conductor (primitiveConductorFamilyLift N i)
    rw [primitiveConductorFamily_lift_conductor] at hb
    exact mul_le_mul_of_nonneg_right hb (hG _)
  · rfl

/-- Precisely the two character removals in (14.8), followed by the actual
conductor Gauss bound. The excluded character η may be the χ-induced lift. -/
theorem primitiveConductorFamily_two_exclusions_gauss_bound {N:ℕ} [NeZero N]
    (η:DirichletCharacter ℂ N) (G:DirichletCharacter ℂ N→ℝ) (hG:∀θ,0≤G θ) :
    (∑θ∈(univ:Finset (DirichletCharacter ℂ N)).filter (fun θ=>θ≠1 ∧ θ≠η),
      ‖gaussSum θ⁻¹ ZMod.stdAddChar‖*G θ) ≤
    ∑i:primitiveConductorFamilyIndex N,
      if 1 < (i.1).val ∧ primitiveConductorFamilyLift N i≠η then
        Real.sqrt (i.1.val:ℝ)*G (primitiveConductorFamilyLift N i) else 0 := by
  rw [primitiveConductorFamily_two_exclusions_sum η (fun θ=>‖gaussSum θ⁻¹ ZMod.stdAddChar‖*G θ)]
  apply sum_le_sum
  intro i hi
  split_ifs with hr
  · have hb := inducedGauss_inverse_norm_le_sqrt_conductor (primitiveConductorFamilyLift N i)
    rw [primitiveConductorFamily_lift_conductor] at hb
    exact mul_le_mul_of_nonneg_right hb (hG _)
  · rfl

end ZhangLS.Spec
