import ZhangLS.Spec.ReciprocalDeltaGcd
import ZhangLS.Spec.InducedGaussMainCharacters

/-! The exact principal/nonprincipal split of the Section7 reciprocal phase.
Both unit conditions are proved or stated at the point of expansion; the
principal contribution is mu(k)/phi(k), including k=1. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical ComplexConjugate
set_option maxHeartbeats 2500000

/-- The literal Section7 character expansion, including its actual principal
term and all nonprincipal characters at the full modulus. -/
theorem proposition71_reciprocal_character_split {k : ℕ} [NeZero k]
    {p l : ℕ} (hp : p.Coprime k) (hl : l.Coprime k) :
    deltaReciprocalWeight p l k=
      (ArithmeticFunction.moebius k : ℂ)/(k.totient : ℂ)+
        (k.totient : ℂ)⁻¹*∑θ∈(univ : Finset (DirichletCharacter ℂ k)).erase 1,
          gaussSum θ⁻¹ ZMod.stdAddChar*θ (-(l : ZMod k))*conj (θ (p : ZMod k)) := by
  have hpunit : IsUnit (p : ZMod k) := (ZMod.isUnit_iff_coprime p k).mpr hp
  have hlunit : IsUnit (l : ZMod k) := (ZMod.isUnit_iff_coprime l k).mpr hl
  obtain ⟨u,hu⟩ := hpunit
  have he := proposition141_additive_phase_character_expansion (l : ZMod k) hlunit u
  rw [←ZMod.inv_coe_unit,hu] at he
  have hpos : 0<k := Nat.pos_of_ne_zero (NeZero.ne k)
  simp only [deltaReciprocalWeight,dif_pos hpos]
  rw [he]
  have hs := sum_erase_add (univ : Finset (DirichletCharacter ℂ k))
    (fun θ => gaussSum θ⁻¹ ZMod.stdAddChar*θ (-(l : ZMod k))*conj (θ (p : ZMod k)))
    (mem_univ (1 : DirichletCharacter ℂ k))
  have hpunit' : IsUnit (p : ZMod k) := (ZMod.isUnit_iff_coprime p k).mpr hp
  simp only [inv_one,inducedGauss_principal_value,MulChar.one_apply hlunit.neg,
    MulChar.one_apply hpunit',map_one,mul_one] at hs
  rw [←hs]
  ring

/-- The nonunit long branch vanishes through each actual character. -/
lemma proposition71_nonunit_character_term_zero {k : ℕ} [NeZero k]
    (θ : DirichletCharacter ℂ k) {l : ℕ} (hl : ¬l.Coprime k) : θ (-(l : ZMod k))=0 := by
  apply MulChar.map_nonunit
  intro hu
  apply hl
  exact (ZMod.isUnit_iff_coprime l k).mp (by simpa only [neg_neg] using hu.neg)

/-- Pointwise split with the original coprimality filter and genuine removal
of that filter only from the character branch. -/
theorem proposition71_reciprocal_filtered_split {k : ℕ} [NeZero k]
    {p l : ℕ} (hp : p.Coprime k) (z : ℂ) :
    (if l.Coprime k then z*deltaReciprocalWeight p l k else 0)=
      (ArithmeticFunction.moebius k : ℂ)/(k.totient : ℂ)*(if l.Coprime k then z else 0)+
        (k.totient : ℂ)⁻¹*∑θ∈(univ : Finset (DirichletCharacter ℂ k)).erase 1,
          gaussSum θ⁻¹ ZMod.stdAddChar*conj (θ (p : ZMod k))*(z*θ (-(l : ZMod k))) := by
  by_cases hl : l.Coprime k
  · rw [if_pos hl,if_pos hl,proposition71_reciprocal_character_split hp hl]
    simp only [mul_add,mul_sum]
    congr 1
    · ring
    · apply sum_congr rfl
      intro θ hθ
      ring
  · simp only [if_neg hl,proposition71_nonunit_character_term_zero _ hl,
      mul_zero,sum_const_zero,add_zero]

end ZhangLS.Spec
