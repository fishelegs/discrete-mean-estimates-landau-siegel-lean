import ZhangLS.Spec.Proposition141CharacterRowAttachment
import ZhangLS.Spec.Proposition141CharacterMainSplit

/-! Literal full, χ-induced and remaining source rows before outer summation.
Each row is defined by the actual finite character expansion, never by a difference. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

noncomputable def proposition141FullCharacterRow (D D₁ D₂ p d k:ℕ) (κ:ℕ→ℂ) : ℂ :=
  if hN:0<D₂*k then
    letI : NeZero (D₂*k) := ⟨hN.ne'⟩
    ((D₂*k).totient:ℂ)⁻¹*∑θ:DirichletCharacter ℂ (D₂*k),
      gaussSum θ⁻¹ ZMod.stdAddChar*proposition141LevelPrimeRow (D:=D) θ κ D₁ d p
  else 0

noncomputable def proposition141ChiCharacterRow {D:ℕ} (χ:RealPrimitiveCharacter D)
    (D₁ D₂ p d k:ℕ) (κ:ℕ→ℂ) : ℂ :=
  if hN:0<D₂*k then
    letI : NeZero (D₂*k) := ⟨hN.ne'⟩
    ((D₂*k).totient:ℂ)⁻¹*
      (if hDN:D∣D₂*k then
        gaussSum (χ.chi.changeLevel hDN)⁻¹ ZMod.stdAddChar*
          proposition141LevelPrimeRow (D:=D) (χ.chi.changeLevel hDN) κ D₁ d p
      else 0)
  else 0

noncomputable def proposition141RemainingCharacterRow {D:ℕ} (χ:RealPrimitiveCharacter D)
    (D₁ D₂ p d k:ℕ) (κ:ℕ→ℂ) : ℂ :=
  if hN:0<D₂*k then
    letI : NeZero (D₂*k) := ⟨hN.ne'⟩
    ((D₂*k).totient:ℂ)⁻¹*∑θ∈(univ:Finset (DirichletCharacter ℂ (D₂*k))).filter
      (fun θ=>θ≠1 ∧ ∀hDN:D∣D₂*k,θ≠χ.chi.changeLevel hDN),
      gaussSum θ⁻¹ ZMod.stdAddChar*proposition141LevelPrimeRow (D:=D) θ κ D₁ d p
  else 0

/-- Exact weighted row partition, with the independently proved literal
principal correction identified on the nose. -/
theorem proposition141_weighted_character_row_partition {D D₁ D₂ p d k:ℕ}
    (χ:RealPrimitiveCharacter D) (hD:1<D) (hN:0<D₂*k) (κ a:ℕ→ℂ) :
    (d:ℂ)⁻¹*(a (d*k)/(k:ℂ))*proposition141FullCharacterRow D D₁ D₂ p d k κ=
      proposition141PrincipalRow D D₁ D₂ p d k κ a+
      (d:ℂ)⁻¹*(a (d*k)/(k:ℂ))*proposition141ChiCharacterRow χ D₁ D₂ p d k κ+
      (d:ℂ)⁻¹*(a (d*k)/(k:ℂ))*proposition141RemainingCharacterRow χ D₁ D₂ p d k κ := by
  letI : NeZero (D₂*k) := ⟨hN.ne'⟩
  unfold proposition141FullCharacterRow proposition141ChiCharacterRow proposition141RemainingCharacterRow
  rw [dif_pos hN,dif_pos hN,dif_pos hN,proposition141_character_main_partition χ hD]
  rw [proposition141_principal_row_eq_level_source]
  ring

/-- Only the actual D₁=1 source branch contains a χ-induced row. -/
theorem proposition141_weighted_chi_source_branch {D D₁ p d k:ℕ}
    (χ:RealPrimitiveCharacter D) (hD₁:D₁∈D.divisors) (hk:0<k) (κ a:ℕ→ℂ) :
    (if k.Coprime D₁ then
      (d:ℂ)⁻¹*(a (d*k)/(k:ℂ))*proposition141ChiCharacterRow χ D₁ (D/D₁) p d k κ else 0)=
      if D₁=1 then (d:ℂ)⁻¹*(a (d*k)/((k:ℂ)*((D*k).totient:ℂ)))*
        proposition141ChiInducedInner χ κ p d k else 0 := by
  letI : NeZero k := ⟨hk.ne'⟩
  have hdiv := (Nat.mem_divisors.mp hD₁).1
  have hD₁0:0<D₁ := Nat.pos_of_dvd_of_pos hdiv χ.modulus_pos
  have hD₂:0<D/D₁ := Nat.div_pos (Nat.le_of_dvd χ.modulus_pos hdiv) hD₁0
  have hN:0<(D/D₁)*k := Nat.mul_pos hD₂ hk
  by_cases h1:D₁=1
  · subst D₁
    simp only [Nat.div_one,if_true]
    rw [if_pos (Nat.coprime_one_right k)]
    unfold proposition141ChiCharacterRow
    rw [dif_pos (Nat.mul_pos χ.modulus_pos hk),dif_pos (D.dvd_mul_right k)]
    rw [proposition141_chi_inner_eq_level_source]
    ring
  · rw [if_neg h1]
    by_cases hc:k.Coprime D₁
    · rw [if_pos hc]
      unfold proposition141ChiCharacterRow
      rw [dif_pos hN,dif_neg (proposition141_off_diagonal_not_dvd
        (Nat.mul_div_cancel' hdiv).symm hD₂ (by omega) hc.symm)]
      simp
    · rw [if_neg hc]

end ZhangLS.Spec
