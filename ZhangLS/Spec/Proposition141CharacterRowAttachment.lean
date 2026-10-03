import ZhangLS.Spec.Proposition141FixedGcdAttachment
import ZhangLS.Spec.Proposition141LevelSigmaAttachment
import ZhangLS.Spec.Proposition141ChiMainNormalization
import ZhangLS.Spec.Proposition71CharacterFibers

/-! Exact full-character expansion of the genuine fixed-D source, and
identification of its literal principal and χ-induced rows. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical ComplexConjugate

lemma proposition141_level_prime_row_positive {D N:ℕ} (θ:DirichletCharacter ℂ N)
    (κ:ℕ→ℂ) (D₁ d p:ℕ) :
    proposition141LevelPrimeRow (D:=D) θ κ D₁ d p=
      ∑'l:ℕ+,κ (D₁*d*l)*θ (-((l:ℕ):ZMod N))*conj (θ (p:ZMod N))*
        lemma53PaperDelta D ((l:ℝ)/((p:ℝ)*(N:ℝ))) := by
  let f := fun l:ℕ=>if 0<l then κ (D₁*d*l)*θ (-(l:ZMod N))*conj (θ (p:ZMod N))*
    lemma53PaperDelta D ((l:ℝ)/((p:ℝ)*(N:ℝ))) else 0
  have hf:f 0=0 := by simp [f]
  change (∑'l:ℕ,f l)=_
  rw [←proposition71_positive_nat_tsum f hf]
  apply tsum_congr
  intro l
  rw [show f (l:ℕ)=_ from if_pos l.property]

lemma proposition141_level_prime_row_character_fiber {D N:ℕ} (θ:DirichletCharacter ℂ N)
    (κ:ℕ→ℂ) (D₁ d p:ℕ) :
    proposition141LevelPrimeRow (D:=D) θ κ D₁ d p=
      conj (θ (p:ZMod N))*proposition71CharacterDeltaFiber D (D₁*d) ((p:ℝ)*(N:ℝ)) κ θ := by
  rw [proposition141_level_prime_row_positive]
  unfold proposition71CharacterDeltaFiber
  rw [←tsum_mul_left]
  apply tsum_congr
  intro l
  ring

/-- Full (14.7) expansion, only after the actual fixed-D reduction has
established the long variable as a unit at the smaller modulus. -/
theorem proposition141_fixed_reciprocal_character_expansion {D D₁ D₂ p d k:ℕ} [NeZero (D₂*k)]
    (hD:1<D) (hL:2000≤lemma23PaperL D) (hp:p.Coprime (D₂*k))
    {B:ℝ} (hB:0≤B) {κ:ℕ→ℂ} (hκ:Proposition141KappaBound B κ)
    (hD₁:0<D₁) (hd:0<d) (hq:1≤(D₂:ℝ)*(p:ℝ)*(k:ℝ))
    (hqP:(D₂:ℝ)*(p:ℝ)*(k:ℝ)≤lemma23PaperP D^10) :
    proposition141FixedReciprocalInner D D₁ D₂ p d k κ=
      ((D₂*k).totient:ℂ)⁻¹*∑θ:DirichletCharacter ℂ (D₂*k),
        gaussSum θ⁻¹ ZMod.stdAddChar*proposition141LevelPrimeRow (D:=D) θ κ D₁ d p := by
  unfold proposition141FixedReciprocalInner
  rw [proposition71_reciprocal_fiber_character_expansion hD hL hp κ hB hκ
    (Nat.mul_pos hD₁ hd) hq hqP]
  congr 1
  apply sum_congr rfl
  intro θ hθ
  rw [proposition141_level_prime_row_character_fiber]
  have hscale:(p:ℝ)*((D₂*k:ℕ):ℝ)=(D₂:ℝ)*(p:ℝ)*(k:ℝ) := by push_cast; ring
  rw [hscale]
  ring

/-- The principal row used by the proved correction bound is precisely
the principal term of the full source character expansion. -/
theorem proposition141_principal_row_eq_level_source {D D₁ D₂ p d k:ℕ} [NeZero (D₂*k)]
    (κ a:ℕ→ℂ) :
    proposition141PrincipalRow D D₁ D₂ p d k κ a=
      (d:ℂ)⁻¹*(a (d*k)/((k:ℂ)*((D₂*k).totient:ℂ)))*
        (gaussSum (1:DirichletCharacter ℂ (D₂*k))⁻¹ ZMod.stdAddChar*
          proposition141LevelPrimeRow (D:=D) (1:DirichletCharacter ℂ (D₂*k)) κ D₁ d p) := by
  rw [proposition141_principal_literal_row]
  unfold proposition141LevelPrimeRow
  congr 2
  apply tsum_congr
  intro l
  by_cases hl:0<l
  · rw [if_pos hl,if_pos hl]
    congr 2
    push_cast
    ring
  · rw [if_neg hl,if_neg hl]

/-- Actual χ-induced row at level Dk, connected to the independently proved
original main normalization. -/
theorem proposition141_chi_inner_eq_level_source {D p d k:ℕ} [NeZero k]
    (χ:RealPrimitiveCharacter D) (κ:ℕ→ℂ) :
    letI : NeZero (D*k) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne k)⟩
    proposition141ChiInducedInner χ κ p d k=
      gaussSum (χ.chi.changeLevel (D.dvd_mul_right k))⁻¹ ZMod.stdAddChar*
        proposition141LevelPrimeRow (D:=D) (χ.chi.changeLevel (D.dvd_mul_right k)) κ 1 d p := by
  letI : NeZero (D*k) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne k)⟩
  have hk:0<k := Nat.pos_of_ne_zero (NeZero.ne k)
  unfold proposition141ChiInducedInner
  rw [dif_pos hk,proposition141_level_prime_row_positive]
  simp only [one_mul]
  congr 1
  apply tsum_congr
  intro l
  congr 2
  push_cast
  ring

end ZhangLS.Spec
