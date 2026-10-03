import ZhangLS.Spec.Proposition141Objects
import ZhangLS.Spec.Proposition71FrontFamilyRate
import ZhangLS.Spec.Proposition71FrontHeadTail
import ZhangLS.Spec.InducedGaussMainCharacters

/-! # Exact original Section14 front-end objects

The functional-equation character is χψ at conductor Dp. Both Dirichlet
polynomial coefficient characters remain ψ and its inverse, without an
extra χ. The original closed short support and upward J(1) are unchanged.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

lemma proposition141_indices_eq_closed_prefix (D:ℕ) :
    proposition141Indices D=Icc 1 ⌊2*lemma61PaperP4 D⌋₊ := by
  ext n
  rw [proposition141_mem_indices,mem_Icc]
  constructor
  · intro hn
    exact ⟨hn.1,Nat.le_floor hn.2⟩
  · intro hn
    exact ⟨hn.1,(Nat.le_floor_iff' (by omega : n≠0)).mp hn.2⟩

lemma proposition141_polynomial_eq_front {D p:ℕ} (a:ℕ→ℂ) (ψ:DirichletCharacter ℂ p) (s:ℂ) :
    proposition141Polynomial D a ψ s=lemma81FiniteCharacterPolynomial ⌊2*lemma61PaperP4 D⌋₊ a ψ s := by
  rw [lemma81_finite_character_polynomial_eq_cpow_sum]
  unfold proposition141Polynomial
  rw [proposition141_indices_eq_closed_prefix]

lemma proposition141_polynomial_shift_exact {D p:ℕ} (a:ℕ→ℂ) (ψ:DirichletCharacter ℂ p) (s:ℂ) :
    proposition141Polynomial D a ψ (1-s)=
      ∑n∈proposition141Indices D,(a n*ψ (n:ZMod p))*(n:ℂ)^(s-1) := by
  unfold proposition141Polynomial
  apply sum_congr rfl
  intro n hn
  rw [show 1-s=-(s-1) by ring,Complex.cpow_neg,div_inv_eq_mul]

lemma proposition141_segment_exact (D:ℕ) (f:ℂ→ℂ) :
    proposition141SegmentIntegral D f=lemma81NormalizedSegmentIntegral D 1 f := by
  simp only [proposition141SegmentIntegral,lemma81NormalizedSegmentIntegral,lemma81SegmentPoint,Complex.ofReal_one]

lemma proposition141_integral_actual_front {D p:ℕ} [NeZero p]
    (χ:RealPrimitiveCharacter D) (κ a:ℕ→ℂ) (ψ:DirichletCharacter ℂ p) :
    letI : NeZero (D*p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    proposition141Integral χ κ a ψ=lemma81NormalizedSegmentIntegral D 1
      (proposition71FrontActualKernel D (lemma44CharacterTwist χ ψ)
        (fun m=>κ m*ψ (m:ZMod p)) (proposition141Indices D) (fun n=>a n*ψ⁻¹ (n:ZMod p))) := by
  letI : NeZero (D*p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  unfold proposition141Integral
  rw [proposition141_segment_exact]
  congr 1
  funext s
  unfold proposition71FrontActualKernel proposition141KappaSeries
  rw [proposition141_polynomial_shift_exact,proposition71_front_omega_exact]

lemma proposition141_integral_infinite_front {D p:ℕ} [NeZero p]
    (χ:RealPrimitiveCharacter D) (κ a:ℕ→ℂ) (ψ:DirichletCharacter ℂ p) :
    letI : NeZero (D*p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    proposition141Integral χ κ a ψ=lemma81NormalizedSegmentIntegral D 1
      (proposition71InfiniteFrontKernel D (lemma44CharacterTwist χ ψ) ψ ⌊2*lemma61PaperP4 D⌋₊ κ a) := by
  letI : NeZero (D*p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  unfold proposition141Integral
  rw [proposition141_segment_exact]
  congr 1
  funext s
  unfold proposition71InfiniteFrontKernel proposition141KappaSeries
  rw [proposition141_polynomial_eq_front,proposition71_front_omega_exact]

lemma proposition141_twist_inverse {D p:ℕ} (χ:RealPrimitiveCharacter D) (ψ:DirichletCharacter ℂ p) :
    (lemma44CharacterTwist χ ψ)⁻¹=lemma44CharacterTwist χ ψ⁻¹ := by
  unfold lemma44CharacterTwist
  rw [mul_inv_rev,inducedGauss_real_changeLevel_inv]
  rw [map_inv]
  exact mul_comm _ _

end ZhangLS.Spec
