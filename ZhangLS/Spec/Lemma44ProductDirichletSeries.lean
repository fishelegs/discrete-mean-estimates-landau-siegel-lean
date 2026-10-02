import ZhangLS.Spec.Lemma44SectionFourGamma
import ZhangLS.Spec.Lemma23ArithmeticCoefficients

/-!
# The actual product Dirichlet series in Lemma 4.4

The primitive twist at level `D*p` is evaluated on natural numbers,
including nonunits. Its product with `ψ` is then identified with the
Dirichlet series with the paper's genuine coefficients `ν(n)ψ(n)`.
-/

namespace ZhangLS.Spec

open ArithmeticFunction
open scoped LSeries.notation ArithmeticFunction.zeta

set_option maxHeartbeats 1000000

/-- Changing levels only removes nonunits; the product removes exactly the
nonunits at either level. Thus this identity also holds when `n` is not coprime. -/
theorem lemma44CharacterTwist_eval_nat {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (n : ℕ) :
    lemma44CharacterTwist χ ψ (n : ZMod (D * p)) =
      χ.chi (n : ZMod D) * ψ (n : ZMod p) := by
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  by_cases hn : n.Coprime (D * p)
  · have hχ := DirichletCharacter.changeLevel_eq_cast_of_dvd χ.chi
      (D.dvd_mul_right p) (ZMod.unitOfCoprime n hn)
    have hψ := DirichletCharacter.changeLevel_eq_cast_of_dvd ψ
      (p.dvd_mul_left D) (ZMod.unitOfCoprime n hn)
    simp only [ZMod.coe_unitOfCoprime,
      ZMod.cast_natCast (D.dvd_mul_right p) n] at hχ
    simp only [ZMod.coe_unitOfCoprime,
      ZMod.cast_natCast (p.dvd_mul_left D) n] at hψ
    simp only [lemma44CharacterTwist, MulChar.mul_apply, hχ, hψ]
  · have hnon : ¬IsUnit (n : ZMod (D * p)) := by
      simpa only [ZMod.isUnit_iff_coprime] using hn
    rw [MulChar.map_nonunit _ hnon]
    by_cases hχ : n.Coprime D
    · have hψ : ¬n.Coprime p := by
        intro hp
        exact hn (hχ.mul_right hp)
      rw [MulChar.map_nonunit ψ (by simpa only [ZMod.isUnit_iff_coprime] using hψ), mul_zero]
    · rw [MulChar.map_nonunit χ.chi (by simpa only [ZMod.isUnit_iff_coprime] using hχ), zero_mul]

/-- The real character's inverse is itself, so the reflected twist has the
paper's conjugate character `ψ⁻¹`. -/
theorem lemma44CharacterTwist_inv {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) :
    (lemma44CharacterTwist χ ψ)⁻¹ = lemma44CharacterTwist χ ψ⁻¹ := by
  have hχ : χ.chi⁻¹ = χ.chi := by
    have h := χ.quadratic
    rw [pow_two] at h
    exact inv_eq_of_mul_eq_one_left h
  simp only [lemma44CharacterTwist, mul_inv_rev, ← map_inv, hχ]
  exact mul_comm _ _

/-- Twisting the genuine `ν=1*χ` coefficients yields the convolution of the
two genuine character sequences. -/
theorem lemma44_nu_twist_convolution {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) :
    (fun n : ℕ => lemma23NuArithmeticFunction χ n * ψ (n : ZMod p)) =
      (fun n : ℕ => ψ (n : ZMod p)) ⍟
        (fun n : ℕ => lemma44CharacterTwist χ ψ (n : ZMod (D * p))) := by
  have hnu : (fun n : ℕ => lemma23NuArithmeticFunction χ n) =
      (1 : ℕ → ℂ) ⍟ (fun n : ℕ => χ.chi (n : ZMod D)) := by
    rw [LSeries.one_convolution_eq_zeta_convolution]
    simp only [LSeries.convolution,
      lemma23NuArithmeticFunction, lemma23CharacterArithmeticFunction]
    have hz : toArithmeticFunction (fun n : ℕ => (ArithmeticFunction.zeta n : ℂ)) =
        (ζ : ArithmeticFunction ℂ) := by
      ext n
      simp [toArithmeticFunction, ArithmeticFunction.zeta_apply]
    rw [hz]
  have htw : ((fun n : ℕ => ψ (n : ZMod p)) *
      (fun n : ℕ => χ.chi (n : ZMod D))) =
        (fun n : ℕ => lemma44CharacterTwist χ ψ (n : ZMod (D * p))) := by
    funext n
    rw [lemma44CharacterTwist_eval_nat]
    exact mul_comm _ _
  have h := ψ.mul_convolution_distrib (1 : ℕ → ℂ) (fun n : ℕ => χ.chi (n : ZMod D))
  rw [mul_one, htw, ← hnu] at h
  rw [h]
  funext n
  exact mul_comm _ _

/-- Absolute convergence of the actual product coefficient series to the
right of one, discharged from character bounds. -/
theorem lemma44_product_series_summable {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n : ℕ => lemma23NuArithmeticFunction χ n * ψ (n : ZMod p)) s := by
  rw [lemma44_nu_twist_convolution]
  exact (DirichletCharacter.LSeriesSummable_of_one_lt_re ψ hs).convolution
    (DirichletCharacter.LSeriesSummable_of_one_lt_re (lemma44CharacterTwist χ ψ) hs)

/-- The actual product `L(s,ψ)L(s,χψ)` has exactly the coefficients used by
the paper's short and long polynomials. -/
theorem lemma44_product_LFunction_eq_LSeries {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    {s : ℂ} (hs : 1 < s.re) :
    letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    DirichletCharacter.LFunction ψ s *
        DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) s =
      LSeries (fun n : ℕ => lemma23NuArithmeticFunction χ n * ψ (n : ZMod p)) s := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  rw [DirichletCharacter.LFunction_eq_LSeries ψ hs,
    DirichletCharacter.LFunction_eq_LSeries (lemma44CharacterTwist χ ψ) hs,
    lemma44_nu_twist_convolution]
  exact (LSeries_convolution' (DirichletCharacter.LSeriesSummable_of_one_lt_re ψ hs)
    (DirichletCharacter.LSeriesSummable_of_one_lt_re (lemma44CharacterTwist χ ψ) hs)).symm

end ZhangLS.Spec
