import ZhangLS.Spec.CoprimeGaussRealTwist
import ZhangLS.Spec.InducedGaussConductor
import ZhangLS.Spec.Proposition71GaussAverage

/-! # Actual χψ Gauss averages for Section14

The full average, exact primitive correction, and nonunit branches use the
actual product character at modulus D*p. The phase is e(m/(D*n)), retaining
χ(p),τ(χ), the D residue, and the primitive +1 correction.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex DirichletCharacter Finset
open scoped Classical

/-- Exact reduction of one actual product-Gauss summand to the prime-level
Gauss summand. This holds for every ψ, including the principal character. -/
theorem coprimeGauss_prime_average_summand {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (hcop : D.Coprime p)
    (ψ : DirichletCharacter ℂ p) (m n : ZMod p) :
    letI : NeZero D := ⟨χ.modulus_ne_zero⟩
    letI : NeZero (D*p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    gaussSum (lemma44CharacterTwist χ ψ⁻¹) ZMod.stdAddChar*ψ m*ψ⁻¹ n =
      (gaussSum χ.chi ZMod.stdAddChar*χ.chi (p:ZMod D))*
        (gaussSum ψ⁻¹ ZMod.stdAddChar*ψ m*ψ⁻¹ ((D:ZMod p)*n)) := by
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  letI : NeZero (D*p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  rw [coprimeGauss_real_twist_formula χ ψ⁻¹ hcop,map_mul]
  ring

/-- The full character average in Section14 before principal subtraction. -/
theorem coprimeGauss_full_prime_average {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (hp : p.Prime) (hcop : D.Coprime p)
    (m n : ZMod p) (hm : IsUnit m) (hn : IsUnit n) :
    letI : NeZero D := ⟨χ.modulus_ne_zero⟩
    letI : NeZero (D*p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    (∑ ψ : DirichletCharacter ℂ p,
      gaussSum (lemma44CharacterTwist χ ψ⁻¹) ZMod.stdAddChar*ψ m*ψ⁻¹ n) =
      (gaussSum χ.chi ZMod.stdAddChar*χ.chi (p:ZMod D))*
        ((p.totient:ℂ)*ZMod.stdAddChar (m*((D:ZMod p)*n)⁻¹)) := by
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  letI : NeZero (D*p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  have hD : IsUnit (D:ZMod p) := by simpa only [ZMod.isUnit_iff_coprime] using hcop
  simp_rw [coprimeGauss_prime_average_summand χ hcop]
  rw [← mul_sum,proposition71_full_gauss_average hp m ((D:ZMod p)*n) hm (hD.mul hn)]

/-- Exact primitive average, including the principal-character correction. -/
theorem coprimeGauss_primitive_prime_average {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (hp : p.Prime) (hcop : D.Coprime p)
    (m n : ZMod p) (hm : IsUnit m) (hn : IsUnit n) :
    letI : NeZero D := ⟨χ.modulus_ne_zero⟩
    letI : NeZero (D*p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    (∑ ψ ∈ (univ:Finset (DirichletCharacter ℂ p)).filter (fun ψ => ψ.IsPrimitive),
      gaussSum (lemma44CharacterTwist χ ψ⁻¹) ZMod.stdAddChar*ψ m*ψ⁻¹ n) =
      (gaussSum χ.chi ZMod.stdAddChar*χ.chi (p:ZMod D))*
        ((p.totient:ℂ)*ZMod.stdAddChar (m*((D:ZMod p)*n)⁻¹)+1) := by
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  letI : NeZero (D*p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  have hD : IsUnit (D:ZMod p) := by simpa only [ZMod.isUnit_iff_coprime] using hcop
  simp_rw [coprimeGauss_prime_average_summand χ hcop]
  rw [← mul_sum,proposition71_primitive_gauss_average hp m ((D:ZMod p)*n) hm (hD.mul hn)]

/-- The exact primitive average differs from the printed p-leading term
by at most 2√D, uniformly over both residue indices. -/
theorem coprimeGauss_primitive_prime_average_error {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (hp : p.Prime) (hcop : D.Coprime p)
    (m n : ZMod p) (hm : IsUnit m) (hn : IsUnit n) :
    letI : NeZero D := ⟨χ.modulus_ne_zero⟩
    letI : NeZero (D*p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    ‖(∑ ψ ∈ (univ:Finset (DirichletCharacter ℂ p)).filter (fun ψ => ψ.IsPrimitive),
        gaussSum (lemma44CharacterTwist χ ψ⁻¹) ZMod.stdAddChar*ψ m*ψ⁻¹ n) -
      (gaussSum χ.chi ZMod.stdAddChar*χ.chi (p:ZMod D))*
        ((p:ℂ)*ZMod.stdAddChar (m*((D:ZMod p)*n)⁻¹))‖ ≤ 2*Real.sqrt (D:ℝ) := by
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  letI : NeZero (D*p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  have hD : IsUnit (D:ZMod p) := by simpa only [ZMod.isUnit_iff_coprime] using hcop
  have he := proposition71_primitive_gauss_error hp m ((D:ZMod p)*n) hm (hD.mul hn)
  rw [proposition71_primitive_gauss_average hp m ((D:ZMod p)*n) hm (hD.mul hn)] at he
  have hfac : ‖gaussSum χ.chi ZMod.stdAddChar*χ.chi (p:ZMod D)‖≤Real.sqrt (D:ℝ) := by
    rw [norm_mul,inducedGauss_primitive_norm χ.chi χ.primitive]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (χ.chi.norm_le_one _)
      (Real.sqrt_nonneg (D:ℝ))
  rw [coprimeGauss_primitive_prime_average χ hp hcop m n hm hn,← mul_sub,norm_mul]
  have hh := mul_le_mul hfac he (norm_nonneg _) (Real.sqrt_nonneg (D:ℝ))
  simpa only [mul_comm] using hh

/-- Every nonunit branch is zero before an additive leading term is inserted.
Replacing this branch by a nonzero phase requires a separate error estimate. -/
theorem coprimeGauss_primitive_average_nonunit {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (m n : ZMod p) (h : ¬IsUnit m ∨ ¬IsUnit n) :
    letI : NeZero (D*p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    (∑ ψ ∈ (univ:Finset (DirichletCharacter ℂ p)).filter (fun ψ => ψ.IsPrimitive),
      gaussSum (lemma44CharacterTwist χ ψ⁻¹) ZMod.stdAddChar*ψ m*ψ⁻¹ n) = 0 := by
  letI : NeZero (D*p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  apply sum_eq_zero
  intro ψ hψ
  rcases h with hm | hn
  · rw [MulChar.map_nonunit ψ hm,mul_zero,zero_mul]
  · rw [MulChar.map_nonunit ψ⁻¹ hn,mul_zero]

end ZhangLS.Spec
