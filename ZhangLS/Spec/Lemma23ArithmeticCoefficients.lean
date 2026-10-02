import ZhangLS.Spec.RealDirichletCharacter
import ZhangLS.Spec.Lemma23FiniteDirichletApproximation
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Zeta

/-!
# Arithmetic coefficients used by Zhang's Section 3

The paper defines `ν` and `υ` as the Dirichlet-series coefficients of `ζ L(s, χ)` and
`ζ⁻¹ L(s, χ)⁻¹`.  This file records those sequences as arithmetic-function convolutions for an
actual real primitive character, and proves their exact inverse relation.  Analytic coefficient
bounds such as `|υ(n)| ≤ ν(n) ≤ τ₂(n)` are separate goals.
-/

namespace ZhangLS.Spec

open ArithmeticFunction
open scoped ArithmeticFunction.zeta ArithmeticFunction.Moebius LSeries.notation

/-- The arithmetic function attached to the actual Dirichlet character `χ`. -/
noncomputable def lemma23CharacterArithmeticFunction {D : ℕ}
    (χ : RealPrimitiveCharacter D) : ArithmeticFunction ℂ :=
  toArithmeticFunction (fun n : ℕ => χ.chi n)

/-- The coefficients `ν = ζ * χ` of `ζ(s)L(s,χ)`. -/
noncomputable def lemma23NuArithmeticFunction {D : ℕ}
    (χ : RealPrimitiveCharacter D) : ArithmeticFunction ℂ :=
  (ζ : ArithmeticFunction ℂ) * lemma23CharacterArithmeticFunction χ

/-- The pointwise twist `χ μ`, which is the coefficient sequence of `L(s,χ)⁻¹`. -/
noncomputable def lemma23CharacterMoebiusArithmeticFunction {D : ℕ}
    (χ : RealPrimitiveCharacter D) : ArithmeticFunction ℂ :=
  toArithmeticFunction (fun n : ℕ => χ.chi n * (μ n : ℂ))

/-- The coefficients `υ = μ * (χ μ)` of `ζ(s)⁻¹L(s,χ)⁻¹`. -/
noncomputable def lemma23UpsilonArithmeticFunction {D : ℕ}
    (χ : RealPrimitiveCharacter D) : ArithmeticFunction ℂ :=
  (μ : ArithmeticFunction ℂ) * lemma23CharacterMoebiusArithmeticFunction χ

/-- Zhang's finite Section 4 polynomial with the actual coefficient sequence `ν`. -/
noncomputable def lemma23ActualSectionFourF {D : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : ℕ → ℂ) (s : ℂ) : ℂ :=
  lemma23SectionFourF D (lemma23NuArithmeticFunction χ) ψ s

/-- Zhang's finite Section 4 polynomial with the actual coefficient sequence `υ`. -/
noncomputable def lemma23ActualSectionFourG {D : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : ℕ → ℂ) (s : ℂ) : ℂ :=
  lemma23SectionFourG D (lemma23UpsilonArithmeticFunction χ) ψ s

/-- The coefficient of the twentieth power of the truncated `ν`-polynomial.
The cutoff on each factor is part of the definition, as in Zhang's expansion of
`F(s, ψ)^20`. -/
noncomputable def lemma23Nu20Coefficient {D : ℕ}
    (χ : RealPrimitiveCharacter D) (n : ℕ) : ℂ :=
  lemma23TupleConvolutionCoefficient (D ^ 4) 20
    (lemma23NuArithmeticFunction χ) n

/-- The coefficient of the twentieth power of the truncated inverse polynomial `G`. -/
noncomputable def lemma23Upsilon20Coefficient {D : ℕ}
    (χ : RealPrimitiveCharacter D) (n : ℕ) : ℂ :=
  lemma23TupleConvolutionCoefficient (D ^ 4) 20
    (lemma23UpsilonArithmeticFunction χ) n

private theorem lemma23_tuple_dirichletCharacter_prod
    {N m : ℕ} (ψ : DirichletCharacter ℂ N) (p : Fin m → ℕ) :
    (∏ i : Fin m, ψ (p i : ZMod N)) =
      ψ (∏ i : Fin m, (p i : ZMod N)) := by
  symm
  exact map_prod ψ (fun i : Fin m => (p i : ZMod N)) Finset.univ

theorem lemma23_tupleConvolutionCoefficient_twist
    {N m : ℕ} (X : ℕ) (c : ℕ → ℂ) (ψ : DirichletCharacter ℂ N) (n : ℕ) :
    lemma23TupleConvolutionCoefficient X m
      (fun k => c k * ψ (k : ZMod N)) n =
        lemma23TupleConvolutionCoefficient X m c n * ψ (n : ZMod N) := by
  classical
  let T := Fintype.piFinset (fun _ : Fin m => Finset.Icc 1 X)
  calc
    lemma23TupleConvolutionCoefficient X m
        (fun k => c k * ψ (k : ZMod N)) n =
      ∑ p ∈ T with (∏ i : Fin m, p i) = n,
        (∏ i : Fin m, c (p i)) *
          ψ (∏ i : Fin m, (p i : ZMod N)) := by
          simp only [lemma23TupleConvolutionCoefficient]
          apply Finset.sum_congr rfl
          intro p hp
          rw [Finset.prod_mul_distrib]
          congr 1
          exact lemma23_tuple_dirichletCharacter_prod ψ p
    _ = ∑ p ∈ T with (∏ i : Fin m, p i) = n,
          (∏ i : Fin m, c (p i)) * ψ (n : ZMod N) := by
          apply Finset.sum_congr rfl
          intro p hp
          simp only [Finset.mem_filter] at hp
          have hprod :
              (∏ i : Fin m, (p i : ZMod N)) = (n : ZMod N) := by
            rw [← Nat.cast_prod, hp.2]
          rw [hprod]
    _ = lemma23TupleConvolutionCoefficient X m c n * ψ (n : ZMod N) := by
          simp only [lemma23TupleConvolutionCoefficient]
          rw [← Finset.sum_mul]

/-- The actual twisted twentieth-power expansion from (3.1) of the paper:
`F(s, ψ)^20 = ∑_{n ≤ D^80} ν₂₀(n) ψ(n) n^{-s}`. -/
theorem lemma23ActualSectionFourF20_expansion {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N) (s : ℂ) :
    (lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod N)) s) ^ 20 =
      ∑ n ∈ Finset.Icc 1 (D ^ 80),
        lemma23Nu20Coefficient χ n * ψ (n : ZMod N) *
          Complex.exp (-s * (Real.log (n : ℝ) : ℂ)) := by
  classical
  rw [lemma23ActualSectionFourF, lemma23SectionFourF]
  have hexp := lemma23FiniteDirichletPolynomial_pow_eq_convolution_sum
    (X := D ^ 4) (m := 20)
    (c := fun n => lemma23NuArithmeticFunction χ n * ψ (n : ZMod N)) s
  have hcut : (D ^ 4) ^ 20 = D ^ 80 := by
    calc
      (D ^ 4) ^ 20 = D ^ (4 * 20) := by rw [pow_mul]
      _ = D ^ 80 := by norm_num
  rw [hcut] at hexp
  have hcoeff (n : ℕ) :
      lemma23TupleConvolutionCoefficient (D ^ 4) 20
        (fun k => lemma23NuArithmeticFunction χ k * ψ (k : ZMod N)) n =
        lemma23Nu20Coefficient χ n * ψ (n : ZMod N) := by
    simpa [lemma23Nu20Coefficient] using
      (lemma23_tupleConvolutionCoefficient_twist (D ^ 4)
        (lemma23NuArithmeticFunction χ) ψ n)
  simpa only [hcoeff] using hexp

/-- The actual twisted twentieth-power expansion for the inverse polynomial `G`, parallel to
the `F` expansion and with its actual `υ₂₀` coefficients. -/
theorem lemma23ActualSectionFourG20_expansion {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N) (s : ℂ) :
    (lemma23ActualSectionFourG χ (fun n => ψ (n : ZMod N)) s) ^ 20 =
      ∑ n ∈ Finset.Icc 1 (D ^ 80),
        lemma23Upsilon20Coefficient χ n * ψ (n : ZMod N) *
          Complex.exp (-s * (Real.log (n : ℝ) : ℂ)) := by
  classical
  rw [lemma23ActualSectionFourG, lemma23SectionFourG]
  have hexp := lemma23FiniteDirichletPolynomial_pow_eq_convolution_sum
    (X := D ^ 4) (m := 20)
    (c := fun n => lemma23UpsilonArithmeticFunction χ n * ψ (n : ZMod N)) s
  have hcut : (D ^ 4) ^ 20 = D ^ 80 := by
    calc
      (D ^ 4) ^ 20 = D ^ (4 * 20) := by rw [pow_mul]
      _ = D ^ 80 := by norm_num
  rw [hcut] at hexp
  have hcoeff (n : ℕ) :
      lemma23TupleConvolutionCoefficient (D ^ 4) 20
        (fun k => lemma23UpsilonArithmeticFunction χ k * ψ (k : ZMod N)) n =
        lemma23Upsilon20Coefficient χ n * ψ (n : ZMod N) := by
    simpa [lemma23Upsilon20Coefficient] using
      (lemma23_tupleConvolutionCoefficient_twist (D ^ 4)
        (lemma23UpsilonArithmeticFunction χ) ψ n)
  simpa only [hcoeff] using hexp

/-- The actual `ν(n)` coefficient is the divisor sum `∑_{d|n} χ(d)`. -/
theorem lemma23NuArithmeticFunction_apply {D : ℕ}
    (χ : RealPrimitiveCharacter D) (n : ℕ) :
    lemma23NuArithmeticFunction χ n = ∑ d ∈ n.divisors, χ.chi d := by
  rw [lemma23NuArithmeticFunction, coe_zeta_mul_apply]
  apply Finset.sum_congr rfl
  intro d hd
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  simp [lemma23CharacterArithmeticFunction, toArithmeticFunction, ne_of_gt hdpos]

/-- The actual Section 3 coefficient sequences are exact Dirichlet-convolution inverses. -/
theorem lemma23Nu_mul_Upsilon_eq_one {D : ℕ}
    (χ : RealPrimitiveCharacter D) :
    lemma23NuArithmeticFunction χ * lemma23UpsilonArithmeticFunction χ = 1 := by
  let χaf : ArithmeticFunction ℂ := lemma23CharacterArithmeticFunction χ
  let χμaf : ArithmeticFunction ℂ := lemma23CharacterMoebiusArithmeticFunction χ
  have hχ : χaf * χμaf = 1 := by
    have hseq := DirichletCharacter.convolution_mul_moebius χ.chi
    have hseq' : (χaf : ℕ → ℂ) ⍟ (χμaf : ℕ → ℂ) = δ := by
      calc
        (χaf : ℕ → ℂ) ⍟ (χμaf : ℕ → ℂ) =
            (fun n : ℕ => χ.chi n) ⍟
              (fun n : ℕ => χ.chi n * (μ n : ℂ)) := by
          apply LSeries.convolution_congr
          · intro n hn
            simp [χaf, lemma23CharacterArithmeticFunction, toArithmeticFunction, hn]
          · intro n hn
            simp [χμaf, lemma23CharacterMoebiusArithmeticFunction,
              toArithmeticFunction, hn]
        _ = δ := hseq
    rw [ArithmeticFunction.coe_mul, ← ArithmeticFunction.one_eq_delta] at hseq'
    exact ArithmeticFunction.coe_inj.mp hseq'
  calc
    lemma23NuArithmeticFunction χ * lemma23UpsilonArithmeticFunction χ
        = ((ζ : ArithmeticFunction ℂ) * (μ : ArithmeticFunction ℂ)) * (χaf * χμaf) := by
            dsimp [lemma23NuArithmeticFunction, lemma23UpsilonArithmeticFunction,
              χaf, χμaf]
            ac_rfl
    _ = 1 := by rw [coe_zeta_mul_coe_moebius, hχ]; simp

/-- Coefficient form of the inverse identity: the `ν * υ` divisor sum is the delta coefficient. -/
theorem lemma23NuUpsilon_convolutionCoefficient {D : ℕ}
    (χ : RealPrimitiveCharacter D) (n : ℕ) :
    (∑ p ∈ n.divisorsAntidiagonal,
      lemma23NuArithmeticFunction χ p.1 * lemma23UpsilonArithmeticFunction χ p.2) =
        if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℂ => f n)
    (lemma23Nu_mul_Upsilon_eq_one χ)
  simpa [ArithmeticFunction.mul_apply, ArithmeticFunction.one_apply] using h

end ZhangLS.Spec
