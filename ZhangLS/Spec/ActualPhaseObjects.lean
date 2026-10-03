import ZhangLS.Spec.Lemma81ActualRectangleResidues
import ZhangLS.Spec.Lemma171Target

/-! Actual root-phase objects for the R2 finite contour branch.

The branch is inherited from the original continuous square root Y. No
principal square root, frozen gamma factor, or Dirichlet-series truncation
is used in this module. All polynomials use the original strict finite
cutoff, all zeros the original strict source window.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex ComplexConjugate Set Filter MeasureTheory
open scoped Real Topology Classical
set_option maxHeartbeats 2000000

/-- The exact product of the two genuine root numbers. -/
noncomputable def actualPhaseRoot {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) : ℂ := by
  letI : NeZero (D*p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  exact DirichletCharacter.rootNumber ψ *
    DirichletCharacter.rootNumber (lemma44CharacterTwist χ ψ)

/-- The genuine functional-equation factor of the primitive product twist. -/
noncomputable def actualPhaseTwistZ {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ) : ℂ := by
  letI : NeZero (D*p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  exact lemma23DirichletZ (lemma44CharacterTwist χ ψ) s

/-- Exact archimedean factor; its parity is the parity of the actual character. -/
noncomputable def actualPhaseArch {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  (q : ℂ)^((1/2 : ℂ)-s) *
    (DirichletCharacter.gammaFactor θ⁻¹ (1-s) / DirichletCharacter.gammaFactor θ s)

theorem actualPhase_Z_eq_root_mul_arch {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) (s : ℂ) :
    lemma23DirichletZ θ s = DirichletCharacter.rootNumber θ * actualPhaseArch θ s := by
  unfold lemma23DirichletZ actualPhaseArch
  ring

/-- The inherited three-shift branch, including the original perturbed shifts. -/
noncomputable def actualPhaseBranch (D : ℕ) (c : ℝ) (Y : ℂ → ℂ) (s : ℂ) : ℂ :=
  (Y (s+lemma52PaperBetaOne D c) * Y (s+lemma52PaperBetaTwo D c) *
    Y (s+lemma52PaperBetaThree D c)) / Y s^3

/-- The full continued quotient, deliberately distinct from every finite kappa sum. -/
noncomputable def actualPhaseLQuotient {p : ℕ} [NeZero p]
    (D : ℕ) (c : ℝ) (ψ : DirichletCharacter ℂ p) (s : ℂ) : ℂ :=
  (ψ.LFunction (s+lemma52PaperBetaOne D c) *
    ψ.LFunction (s+lemma52PaperBetaTwo D c) *
    ψ.LFunction (s+lemma52PaperBetaThree D c)) / ψ.LFunction s

/-- Changing the sign of the inherited square root does not change B_beta. -/
theorem actualPhase_branch_neg (D : ℕ) (c : ℝ) (Y : ℂ → ℂ) (s : ℂ) :
    actualPhaseBranch D c (fun z => -Y z) s = actualPhaseBranch D c Y s := by
  unfold actualPhaseBranch
  ring

/-- The exact source residue kernel, retaining the inherited branch multiplier. -/
theorem actualPhase_Ctilde_exact {D p : ℕ} [NeZero p]
    (c : ℝ) (ψ : DirichletCharacter ℂ p) (hψ : ψ.IsPrimitive) (hp : p ≠ 1)
    (Y : ℂ → ℂ) (hY : Lemma23ActualBranch ψ Y) {s : ℂ} (hs : 0 < s.im) :
    lemma81ActualCtilde D c ψ Y s =
      -I * actualPhaseBranch D c Y s * (lemma23DirichletZ ψ s)⁻¹ *
        actualPhaseLQuotient D c ψ s := by
  have hy := lemma52_actual_branch_ne_zero ψ hψ hp Y hY hs
  rw [← hY.2 s hs]
  unfold lemma81ActualCtilde actualPhaseBranch actualPhaseLQuotient
    lemma23DirichletNormalizedM lemma23NormalizedM
  simp only [div_eq_mul_inv, mul_inv_rev]
  field_simp [hy]

/-- The analytic test whose values give C1. -/
noncomputable def actualPhaseCTest {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (a b : ℕ → ℂ) (s : ℂ) : ℂ :=
  actualPhaseRoot χ ψ * (actualPhaseTwistZ χ ψ s)⁻¹ *
    lemma81Polynomial D a ψ s * lemma81Polynomial D b ψ s

/-- The analytic continuation of the T1 test, with conjugated coefficients. -/
noncomputable def actualPhaseTTest {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (a j : ℕ → ℂ) (s : ℂ) : ℂ :=
  actualPhaseRoot χ ψ * lemma81Polynomial D a ψ s *
    lemma81Polynomial D (lemma81ConjugateSequence j) ψ⁻¹ (1-s)

theorem actualPhase_TTest_on_critical_line {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (a j : ℕ → ℂ) {s : ℂ} (hs : s.re = 1/2) :
    actualPhaseTTest χ ψ a j s = actualPhaseRoot χ ψ *
      lemma81Polynomial D a ψ s * conj (lemma81Polynomial D j ψ s) := by
  have he : 1-s = conj s := by
    apply Complex.ext <;> simp [hs]
    <;> ring
  unfold actualPhaseTTest
  rw [he, ← lemma81_polynomial_conjugate]

theorem actualPhase_TTest_analytic {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (a j : ℕ → ℂ) (s : ℂ) : AnalyticAt ℂ (actualPhaseTTest χ ψ a j) s := by
  exact (analyticAt_const.mul ((lemma81_polynomial_differentiable D a ψ).analyticAt s)).mul
    (((lemma81_polynomial_differentiable D (lemma81ConjugateSequence j) ψ⁻¹).analyticAt
      (1-s)).comp (by fun_prop))

theorem actualPhase_CTest_analytic {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hL : 3 ≤ lemma23PaperL D) (hψ : Lemma23InPsi (D := D) ψ)
    (a b : ℕ → ℂ) {s : ℂ} (hs : 0 < s.im) :
    AnalyticAt ℂ (actualPhaseCTest χ ψ a b) s := by
  letI : NeZero (D*p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  have htw := lemma44CharacterTwist_isPrimitive χ ψ hψ.2.1
    (lemma44_family_coprime χ ψ hL hψ)
  have hDp : D*p ≠ 1 := by
    intro he
    have hdvd : p ∣ 1 := he ▸ p.dvd_mul_left D
    exact hψ.1.ne_one (Nat.eq_one_of_dvd_one hdvd)
  have hz : AnalyticAt ℂ (actualPhaseTwistZ χ ψ) s := by
    have hd : DifferentiableOn ℂ (lemma23DirichletZ (lemma44CharacterTwist χ ψ))
        {z : ℂ | 0 < z.im} := by
      intro z hz
      exact (lemma23DirichletZ_differentiableAt_of_im_ne_zero
        (lemma44CharacterTwist χ ψ) hz.ne').differentiableWithinAt
    exact (hd.analyticOnNhd UpperHalfPlane.isOpen_upperHalfPlaneSet) s hs
  have hn : actualPhaseTwistZ χ ψ s ≠ 0 :=
    lemma23DirichletZ_ne_zero_of_im_pos (lemma44CharacterTwist χ ψ) htw hDp hs
  exact ((analyticAt_const.mul (hz.inv hn)).mul
    ((lemma81_polynomial_differentiable D a ψ).analyticAt s)).mul
    ((lemma81_polynomial_differentiable D b ψ).analyticAt s)

/-- The actual test numerator; the denominator will be the original M=Y L. -/
noncomputable def actualPhaseNumerator {p : ℕ} [NeZero p]
    (D : ℕ) (c : ℝ) (ψ : DirichletCharacter ℂ p) (Y f : ℂ → ℂ) (s : ℂ) : ℂ :=
  -I * (lemma23DirichletNormalizedM ψ Y (s+lemma52PaperBetaOne D c) *
    lemma23DirichletNormalizedM ψ Y (s+lemma52PaperBetaTwo D c) *
    lemma23DirichletNormalizedM ψ Y (s+lemma52PaperBetaThree D c)) * f s * lemma81Omega D s

noncomputable def actualPhaseIntegrand {p : ℕ} [NeZero p]
    (D : ℕ) (c : ℝ) (ψ : DirichletCharacter ℂ p) (Y f : ℂ → ℂ) (s : ℂ) : ℂ :=
  lemma81ActualCtilde D c ψ Y s * f s * lemma81Omega D s

noncomputable def actualPhaseResidue {p : ℕ} [NeZero p]
    (D : ℕ) (c : ℝ) (ψ : DirichletCharacter ℂ p) (Y f : ℂ → ℂ) (ρ : ℂ) : ℂ :=
  lemma23ActualCoefficient ψ Y D c ρ * f ρ * lemma81Omega D ρ

theorem actualPhase_integrand_eq_quotient {p : ℕ} [NeZero p]
    (D : ℕ) (c : ℝ) (ψ : DirichletCharacter ℂ p) (Y f : ℂ → ℂ) (s : ℂ) :
    actualPhaseIntegrand D c ψ Y f s =
      actualPhaseNumerator D c ψ Y f s / lemma23DirichletNormalizedM ψ Y s := by
  unfold actualPhaseIntegrand actualPhaseNumerator lemma81ActualCtilde
  ring

theorem actualPhase_numerator_div_deriv {p : ℕ} [NeZero p]
    (D : ℕ) (c : ℝ) (ψ : DirichletCharacter ℂ p) (Y f : ℂ → ℂ) (ρ : ℂ) :
    actualPhaseNumerator D c ψ Y f ρ / deriv (lemma23DirichletNormalizedM ψ Y) ρ =
      actualPhaseResidue D c ψ Y f ρ := by
  unfold actualPhaseNumerator actualPhaseResidue lemma23ActualCoefficient
    lemma23ComplexCoefficient criticalLinePoint lemma52PaperBetaOne lemma52PaperBetaTwo
    lemma52PaperBetaThree
  ring

theorem actualPhase_numerator_analytic {D p : ℕ} [NeZero p]
    (c : ℝ) (ψ : DirichletCharacter ℂ p) (hψ : ψ.IsPrimitive) (hp : p ≠ 1)
    (Y f : ℂ → ℂ) (hY : Lemma23ActualBranch ψ Y) {s : ℂ} (hf : AnalyticAt ℂ f s)
    (h₁ : 0 < s.im+lemma23PaperOffsetOne D c)
    (h₂ : 0 < s.im+lemma23PaperOffsetTwo D c)
    (h₃ : 0 < s.im+lemma23PaperOffsetThree D c) :
    AnalyticAt ℂ (actualPhaseNumerator D c ψ Y f) s := by
  have hM := lemma81_actual_M_analytic ψ hψ hp Y hY
  have hM₁ : AnalyticAt ℂ (fun z => lemma23DirichletNormalizedM ψ Y
      (z+lemma52PaperBetaOne D c)) s :=
    (hM _ (by simpa [lemma52PaperBetaOne] using h₁)).comp (by fun_prop)
  have hM₂ : AnalyticAt ℂ (fun z => lemma23DirichletNormalizedM ψ Y
      (z+lemma52PaperBetaTwo D c)) s :=
    (hM _ (by simpa [lemma52PaperBetaTwo] using h₂)).comp (by fun_prop)
  have hM₃ : AnalyticAt ℂ (fun z => lemma23DirichletNormalizedM ψ Y
      (z+lemma52PaperBetaThree D c)) s :=
    (hM _ (by simpa [lemma52PaperBetaThree] using h₃)).comp (by fun_prop)
  exact ((analyticAt_const.mul ((hM₁.mul hM₂).mul hM₃)).mul hf).mul
    ((lemma81_omega_differentiable D).analyticAt s)

end ZhangLS.Spec
