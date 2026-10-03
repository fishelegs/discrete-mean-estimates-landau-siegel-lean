import ZhangLS.Spec.ActualPhaseObjects

/-! Exact phase transforms before truncation or character completion.
Every quotient in this file is a quotient of the genuine continued
L-functions. No finite kappa polynomial is identified with one.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex ComplexConjugate Set
open scoped Real Topology Classical
set_option maxHeartbeats 2000000

/-- Exact archimedean factor of chi times psi at conductor D p. -/
noncomputable def actualPhaseTwistArch {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ) : ℂ := by
  letI : NeZero (D*p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  exact actualPhaseArch (lemma44CharacterTwist χ ψ) s

noncomputable def actualPhaseTwistRoot {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) : ℂ := by
  letI : NeZero (D*p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  exact DirichletCharacter.rootNumber (lemma44CharacterTwist χ ψ)

theorem actualPhase_twist_Z_eq_root_arch {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ) :
    actualPhaseTwistZ χ ψ s = actualPhaseTwistRoot χ ψ * actualPhaseTwistArch χ ψ s := by
  letI : NeZero (D*p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  exact actualPhase_Z_eq_root_mul_arch (lemma44CharacterTwist χ ψ) s

/-- The exact shifted gamma ratio, with root numbers still cancellable algebraically. -/
noncomputable def actualPhaseShiftRatio {p : ℕ} [NeZero p]
    (D : ℕ) (c : ℝ) (ψ : DirichletCharacter ℂ p) (s : ℂ) : ℂ :=
  (lemma23DirichletZ ψ (s+lemma52PaperBetaOne D c) *
    lemma23DirichletZ ψ (s+lemma52PaperBetaTwo D c) *
    lemma23DirichletZ ψ (s+lemma52PaperBetaThree D c)) / (lemma23DirichletZ ψ s)^3

theorem actualPhase_branch_square {D p : ℕ} [NeZero p]
    (c : ℝ) (ψ : DirichletCharacter ℂ p) (Y : ℂ → ℂ)
    (hY : Lemma23ActualBranch ψ Y) {s : ℂ} (hs : 0 < s.im)
    (h₁ : 0 < (s+lemma52PaperBetaOne D c).im)
    (h₂ : 0 < (s+lemma52PaperBetaTwo D c).im)
    (h₃ : 0 < (s+lemma52PaperBetaThree D c).im) :
    actualPhaseBranch D c Y s ^ 2 = (actualPhaseShiftRatio D c ψ s)⁻¹ := by
  have he : actualPhaseBranch D c Y s ^ 2 =
      (Y (s+lemma52PaperBetaOne D c)^2 * Y (s+lemma52PaperBetaTwo D c)^2 *
        Y (s+lemma52PaperBetaThree D c)^2) / (Y s^2)^3 := by
    unfold actualPhaseBranch
    ring
  rw [he,hY.2 _ h₁,hY.2 _ h₂,hY.2 _ h₃,hY.2 _ hs]
  simp only [actualPhaseShiftRatio,div_eq_mul_inv,mul_inv_rev,inv_pow,inv_inv]
  ring

/-- The shifted ratio has no root-number dependence after exact cancellation. -/
theorem actualPhase_shift_ratio_arch {D p : ℕ} [NeZero p]
    (c : ℝ) (ψ : DirichletCharacter ℂ p) (hψ : ψ.IsPrimitive) (hp : p ≠ 1) (s : ℂ) :
    actualPhaseShiftRatio D c ψ s =
      (actualPhaseArch ψ (s+lemma52PaperBetaOne D c) *
        actualPhaseArch ψ (s+lemma52PaperBetaTwo D c) *
        actualPhaseArch ψ (s+lemma52PaperBetaThree D c)) / actualPhaseArch ψ s^3 := by
  have hr : DirichletCharacter.rootNumber ψ ≠ 0 := by
    exact norm_ne_zero_iff.mp (by rw [lemma23_rootNumber_norm_eq_one ψ hψ hp]; norm_num)
  simp only [actualPhaseShiftRatio,actualPhase_Z_eq_root_mul_arch,div_eq_mul_inv,
    mul_inv_rev,mul_pow]
  field_simp [hr]
  <;> ring

/-- Exact dual continued quotient, with opposite shifts and inverse character. -/
noncomputable def actualPhaseDualLQuotient {p : ℕ} [NeZero p]
    (D : ℕ) (c : ℝ) (ψ : DirichletCharacter ℂ p) (s : ℂ) : ℂ :=
  (ψ⁻¹.LFunction (1-s-lemma52PaperBetaOne D c) *
    ψ⁻¹.LFunction (1-s-lemma52PaperBetaTwo D c) *
    ψ⁻¹.LFunction (1-s-lemma52PaperBetaThree D c)) / ψ⁻¹.LFunction (1-s)

theorem actualPhase_functional_equation_at {p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : ψ.IsPrimitive) (hp : p ≠ 1)
    {s : ℂ} (hs : 0 < s.im) :
    ψ.LFunction s = lemma23DirichletZ ψ s * ψ⁻¹.LFunction (1-s) := by
  apply lemma23_dirichletLFunction_functional_equation ψ hψ hp
  · exact lemma23_gammaFactor_ne_zero_of_im_ne_zero ψ hs.ne'
  · exact lemma23_gammaFactor_ne_zero_of_im_ne_zero ψ⁻¹ (by simpa using hs.ne')

/-- All four functional equations are applied before simplifying the phase. -/
theorem actualPhase_quotient_functional_equation {D p : ℕ} [NeZero p]
    (c : ℝ) (ψ : DirichletCharacter ℂ p) (hψ : ψ.IsPrimitive) (hp : p ≠ 1)
    {s : ℂ} (hs : 0 < s.im)
    (h₁ : 0 < (s+lemma52PaperBetaOne D c).im)
    (h₂ : 0 < (s+lemma52PaperBetaTwo D c).im)
    (h₃ : 0 < (s+lemma52PaperBetaThree D c).im) :
    actualPhaseLQuotient D c ψ s = (lemma23DirichletZ ψ s)^2 *
      actualPhaseShiftRatio D c ψ s * actualPhaseDualLQuotient D c ψ s := by
  have hz := lemma23DirichletZ_ne_zero_of_im_pos ψ hψ hp hs
  unfold actualPhaseLQuotient
  rw [actualPhase_functional_equation_at ψ hψ hp h₁,
    actualPhase_functional_equation_at ψ hψ hp h₂,
    actualPhase_functional_equation_at ψ hψ hp h₃,
    actualPhase_functional_equation_at ψ hψ hp hs]
  have he (β : ℂ) : 1-(s+β) = 1-s-β := by ring
  simp only [he,actualPhaseShiftRatio,actualPhaseDualLQuotient,div_eq_mul_inv,mul_inv_rev]
  field_simp [hz]
  <;> ring

/-- Exact left residue kernel, retaining the inverse inherited branch. -/
theorem actualPhase_Ctilde_dual {D p : ℕ} [NeZero p]
    (c : ℝ) (ψ : DirichletCharacter ℂ p) (hψ : ψ.IsPrimitive) (hp : p ≠ 1)
    (Y : ℂ → ℂ) (hY : Lemma23ActualBranch ψ Y) {s : ℂ} (hs : 0 < s.im)
    (h₁ : 0 < (s+lemma52PaperBetaOne D c).im)
    (h₂ : 0 < (s+lemma52PaperBetaTwo D c).im)
    (h₃ : 0 < (s+lemma52PaperBetaThree D c).im) :
    lemma81ActualCtilde D c ψ Y s =
      -I * (actualPhaseBranch D c Y s)⁻¹ * lemma23DirichletZ ψ s *
        actualPhaseDualLQuotient D c ψ s := by
  have hz := lemma23DirichletZ_ne_zero_of_im_pos ψ hψ hp hs
  have hb : actualPhaseBranch D c Y s ≠ 0 := by
    unfold actualPhaseBranch
    exact div_ne_zero
      (mul_ne_zero (mul_ne_zero
        (lemma52_actual_branch_ne_zero ψ hψ hp Y hY h₁)
        (lemma52_actual_branch_ne_zero ψ hψ hp Y hY h₂))
        (lemma52_actual_branch_ne_zero ψ hψ hp Y hY h₃))
      (pow_ne_zero _ (lemma52_actual_branch_ne_zero ψ hψ hp Y hY hs))
  have he : actualPhaseShiftRatio D c ψ s = (actualPhaseBranch D c Y s)^(-2 : ℤ) := by
    have hh := congrArg Inv.inv (actualPhase_branch_square c ψ Y hY hs h₁ h₂ h₃)
    simpa only [inv_inv,zpow_neg,pow_two,zpow_ofNat] using hh.symm
  rw [actualPhase_Ctilde_exact c ψ hψ hp Y hY hs,
    actualPhase_quotient_functional_equation c ψ hψ hp hs h₁ h₂ h₃,he]
  simp only [zpow_neg,zpow_ofNat]
  field_simp [hz,hb]
  <;> ring


theorem actualPhase_root_norm {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hL : 3 ≤ lemma23PaperL D) (hψ : Lemma23InPsi (D := D) ψ) :
    ‖actualPhaseRoot χ ψ‖ = 1 := by
  letI : NeZero (D*p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  have htw := lemma44CharacterTwist_isPrimitive χ ψ hψ.2.1
    (lemma44_family_coprime χ ψ hL hψ)
  have hDp : D*p ≠ 1 := by
    intro he
    have hdvd : p ∣ 1 := he ▸ p.dvd_mul_left D
    exact hψ.1.ne_one (Nat.eq_one_of_dvd_one hdvd)
  exact (show ‖DirichletCharacter.rootNumber ψ *
      DirichletCharacter.rootNumber (lemma44CharacterTwist χ ψ)‖ = 1 by
    rw [norm_mul,lemma23_rootNumber_norm_eq_one ψ hψ.2.1 hψ.1.ne_one,
      lemma23_rootNumber_norm_eq_one (lemma44CharacterTwist χ ψ) htw hDp,one_mul])

theorem actualPhase_root_cancel {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hL : 3 ≤ lemma23PaperL D) (hψ : Lemma23InPsi (D := D) ψ) (s : ℂ) :
    actualPhaseRoot χ ψ * (lemma23DirichletZ ψ s)⁻¹ * (actualPhaseTwistZ χ ψ s)⁻¹ =
      (actualPhaseArch ψ s * actualPhaseTwistArch χ ψ s)⁻¹ := by
  have hr : actualPhaseRoot χ ψ ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [actualPhase_root_norm χ ψ hL hψ]; norm_num)
  have hr1 : DirichletCharacter.rootNumber ψ ≠ 0 := (mul_ne_zero_iff.mp hr).1
  have hr2 : actualPhaseTwistRoot χ ψ ≠ 0 := (mul_ne_zero_iff.mp hr).2
  rw [actualPhase_Z_eq_root_mul_arch,actualPhase_twist_Z_eq_root_arch]
  change (DirichletCharacter.rootNumber ψ * actualPhaseTwistRoot χ ψ) * _ * _ = _
  calc
    _ = (DirichletCharacter.rootNumber ψ * (DirichletCharacter.rootNumber ψ)⁻¹) *
        (actualPhaseTwistRoot χ ψ * (actualPhaseTwistRoot χ ψ)⁻¹) *
        (actualPhaseArch ψ s * actualPhaseTwistArch χ ψ s)⁻¹ := by
      simp only [mul_inv_rev]
      ring
    _ = _ := by rw [mul_inv_cancel₀ hr1,mul_inv_cancel₀ hr2,one_mul,one_mul]

/-- C1's exact right kernel: both roots cancel, but both gamma factors remain. -/
theorem actualPhase_C_right_integrand {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (c : ℝ) (ψ : DirichletCharacter ℂ p)
    (hL : 3 ≤ lemma23PaperL D) (hψ : Lemma23InPsi (D := D) ψ)
    (Y : ℂ → ℂ) (hY : Lemma23ActualBranch ψ Y) (a b : ℕ → ℂ)
    {s : ℂ} (hs : 0 < s.im) :
    actualPhaseIntegrand D c ψ Y (actualPhaseCTest χ ψ a b) s =
      -I * actualPhaseBranch D c Y s *
        (actualPhaseArch ψ s * actualPhaseTwistArch χ ψ s)⁻¹ *
        actualPhaseLQuotient D c ψ s * lemma81Polynomial D a ψ s *
        lemma81Polynomial D b ψ s * lemma81Omega D s := by
  rw [actualPhaseIntegrand,actualPhase_Ctilde_exact c ψ hψ.2.1 hψ.1.ne_one Y hY hs]
  unfold actualPhaseCTest
  have hh := actualPhase_root_cancel χ ψ hL hψ s
  calc
    _ = -I * actualPhaseBranch D c Y s *
        (actualPhaseRoot χ ψ * (lemma23DirichletZ ψ s)⁻¹ * (actualPhaseTwistZ χ ψ s)⁻¹) *
        actualPhaseLQuotient D c ψ s * lemma81Polynomial D a ψ s *
        lemma81Polynomial D b ψ s * lemma81Omega D s := by ring
    _ = _ := by rw [hh]

/-- C1's left kernel keeps the exact twist ratio, full root phase and dual quotient. -/
theorem actualPhase_C_left_integrand {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (c : ℝ) (ψ : DirichletCharacter ℂ p)
    (hψ : ψ.IsPrimitive) (hp : p ≠ 1) (Y : ℂ → ℂ) (hY : Lemma23ActualBranch ψ Y)
    (a b : ℕ → ℂ) {s : ℂ} (hs : 0 < s.im)
    (h₁ : 0 < (s+lemma52PaperBetaOne D c).im)
    (h₂ : 0 < (s+lemma52PaperBetaTwo D c).im)
    (h₃ : 0 < (s+lemma52PaperBetaThree D c).im) :
    actualPhaseIntegrand D c ψ Y (actualPhaseCTest χ ψ a b) s =
      -I * (actualPhaseBranch D c Y s)⁻¹ * actualPhaseRoot χ ψ *
        (lemma23DirichletZ ψ s / actualPhaseTwistZ χ ψ s) *
        actualPhaseDualLQuotient D c ψ s * lemma81Polynomial D a ψ s *
        lemma81Polynomial D b ψ s * lemma81Omega D s := by
  rw [actualPhaseIntegrand,actualPhase_Ctilde_dual c ψ hψ hp Y hY hs h₁ h₂ h₃]
  unfold actualPhaseCTest
  ring

/-- T1's exact right kernel contains the twist root and one inverse gamma factor. -/
theorem actualPhase_T_right_integrand {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (c : ℝ) (ψ : DirichletCharacter ℂ p)
    (hψ : ψ.IsPrimitive) (hp : p ≠ 1) (Y : ℂ → ℂ) (hY : Lemma23ActualBranch ψ Y)
    (a j : ℕ → ℂ) {s : ℂ} (hs : 0 < s.im) :
    actualPhaseIntegrand D c ψ Y (actualPhaseTTest χ ψ a j) s =
      -I * actualPhaseBranch D c Y s * actualPhaseTwistRoot χ ψ *
        (actualPhaseArch ψ s)⁻¹ * actualPhaseLQuotient D c ψ s *
        lemma81Polynomial D a ψ s *
        lemma81Polynomial D (lemma81ConjugateSequence j) ψ⁻¹ (1-s) * lemma81Omega D s := by
  have hr : DirichletCharacter.rootNumber ψ ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [lemma23_rootNumber_norm_eq_one ψ hψ hp]; norm_num)
  have hc : actualPhaseRoot χ ψ * (lemma23DirichletZ ψ s)⁻¹ =
      actualPhaseTwistRoot χ ψ * (actualPhaseArch ψ s)⁻¹ := by
    rw [actualPhase_Z_eq_root_mul_arch]
    change (DirichletCharacter.rootNumber ψ * actualPhaseTwistRoot χ ψ) * _ = _
    calc
      _ = (DirichletCharacter.rootNumber ψ * (DirichletCharacter.rootNumber ψ)⁻¹) *
          actualPhaseTwistRoot χ ψ * (actualPhaseArch ψ s)⁻¹ := by
        rw [mul_inv_rev]; ring
      _ = _ := by rw [mul_inv_cancel₀ hr,one_mul]
  rw [actualPhaseIntegrand,actualPhase_Ctilde_exact c ψ hψ hp Y hY hs]
  unfold actualPhaseTTest
  calc
    _ = -I * actualPhaseBranch D c Y s *
        (actualPhaseRoot χ ψ * (lemma23DirichletZ ψ s)⁻¹) * actualPhaseLQuotient D c ψ s *
        lemma81Polynomial D a ψ s *
        lemma81Polynomial D (lemma81ConjugateSequence j) ψ⁻¹ (1-s) * lemma81Omega D s := by ring
    _ = _ := by rw [hc]; ring

/-- T1's left kernel has the full root phase times the psi root and gamma factor. -/
theorem actualPhase_T_left_integrand {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (c : ℝ) (ψ : DirichletCharacter ℂ p)
    (hψ : ψ.IsPrimitive) (hp : p ≠ 1) (Y : ℂ → ℂ) (hY : Lemma23ActualBranch ψ Y)
    (a j : ℕ → ℂ) {s : ℂ} (hs : 0 < s.im)
    (h₁ : 0 < (s+lemma52PaperBetaOne D c).im)
    (h₂ : 0 < (s+lemma52PaperBetaTwo D c).im)
    (h₃ : 0 < (s+lemma52PaperBetaThree D c).im) :
    actualPhaseIntegrand D c ψ Y (actualPhaseTTest χ ψ a j) s =
      -I * (actualPhaseBranch D c Y s)⁻¹ * actualPhaseRoot χ ψ *
        DirichletCharacter.rootNumber ψ * actualPhaseArch ψ s *
        actualPhaseDualLQuotient D c ψ s * lemma81Polynomial D a ψ s *
        lemma81Polynomial D (lemma81ConjugateSequence j) ψ⁻¹ (1-s) * lemma81Omega D s := by
  rw [actualPhaseIntegrand,actualPhase_Ctilde_dual c ψ hψ hp Y hY hs h₁ h₂ h₃,
    actualPhase_Z_eq_root_mul_arch]
  unfold actualPhaseTTest
  ring

end ZhangLS.Spec
