import ZhangLS.Spec.Lemma44CharacterProduct
import ZhangLS.Spec.Lemma44DirichletFactorEstimates
import ZhangLS.Spec.Lemma23GoodSet

/-!
# The actual Section 4 Gamma factor and estimate (4.6)

The twist `χψ` is constructed at modulus `D*p`; coprimality and primitivity
are derived from genuine family membership. High-height Gamma estimates
then give the paper's `-2 log P + O(L)` logarithmic derivative, uniformly on
the entire wide strip preceding Lemma 4.4.
-/

namespace ZhangLS.Spec

open Complex

set_option maxHeartbeats 1000000

/-- The wide strip used in (4.5)--(4.6), before restricting to `Ω₃`. -/
def Lemma44InGammaRegion (D : ℕ) (s : ℂ) : Prop :=
  |s.re - 1 / 2| ≤ 100 ∧
    |s.im - (lemma23PaperCenter D).im| ≤ lemma23PaperL D ^ 405 + 3

/-- `P` exceeds `D`, so every prime in the paper's family is coprime to `D`. -/
theorem lemma44_family_coprime {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hL : 3 ≤ lemma23PaperL D) (hψ : Lemma23InPsi (D := D) ψ) : D.Coprime p := by
  have hL1 : 1 ≤ lemma23PaperL D := by linarith
  have hL2 : lemma23PaperL D ^ 2 ≤ lemma23PaperL D ^ 9 :=
    pow_le_pow_right₀ hL1 (by norm_num)
  have hexp : (D : ℝ) < lemma23PaperP D := by
    have hD : (0 : ℝ) < D := by exact_mod_cast χ.modulus_pos
    rw [← Real.exp_log hD]
    apply Real.exp_lt_exp.mpr
    change lemma23PaperL D < lemma23PaperL D ^ 9
    nlinarith
  have hDp : D < p := by exact_mod_cast hexp.trans hψ.2.2.1
  exact (Nat.coprime_of_lt_prime χ.modulus_ne_zero hDp hψ.1).symm

/-- The precise paper product factor, using the actual primitive twist. -/
noncomputable def lemma44ActualZtilde {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ) : ℂ := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  exact lemma44ProductZ ψ (lemma44CharacterTwist χ ψ) s

/-- All points of the wide paper strip meet the quantitative high-height hypotheses. -/
theorem lemma44_gamma_region_height {D : ℕ} {s : ℂ}
    (hL : 3 ≤ lemma23PaperL D) (hs : Lemma44InGammaRegion D s) :
    24 ≤ |s.im| ∧ |s.re| + 2 ≤ |s.im| / 4 ∧
      Real.log (3 * |s.im|) ≤ 550 * lemma23PaperL D := by
  let L := lemma23PaperL D
  have hL3 : 3 ≤ L := hL
  have hL1 : 1 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  have hpow : L ^ 405 ≤ L ^ 519 := pow_le_pow_right₀ hL1 (by norm_num)
  have hpow3 : 3 ≤ L ^ 519 := (show L ≤ L ^ 519 from le_self_pow₀ hL1 (by norm_num))
    |>.trans' hL3
  have hpow729 : 729 ≤ L ^ 519 := by
    have h₆ : (3 : ℝ) ^ 6 ≤ L ^ 6 := pow_le_pow_left₀ (by norm_num) hL3 6
    have h₆' : L ^ 6 ≤ L ^ 519 := pow_le_pow_right₀ hL1 (by norm_num)
    norm_num at h₆
    exact h₆.trans h₆'
  have him : |s.im - 2 * Real.pi * L ^ 519| ≤ L ^ 405 + 3 := hs.2
  have himlo : L ^ 519 ≤ s.im := by
    have h := (abs_le.mp him).1
    have hpi := Real.one_le_pi_div_two
    nlinarith
  have himhi : s.im ≤ 10 * L ^ 519 := by
    have h := (abs_le.mp him).2
    nlinarith [Real.pi_le_four]
  have hspos : 0 ≤ s.im := by linarith
  rw [abs_of_nonneg hspos]
  have hre : |s.re| ≤ 101 := by
    have h := abs_add_le (s.re - 1 / 2) (1 / 2 : ℝ)
    norm_num at h
    have hreal := hs.1
    linarith
  refine ⟨by linarith, by linarith, ?_⟩
  have htpos : 0 < 3 * s.im := by linarith
  calc
    Real.log (3 * s.im) ≤ Real.log (30 * L ^ 519) :=
      Real.log_le_log htpos (by linarith)
    _ = Real.log 30 + 519 * Real.log L := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      norm_num
    _ ≤ 550 * L := by
      have hlogL := Real.log_le_self hLpos.le
      have hlog30 := Real.log_le_self (by norm_num : (0 : ℝ) ≤ 30)
      nlinarith

/-- The conductor logarithm differs from `log P` by at most a fixed constant. -/
theorem lemma44_family_log_bound {D p : ℕ}
    (hL : 3 ≤ lemma23PaperL D) (ψ : DirichletCharacter ℂ p)
    (hψ : Lemma23InPsi (D := D) ψ) :
    0 ≤ Real.log (p : ℝ) - Real.log (lemma23PaperP D) ∧
      Real.log (p : ℝ) - Real.log (lemma23PaperP D) ≤ 1 := by
  have hP : 0 < lemma23PaperP D := Real.exp_pos _
  have hp : (0 : ℝ) < p := hP.trans hψ.2.2.1
  have hpow : lemma23PaperL D ^ (-68 : ℤ) ≤ 1 := by
    rw [zpow_neg]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith : 1 ≤ lemma23PaperL D))
  have hphi : (p : ℝ) ≤ 2 * lemma23PaperP D := by
    have h := hψ.2.2.2
    nlinarith
  have hlo := Real.log_le_log hP hψ.2.2.1.le
  have hhi := Real.log_le_log hp hphi
  rw [Real.log_mul (by norm_num) hP.ne'] at hhi
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  constructor <;> linarith

/-- Paper equation (4.6), with an explicit absolute constant and genuine family inputs.
No Gamma or twist-primitivity estimate is assumed. -/
theorem lemma44_equation46 {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hL : 3 ≤ lemma23PaperL D) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hs : Lemma44InGammaRegion D s) :
    ‖logDeriv (lemma44ActualZtilde χ ψ) s +
      ((2 * Real.log (lemma23PaperP D) : ℝ) : ℂ)‖ ≤ 60000 * lemma23PaperL D := by
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  have hpne : p ≠ 1 := hψ.1.ne_one
  have hDpne : D * p ≠ 1 := by
    intro h
    exact hpne (Nat.dvd_one.mp (h ▸ Nat.dvd_mul_left p D))
  have htwist := lemma44CharacterTwist_isPrimitive χ ψ hψ.2.1
    (lemma44_family_coprime χ ψ hL hψ)
  have hheight := lemma44_gamma_region_height hL hs
  have hfactor := lemma44_productZ_logDeriv_bound ψ (lemma44CharacterTwist χ ψ)
    hψ.2.1 htwist hpne hDpne hheight.1 hheight.2.1
  change ‖logDeriv (lemma44ActualZtilde χ ψ) s + Complex.log (p : ℂ) +
    Complex.log ((D * p : ℕ) : ℂ)‖ ≤ _ at hfactor
  have hπ : ‖Complex.log (Real.pi : ℂ)‖ ≤ 4 := by
    rw [← Complex.ofReal_log Real.pi_pos.le, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by linarith [Real.one_le_pi_div_two]))]
    exact (Real.log_le_self Real.pi_pos.le).trans Real.pi_le_four
  have hfactor' : ‖logDeriv (lemma44ActualZtilde χ ψ) s + Complex.log (p : ℂ) +
      Complex.log ((D * p : ℕ) : ℂ)‖ ≤ 59000 * lemma23PaperL D := by
    apply hfactor.trans
    nlinarith [hheight.2.2, Real.pi_le_four]
  have hlogDp : Complex.log ((D * p : ℕ) : ℂ) =
      ((lemma23PaperL D + Real.log (p : ℝ) : ℝ) : ℂ) := by
    rw [← Complex.natCast_log, Nat.cast_mul, Real.log_mul
      (by exact_mod_cast χ.modulus_ne_zero) (by exact_mod_cast NeZero.ne p)]
    rfl
  have hlogp : Complex.log (p : ℂ) = ((Real.log (p : ℝ) : ℝ) : ℂ) :=
    (Complex.natCast_log (n := p)).symm
  have hlogbounds := lemma44_family_log_bound hL ψ hψ
  let E : ℝ := lemma23PaperL D + 2 *
    (Real.log (p : ℝ) - Real.log (lemma23PaperP D))
  have hE : 0 ≤ E ∧ E ≤ lemma23PaperL D + 2 := by dsimp [E]; constructor <;> linarith
  have heq : logDeriv (lemma44ActualZtilde χ ψ) s +
      ((2 * Real.log (lemma23PaperP D) : ℝ) : ℂ) =
      (logDeriv (lemma44ActualZtilde χ ψ) s + Complex.log (p : ℂ) +
        Complex.log ((D * p : ℕ) : ℂ)) - (E : ℂ) := by
    rw [hlogDp, hlogp]
    dsimp [E]
    push_cast
    ring
  rw [heq]
  have hnormE : ‖(E : ℂ)‖ ≤ lemma23PaperL D + 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hE.1]
    exact hE.2
  exact (norm_sub_le _ _).trans (by linarith)

/-- The actual product functional equation (4.4); twist primitivity is discharged. -/
theorem lemma44_equation44 {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hL : 3 ≤ lemma23PaperL D) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (him : 0 < s.im) :
    letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    DirichletCharacter.LFunction ψ s *
        DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) s =
      lemma44ActualZtilde χ ψ s *
        (DirichletCharacter.LFunction ψ⁻¹ (1 - s) *
          DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ)⁻¹ (1 - s)) := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  have hpne : p ≠ 1 := hψ.1.ne_one
  have hDpne : D * p ≠ 1 := by
    intro h
    exact hpne (Nat.dvd_one.mp (h ▸ Nat.dvd_mul_left p D))
  have htwist := lemma44CharacterTwist_isPrimitive χ ψ hψ.2.1
    (lemma44_family_coprime χ ψ hL hψ)
  rw [lemma23_dirichletLFunction_functional_equation ψ hψ.2.1 hpne
    (lemma23_gammaFactor_ne_zero_of_im_ne_zero ψ him.ne')
    (lemma23_gammaFactor_ne_zero_of_im_ne_zero ψ⁻¹ (by simpa using neg_ne_zero.mpr him.ne')),
    lemma23_dirichletLFunction_functional_equation (lemma44CharacterTwist χ ψ) htwist hDpne
      (lemma23_gammaFactor_ne_zero_of_im_ne_zero _ him.ne')
      (lemma23_gammaFactor_ne_zero_of_im_ne_zero _ (by simpa using neg_ne_zero.mpr him.ne'))]
  simp only [lemma44ActualZtilde, lemma44ProductZ]
  ring

/-- Critical-line unit modulus for the exact product factor. -/
theorem lemma44ActualZtilde_norm_eq_one {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hL : 3 ≤ lemma23PaperL D) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hs : s.re = 1 / 2) : ‖lemma44ActualZtilde χ ψ s‖ = 1 := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  have hpne : p ≠ 1 := hψ.1.ne_one
  have hDpne : D * p ≠ 1 := by
    intro h
    exact hpne (Nat.dvd_one.mp (h ▸ Nat.dvd_mul_left p D))
  have htwist := lemma44CharacterTwist_isPrimitive χ ψ hψ.2.1
    (lemma44_family_coprime χ ψ hL hψ)
  simp only [lemma44ActualZtilde, lemma44ProductZ, norm_mul,
    lemma23DirichletZ_norm_eq_one_on_critical_line ψ hψ.2.1 hpne hs,
    lemma23DirichletZ_norm_eq_one_on_critical_line (lemma44CharacterTwist χ ψ) htwist hDpne hs,
    mul_one]

end ZhangLS.Spec
