import ZhangLS.Spec.ShortUpsilonPaperEnergy
import ZhangLS.Spec.Lemma81ActualPolynomialMoments

/-! Actual full primitive-family 2/4/4 estimate. No contour attachment is asserted. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Finset
open scoped Classical

/-- A common mask is part of the coefficients, before a primitive character is chosen. -/
noncomputable def shortUpsilonResidualPolynomial {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) (mask : ℕ → ℂ) (ψ : DirichletCharacter ℂ p) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊lemma23PaperP D^2⌋₊,
    LSeries.term (fun n => mask n*(lemma83Kappa β n-shortUpsilonKappa χ β n)) s n *
      ψ (n : ZMod p)

noncomputable def shortUpsilonSecondMomentConstant : ℝ := (32+Real.pi^2)*(36*3^40)

lemma shortUpsilon_second_constant_pos : 0 < shortUpsilonSecondMomentConstant := by
  unfold shortUpsilonSecondMomentConstant
  positivity

theorem shortUpsilon_actual_residual_second_moment {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 3 ≤ lemma23PaperL D) (hA : NormalizedAssumptionA χ)
    (hAbs : (Real.sqrt (D : ℝ))⁻¹ ≤ lemma23PaperL D^(-2013 : ℤ))
    (β : Fin 3 → ℂ) (hβ : ∀ j, (β j).re = 0)
    (mask : ℕ → ℂ) (hm : ∀ n ∈ Finset.Icc 1 ⌊lemma23PaperP D^2⌋₊, ‖mask n‖ ≤ 1)
    (s : ℂ) (hs : s.re = 1/2) :
    (∑ ψ ∈ lemma33ActualFamily D, ‖shortUpsilonResidualPolynomial χ β mask ψ.2 s‖^2) ≤
      shortUpsilonSecondMomentConstant * lemma23PaperP D^2 * lemma23PaperL D^(-640 : ℤ) := by
  have he := lemma33_actual_second_Dirichlet_mean_bound hL
    (fun n => mask n*(lemma83Kappa β n-shortUpsilonKappa χ β n)) s
  have hpower : 2*s.re = 1 := by rw [hs]; norm_num
  simp only [hpower, Real.rpow_one, div_eq_mul_inv] at he
  have henergy := (shortUpsilon_masked_energy_le χ β _ mask hm).trans
    (shortUpsilon_error_energy_le χ hD (by linarith) hA hAbs β hβ _ le_rfl)
  change (∑ ψ ∈ lemma33ActualFamily D,
    ‖shortUpsilonResidualPolynomial χ β mask ψ.2 s‖^2) ≤ _ at he
  apply (he.trans (mul_le_mul_of_nonneg_left henergy (by positivity))).trans_eq
  unfold shortUpsilonSecondMomentConstant
  ring

/-- Every bounded pair of actual finite polynomials, at every critical-line height.
The squared form has no square roots and keeps all constants explicit. -/
theorem shortUpsilon_actual_trilinear_error_sq {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 3 ≤ lemma23PaperL D) (hA : NormalizedAssumptionA χ)
    (hAbs : (Real.sqrt (D : ℝ))⁻¹ ≤ lemma23PaperL D^(-2013 : ℤ))
    (β : Fin 3 → ℂ) (hβ : ∀ j, (β j).re = 0)
    (mask : ℕ → ℂ) (hm : ∀ n ∈ Finset.Icc 1 ⌊lemma23PaperP D^2⌋₊, ‖mask n‖ ≤ 1)
    (s : ℂ) (hs : s.re = 1/2)
    (B₁ B₂ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (X Y : ℕ) (hX : X ≤ ⌊lemma23PaperP D⌋₊) (hY : Y ≤ ⌊lemma23PaperP D⌋₊)
    (a b : ℕ → ℂ) (ha : ∀ n ∈ Finset.Icc 1 X, ‖a n‖ ≤ B₁)
    (hb : ∀ n ∈ Finset.Icc 1 Y, ‖b n‖ ≤ B₂) :
    (∑ ψ ∈ lemma33ActualFamily D,
      ‖shortUpsilonResidualPolynomial χ β mask ψ.2 s *
        lemma81FiniteCharacterPolynomial X a ψ.2 s *
        lemma81FiniteCharacterPolynomial Y b ψ.2 s‖)^2 ≤
      shortUpsilonSecondMomentConstant * lemma81FourthMomentConstant *
        B₁^2*B₂^2*lemma23PaperP D^4*lemma23PaperL D^(-604 : ℤ) := by
  have hLp : 0 < lemma23PaperL D := by linarith
  have hstrip : |s.re-1/2| ≤ lemma44PaperAlpha D := by
    rw [hs, sub_self, abs_zero]
    exact (lemma44_alpha_pos_le_one hL).1.le
  let C : ℝ := lemma81FourthMomentConstant * lemma23PaperP D^2 * lemma23PaperL D^36
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg lemma81_fourth_moment_constant_pos.le (sq_nonneg _)) (by positivity)
  have hfa : (∑ ψ ∈ lemma33ActualFamily D,
      ‖lemma81FiniteCharacterPolynomial X a ψ.2 s‖^4) ≤ C*(B₁^2)^2 := by
    apply (lemma81_actual_polynomial_fourth_moment hB₁ hL X hX a ha hstrip).trans_eq
    dsimp [C]
    ring
  have hfb : (∑ ψ ∈ lemma33ActualFamily D,
      ‖lemma81FiniteCharacterPolynomial Y b ψ.2 s‖^4) ≤ C*(B₂^2)^2 := by
    apply (lemma81_actual_polynomial_fourth_moment hB₂ hL Y hY b hb hstrip).trans_eq
    dsimp [C]
    ring
  have hprod := lemma81_product_moment_of_fourth (lemma33ActualFamily D)
    (fun ψ => lemma81FiniteCharacterPolynomial X a ψ.2 s)
    (fun ψ => lemma81FiniteCharacterPolynomial Y b ψ.2 s)
    hC (sq_nonneg B₁) (sq_nonneg B₂) hfa hfb
  have hsecond := shortUpsilon_actual_residual_second_moment χ hD hL hA hAbs β hβ mask hm s hs
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (lemma33ActualFamily D)
    (fun ψ => ‖shortUpsilonResidualPolynomial χ β mask ψ.2 s‖)
    (fun ψ => ‖lemma81FiniteCharacterPolynomial X a ψ.2 s *
      lemma81FiniteCharacterPolynomial Y b ψ.2 s‖)
  calc
    _ = (∑ ψ ∈ lemma33ActualFamily D,
        ‖shortUpsilonResidualPolynomial χ β mask ψ.2 s‖ *
          ‖lemma81FiniteCharacterPolynomial X a ψ.2 s *
            lemma81FiniteCharacterPolynomial Y b ψ.2 s‖)^2 := by
      simp only [norm_mul, mul_assoc]
    _ ≤ _ := hcs
    _ ≤ (shortUpsilonSecondMomentConstant*lemma23PaperP D^2*lemma23PaperL D^(-640 : ℤ)) *
        (C*B₁^2*B₂^2) :=
      mul_le_mul hsecond hprod (by positivity)
        (mul_nonneg (mul_nonneg shortUpsilon_second_constant_pos.le (sq_nonneg _))
          (zpow_pos hLp _).le)
    _ = (shortUpsilonSecondMomentConstant*lemma81FourthMomentConstant*B₁^2*B₂^2*
        lemma23PaperP D^4) * (lemma23PaperL D^(-640 : ℤ)*lemma23PaperL D^36) := by
      dsimp [C]
      ring
    _ = _ := by
      congr 1
      simpa only [Int.reduceAdd, zpow_ofNat] using
        (zpow_add₀ hLp.ne' (-640 : ℤ) 36).symm


/-- Linear form of the same full-family estimate, with an explicit absolute constant. -/
theorem shortUpsilon_actual_trilinear_error {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 3 ≤ lemma23PaperL D) (hA : NormalizedAssumptionA χ)
    (hAbs : (Real.sqrt (D : ℝ))⁻¹ ≤ lemma23PaperL D^(-2013 : ℤ))
    (β : Fin 3 → ℂ) (hβ : ∀ j, (β j).re = 0)
    (mask : ℕ → ℂ) (hm : ∀ n ∈ Finset.Icc 1 ⌊lemma23PaperP D^2⌋₊, ‖mask n‖ ≤ 1)
    (s : ℂ) (hs : s.re = 1/2)
    (B₁ B₂ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (X Y : ℕ) (hX : X ≤ ⌊lemma23PaperP D⌋₊) (hY : Y ≤ ⌊lemma23PaperP D⌋₊)
    (a b : ℕ → ℂ) (ha : ∀ n ∈ Finset.Icc 1 X, ‖a n‖ ≤ B₁)
    (hb : ∀ n ∈ Finset.Icc 1 Y, ‖b n‖ ≤ B₂) :
    (∑ ψ ∈ lemma33ActualFamily D,
      ‖shortUpsilonResidualPolynomial χ β mask ψ.2 s *
        lemma81FiniteCharacterPolynomial X a ψ.2 s *
        lemma81FiniteCharacterPolynomial Y b ψ.2 s‖) ≤
      (shortUpsilonSecondMomentConstant+lemma81FourthMomentConstant) *
        B₁*B₂*lemma23PaperP D^2*lemma23PaperL D^(-302 : ℤ) := by
  have hLp : 0 < lemma23PaperL D := by linarith
  have hsecond := shortUpsilon_second_constant_pos.le
  have hfourth := lemma81_fourth_moment_constant_pos.le
  have hsq := shortUpsilon_actual_trilinear_error_sq χ hD hL hA hAbs β hβ mask hm
    s hs B₁ B₂ hB₁ hB₂ X Y hX hY a b ha hb
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  apply hsq.trans
  have hc : shortUpsilonSecondMomentConstant*lemma81FourthMomentConstant ≤
      (shortUpsilonSecondMomentConstant+lemma81FourthMomentConstant)^2 := by
    nlinarith [sq_nonneg shortUpsilonSecondMomentConstant,
      sq_nonneg lemma81FourthMomentConstant,
      mul_nonneg hsecond hfourth]
  have hp : (lemma23PaperL D^(-302 : ℤ))^2 = lemma23PaperL D^(-604 : ℤ) := by
    rw [← zpow_natCast (lemma23PaperL D^(-302 : ℤ)) 2, ← zpow_mul]
    norm_num
  calc
    _ = (shortUpsilonSecondMomentConstant*lemma81FourthMomentConstant) *
        (B₁*B₂*lemma23PaperP D^2*lemma23PaperL D^(-302 : ℤ))^2 := by
      rw [mul_pow, hp]
      ring
    _ ≤ (shortUpsilonSecondMomentConstant+lemma81FourthMomentConstant)^2 *
        (B₁*B₂*lemma23PaperP D^2*lemma23PaperL D^(-302 : ℤ))^2 :=
      mul_le_mul_of_nonneg_right hc (sq_nonneg _)
    _ = _ := by ring

/-- The same bound for the target pairing with a conjugated second polynomial. -/
theorem shortUpsilon_actual_trilinear_error_conjugate {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 3 ≤ lemma23PaperL D) (hA : NormalizedAssumptionA χ)
    (hAbs : (Real.sqrt (D : ℝ))⁻¹ ≤ lemma23PaperL D^(-2013 : ℤ))
    (β : Fin 3 → ℂ) (hβ : ∀ j, (β j).re = 0)
    (mask : ℕ → ℂ) (hm : ∀ n ∈ Finset.Icc 1 ⌊lemma23PaperP D^2⌋₊, ‖mask n‖ ≤ 1)
    (s : ℂ) (hs : s.re = 1/2)
    (B₁ B₂ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (X Y : ℕ) (hX : X ≤ ⌊lemma23PaperP D⌋₊) (hY : Y ≤ ⌊lemma23PaperP D⌋₊)
    (a b : ℕ → ℂ) (ha : ∀ n ∈ Finset.Icc 1 X, ‖a n‖ ≤ B₁)
    (hb : ∀ n ∈ Finset.Icc 1 Y, ‖b n‖ ≤ B₂) :
    (∑ ψ ∈ lemma33ActualFamily D,
      ‖shortUpsilonResidualPolynomial χ β mask ψ.2 s *
        lemma81FiniteCharacterPolynomial X a ψ.2 s *
        star (lemma81FiniteCharacterPolynomial Y b ψ.2 s)‖) ≤
      (shortUpsilonSecondMomentConstant+lemma81FourthMomentConstant) *
        B₁*B₂*lemma23PaperP D^2*lemma23PaperL D^(-302 : ℤ) := by
  simpa only [norm_mul, norm_star] using
    shortUpsilon_actual_trilinear_error χ hD hL hA hAbs β hβ mask hm s hs
      B₁ B₂ hB₁ hB₂ X Y hX hY a b ha hb

end ZhangLS.Spec
