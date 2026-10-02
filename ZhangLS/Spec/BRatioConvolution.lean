import ZhangLS.Spec.BProductBridge
import ZhangLS.Spec.Lemma152Definitions

set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical

/-- Exact shift identity for the actual power coefficient, including n=0. -/
lemma b_power_twist_term {p : ℕ} (ψ : DirichletCharacter ℂ p) (β s : ℂ) (n : ℕ) :
    LSeries.term (fun n : ℕ => ψ (n : ZMod p)*lemma83PowerCoefficient β n) s n =
      LSeries.term (fun n : ℕ => ψ (n : ZMod p)) (s+β) n := by
  by_cases hn : n = 0
  · subst n; simp
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [LSeries.term_of_ne_zero hn,LSeries.term_of_ne_zero hn]
  simp only [lemma83PowerCoefficient,ArithmeticFunction.coe_mk,if_neg hn,
    Complex.cpow_add s β hnC,Complex.cpow_neg,div_eq_mul_inv,mul_inv_rev]
  ring

lemma b_power_twist_summable {p : ℕ} (ψ : DirichletCharacter ℂ p)
    (β : ℂ) (hβ : β.re = 0) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n : ℕ => ψ (n : ZMod p)*lemma83PowerCoefficient β n) s := by
  have hh : 1 < (s+β).re := by simpa [hβ] using hs
  exact (DirichletCharacter.LSeriesSummable_of_one_lt_re ψ hh).congr
    (fun n => (b_power_twist_term ψ β s n).symm)

lemma b_power_twist_LSeries {p : ℕ} (ψ : DirichletCharacter ℂ p) (β s : ℂ) :
    LSeries (fun n : ℕ => ψ (n : ZMod p)*lemma83PowerCoefficient β n) s =
      LSeries (fun n : ℕ => ψ (n : ZMod p)) (s+β) := by
  unfold LSeries
  exact tsum_congr (b_power_twist_term ψ β s)

lemma b_twist_arithmetic_product {p : ℕ} (ψ : DirichletCharacter ℂ p)
    (f g : ArithmeticFunction ℂ) :
    (fun n : ℕ => ψ (n : ZMod p)*(f*g) n) = LSeries.convolution
      (fun n : ℕ => ψ (n : ZMod p)*f n) (fun n : ℕ => ψ (n : ZMod p)*g n) := by
  simpa only [ArithmeticFunction.coe_mul] using
    (DirichletCharacter.mul_convolution_distrib ψ f g).symm

lemma b_moebius_twist_summable {p : ℕ} (ψ : DirichletCharacter ℂ p)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n : ℕ => ψ (n : ZMod p)*
      (ArithmeticFunction.moebius : ArithmeticFunction ℂ) n) s := by
  exact DirichletCharacter.LSeriesSummable_mul ψ
    (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs)

lemma b_kappa_twist_summable {p : ℕ} (ψ : DirichletCharacter ℂ p)
    (β : Fin 2 → ℂ) (hβ : ∀ j, (β j).re = 0) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n : ℕ => ψ (n : ZMod p)*lemma152Kappa β n) s := by
  unfold lemma152Kappa
  rw [b_twist_arithmetic_product,b_twist_arithmetic_product]
  exact (b_moebius_twist_summable ψ hs).convolution
    ((b_power_twist_summable ψ (β 0) (hβ 0) hs).convolution
      (b_power_twist_summable ψ (β 1) (hβ 1) hs))

/-- The actual two-shift Möbius convolution is the L-series ratio in Section 15. -/
theorem b_kappa_twist_LSeries_ratio {p : ℕ} (ψ : DirichletCharacter ℂ p)
    (β : Fin 2 → ℂ) (hβ : ∀ j, (β j).re = 0) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n : ℕ => ψ (n : ZMod p)*lemma152Kappa β n) s =
      LSeries (fun n : ℕ => ψ (n : ZMod p)) (s+β 0)*
      LSeries (fun n : ℕ => ψ (n : ZMod p)) (s+β 1) /
      LSeries (fun n : ℕ => ψ (n : ZMod p)) s := by
  unfold lemma152Kappa
  rw [b_twist_arithmetic_product,b_twist_arithmetic_product,
    LSeries_convolution' (b_moebius_twist_summable ψ hs)
      ((b_power_twist_summable ψ (β 0) (hβ 0) hs).convolution
        (b_power_twist_summable ψ (β 1) (hβ 1) hs)),
    LSeries_convolution' (b_power_twist_summable ψ (β 0) (hβ 0) hs)
      (b_power_twist_summable ψ (β 1) (hβ 1) hs),
    b_power_twist_LSeries,b_power_twist_LSeries]
  have hμ := DirichletCharacter.LSeries.mul_mu_eq_one ψ hs
  have hn := DirichletCharacter.LSeries_ne_zero_of_one_lt_re ψ hs
  apply (eq_div_iff hn).mpr
  calc
    _ = (LSeries (fun n : ℕ => ψ (n : ZMod p)) s *
      LSeries (fun n : ℕ => ψ (n : ZMod p)*(ArithmeticFunction.moebius : ArithmeticFunction ℂ) n) s)*
      (LSeries (fun n : ℕ => ψ (n : ZMod p)) (s+β 0)*
        LSeries (fun n : ℕ => ψ (n : ZMod p)) (s+β 1)) := by ring
    _ = _ := by
      simpa only [ArithmeticFunction.intCoe_apply,one_mul] using
        (congrArg (fun z => z*(LSeries (fun n : ℕ => ψ (n : ZMod p)) (s+β 0)*
          LSeries (fun n : ℕ => ψ (n : ZMod p)) (s+β 1))) hμ)

noncomputable def bPsiArithmetic {D : ℕ} (χ : RealPrimitiveCharacter D) :
    ArithmeticFunction ℂ :=
  ⟨lemma151BPsi χ, by simp [lemma151BPsi,lemma151BChiPsi]⟩

/-- The genuinely derived pre-(15.5) identity. The convolution uses bψ, not b0.
All convergence hypotheses follow from Re s>1 and the proved finite support. -/
theorem b_source_ratio_convolution {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (c : ℝ) {s : ℂ} (hs : 1 < s.re) :
    ψ.LFunction (s+lemma52PaperBetaOne D c)*ψ.LFunction (s+lemma52PaperBetaTwo D c)/
      ψ.LFunction s*bSourceB χ ψ s =
    LSeries (fun n : ℕ => ψ (n : ZMod p)*
      (lemma152Kappa (lemma152PaperBeta D c)*bPsiArithmetic χ) n) s := by
  have hβ := lemma152_beta_re D c
  have h0 : lemma152PaperBeta D c 0 = lemma52PaperBetaOne D c := by
    simp [lemma152PaperBeta]
  have h1 : lemma152PaperBeta D c 1 = lemma52PaperBetaTwo D c := by
    simp [lemma152PaperBeta]
  have hs0 : 1 < (s+lemma52PaperBetaOne D c).re := by
    simpa [lemma52PaperBetaOne] using hs
  have hs1 : 1 < (s+lemma52PaperBetaTwo D c).re := by
    simpa [lemma52PaperBetaTwo] using hs
  rw [b_twist_arithmetic_product]
  simp only [bPsiArithmetic,ArithmeticFunction.coe_mk]
  rw [LSeries_convolution' (b_kappa_twist_summable ψ _ hβ hs)
      (b_strict_support_summable (b_strict_support_mul_left (b_psi_strict_support χ)
        (fun n : ℕ => ψ (n : ZMod p))) s),
    b_kappa_twist_LSeries_ratio ψ _ hβ hs,h0,h1,
    DirichletCharacter.LFunction_eq_LSeries ψ hs0,
    DirichletCharacter.LFunction_eq_LSeries ψ hs1,
    DirichletCharacter.LFunction_eq_LSeries ψ hs,b_source_product_eq_psi_series]

end ZhangLS.Spec
