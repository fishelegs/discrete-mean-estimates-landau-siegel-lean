import ZhangLS.Spec.BRatioConvolution
import ZhangLS.Spec.Proposition71CoefficientEnergy

/-! # The actual Section7 three-shift coefficient series

This extends the independently proved character-twist convolution helpers to
the original three β shifts, and identifies the actual κ*a₁ series. No desired
Euler identity or contour representation is assumed.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 3500000

lemma proposition71_kappa_twist_summable {p : ℕ} (ψ : DirichletCharacter ℂ p)
    (β : Fin 3 → ℂ) (hβ : ∀j, (β j).re=0) {s : ℂ} (hs : 1<s.re) :
    LSeriesSummable (fun n : ℕ => ψ (n : ZMod p)*lemma83Kappa β n) s := by
  unfold lemma83Kappa
  rw [b_twist_arithmetic_product,b_twist_arithmetic_product,b_twist_arithmetic_product]
  exact (b_moebius_twist_summable ψ hs).convolution
    (((b_power_twist_summable ψ (β 0) (hβ 0) hs).convolution
      (b_power_twist_summable ψ (β 1) (hβ 1) hs)).convolution
        (b_power_twist_summable ψ (β 2) (hβ 2) hs))

/-- Exact actual three-shift quotient on its genuine convergence half-plane. -/
theorem proposition71_kappa_twist_LSeries_ratio {p : ℕ} (ψ : DirichletCharacter ℂ p)
    (β : Fin 3 → ℂ) (hβ : ∀j, (β j).re=0) {s : ℂ} (hs : 1<s.re) :
    LSeries (fun n : ℕ => ψ (n : ZMod p)*lemma83Kappa β n) s=
      LSeries (fun n : ℕ => ψ (n : ZMod p)) (s+β 0)*
      LSeries (fun n : ℕ => ψ (n : ZMod p)) (s+β 1)*
      LSeries (fun n : ℕ => ψ (n : ZMod p)) (s+β 2)/
      LSeries (fun n : ℕ => ψ (n : ZMod p)) s := by
  have h0 := b_power_twist_summable ψ (β 0) (hβ 0) hs
  have h1 := b_power_twist_summable ψ (β 1) (hβ 1) hs
  have h2 := b_power_twist_summable ψ (β 2) (hβ 2) hs
  have hμ := b_moebius_twist_summable ψ hs
  unfold lemma83Kappa
  rw [b_twist_arithmetic_product,b_twist_arithmetic_product,b_twist_arithmetic_product,
    LSeries_convolution' hμ ((h0.convolution h1).convolution h2),
    LSeries_convolution' (h0.convolution h1) h2,LSeries_convolution' h0 h1,
    b_power_twist_LSeries,b_power_twist_LSeries,b_power_twist_LSeries]
  have hμone := DirichletCharacter.LSeries.mul_mu_eq_one ψ hs
  have hn := DirichletCharacter.LSeries_ne_zero_of_one_lt_re ψ hs
  apply (eq_div_iff hn).mpr
  calc
    _=(LSeries (fun n : ℕ => ψ (n : ZMod p)) s*
        LSeries (fun n : ℕ => ψ (n : ZMod p)*(ArithmeticFunction.moebius : ArithmeticFunction ℂ) n) s)*
        (LSeries (fun n : ℕ => ψ (n : ZMod p)) (s+β 0)*
          LSeries (fun n : ℕ => ψ (n : ZMod p)) (s+β 1)*
          LSeries (fun n : ℕ => ψ (n : ZMod p)) (s+β 2)) := by ring
    _=_ := by
      simpa only [ArithmeticFunction.intCoe_apply,one_mul] using
        congrArg (fun z => z*(LSeries (fun n : ℕ => ψ (n : ZMod p)) (s+β 0)*
          LSeries (fun n : ℕ => ψ (n : ZMod p)) (s+β 1)*
          LSeries (fun n : ℕ => ψ (n : ZMod p)) (s+β 2))) hμone

lemma proposition71_arithmetic_sequence_strict_support {D : ℕ} {B : ℝ}
    (a : ℕ → ℂ) (ha : Lemma81AdmissibleSequence D B a) :
    BStrictSupport (lemma81Cutoff D) (proposition71ArithmeticSequence a) := by
  intro n hn
  have hn0 : n≠0 := by intro hh; subst n; exact hn (by simp)
  have hp : 0<n := Nat.pos_of_ne_zero hn0
  refine ⟨hp,?_⟩
  by_contra hh
  have hz := ha.2 n (le_of_not_gt hh)
  exact hn (by rw [proposition71_arithmetic_sequence_positive a hp,hz])

lemma proposition71_arithmetic_sequence_LSeries {D p : ℕ} {B : ℝ}
    (a : ℕ → ℂ) (ha : Lemma81AdmissibleSequence D B a)
    (ψ : DirichletCharacter ℂ p) (s : ℂ) :
    LSeries (fun n : ℕ => ψ (n : ZMod p)*proposition71ArithmeticSequence a n) s=
      lemma81Polynomial D a ψ s := by
  unfold LSeries
  have he : (∑' n, LSeries.term (fun n : ℕ => ψ (n : ZMod p)*proposition71ArithmeticSequence a n) s n)=
      ∑n∈lemma81PolynomialIndices D, LSeries.term (fun n : ℕ => ψ (n : ZMod p)*proposition71ArithmeticSequence a n) s n := by
    apply tsum_eq_sum
    intro n hn
    by_cases hn0 : n=0
    · subst n; simp
    have hp : 0<n := Nat.pos_of_ne_zero hn0
    have hcut : lemma81Cutoff D≤(n : ℝ) := by
      by_contra hh
      exact hn ((proposition71_mem_indices D n).mpr ⟨hp,lt_of_not_ge hh⟩)
    rw [LSeries.term_of_ne_zero hn0,proposition71_arithmetic_sequence_positive a hp,ha.2 n hcut]
    simp
  rw [he]
  unfold lemma81Polynomial
  apply sum_congr rfl
  intro n hn
  have hp := ((proposition71_mem_indices D n).mp hn).1
  rw [LSeries.term_of_ne_zero hp.ne',proposition71_arithmetic_sequence_positive a hp]
  ring

/-- The actual quotient times A(a₁), with all original β shifts and the
original strict sequence, is its genuine κ*a₁ Dirichlet series. -/
theorem proposition71_actual_ratio_convolution {D p : ℕ} [NeZero p] {B : ℝ}
    (ψ : DirichletCharacter ℂ p) (c : ℝ) (a : ℕ → ℂ)
    (ha : Lemma81AdmissibleSequence D B a) {s : ℂ} (hs : 1<s.re) :
    ψ.LFunction (s+lemma52PaperBetaOne D c)*ψ.LFunction (s+lemma52PaperBetaTwo D c)*
      ψ.LFunction (s+lemma52PaperBetaThree D c)/ψ.LFunction s*lemma81Polynomial D a ψ s=
      LSeries (fun n : ℕ => (lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a) n*
        ψ (n : ZMod p)) s := by
  have hβ := lemma83_beta_re D c
  have h0 : lemma83PaperBeta D c 0=lemma52PaperBetaOne D c := by simp [lemma83PaperBeta]
  have h1 : lemma83PaperBeta D c 1=lemma52PaperBetaTwo D c := by simp [lemma83PaperBeta]
  have h2 : lemma83PaperBeta D c 2=lemma52PaperBetaThree D c := by simp [lemma83PaperBeta]
  have hs0 : 1<(s+lemma52PaperBetaOne D c).re := by simpa [lemma52PaperBetaOne] using hs
  have hs1 : 1<(s+lemma52PaperBetaTwo D c).re := by simpa [lemma52PaperBetaTwo] using hs
  have hs2 : 1<(s+lemma52PaperBetaThree D c).re := by simpa [lemma52PaperBetaThree] using hs
  have ht := b_strict_support_summable (b_strict_support_mul_left
    (proposition71_arithmetic_sequence_strict_support a ha) (fun n : ℕ => ψ (n : ZMod p))) s
  have he : (fun n : ℕ => (lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a) n*ψ (n : ZMod p))=
      (fun n : ℕ => ψ (n : ZMod p)*(lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a) n) := by
    funext n; ring
  rw [he,b_twist_arithmetic_product,
    LSeries_convolution' (proposition71_kappa_twist_summable ψ _ hβ hs) ht,
    proposition71_kappa_twist_LSeries_ratio ψ _ hβ hs,h0,h1,h2,
    DirichletCharacter.LFunction_eq_LSeries ψ hs0,
    DirichletCharacter.LFunction_eq_LSeries ψ hs1,
    DirichletCharacter.LFunction_eq_LSeries ψ hs2,
    DirichletCharacter.LFunction_eq_LSeries ψ hs,proposition71_arithmetic_sequence_LSeries a ha ψ s]

end ZhangLS.Spec
