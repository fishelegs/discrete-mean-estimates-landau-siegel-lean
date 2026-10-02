import ZhangLS.Spec.Proposition71MellinDoubleSum
import ZhangLS.Spec.Proposition71DyadicPrimeMean

/-! # Exact Mellin representation of the actual finite Section 7 σ sum -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset MeasureTheory
open scoped Classical
set_option maxHeartbeats 2500000

noncomputable def proposition71KappaCharacterPolynomial {r : ℕ}
    (D : ℕ) (c : ℝ) (a : ℕ → ℂ) (d : ℕ) (S : Finset ℕ)
    (θ : DirichletCharacter ℂ r) (s : ℂ) : ℂ :=
  ∑ l∈S, ((lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a) (d*l)/(l : ℂ)^s)*
    θ (l : ZMod r)

noncomputable def proposition71PrimeCharacterPolynomial {r : ℕ}
    (D : ℕ) (b : ℝ) (θ : DirichletCharacter ℂ r) (s : ℂ) : ℂ :=
  ∑ p∈lemma56PaperPrimes D, (p : ℂ)^(s+I*(b : ℂ))*θ⁻¹ (p : ZMod r)

noncomputable def proposition71SigmaOnSet {r : ℕ}
    (D : ℕ) (c b : ℝ) (a : ℕ → ℂ) (h : ℝ) (d : ℕ)
    (S : Finset ℕ) (θ : DirichletCharacter ℂ r) : ℂ :=
  ∑ l∈S, (lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a) (d*l)*θ (l : ZMod r)*
    ∑ p∈lemma56PaperPrimes D, (p : ℂ)^(I*(b : ℂ))*θ⁻¹ (p : ZMod r)*
      lemma53PaperDelta D ((l : ℝ)/((p : ℝ)*h*(r : ℝ)))

noncomputable def proposition71SigmaMellinIntegrand {r : ℕ}
    (D : ℕ) (c b σ : ℝ) (a : ℕ → ℂ) (h : ℝ) (d : ℕ)
    (S : Finset ℕ) (θ : DirichletCharacter ℂ r) (t : ℝ) : ℂ :=
  lemma54PaperDeltaMellin D ((σ : ℂ)+(t : ℂ)*I)*
    ((h*(r : ℝ) : ℝ) : ℂ)^((σ : ℂ)+(t : ℂ)*I)*
      proposition71KappaCharacterPolynomial D c a d S θ ((σ : ℂ)+(t : ℂ)*I)*
      proposition71PrimeCharacterPolynomial D b θ ((σ : ℂ)+(t : ℂ)*I)

lemma proposition71_kappa_character_polynomial_factor {r : ℕ}
    (D : ℕ) (c : ℝ) (a : ℕ → ℂ) (d : ℕ) (S : Finset ℕ)
    (θ : DirichletCharacter ℂ r) (s : ℂ) :
    (∑ l∈S, ((lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a) (d*l)*θ (l : ZMod r))*
      (l : ℂ)^(-s))=proposition71KappaCharacterPolynomial D c a d S θ s := by
  unfold proposition71KappaCharacterPolynomial
  apply sum_congr rfl
  intro l hl
  rw [Complex.cpow_neg]
  ring

lemma proposition71_prime_character_polynomial_factor {r : ℕ}
    (D : ℕ) (b : ℝ) (θ : DirichletCharacter ℂ r) (s : ℂ) :
    (∑ p∈lemma56PaperPrimes D, ((p : ℂ)^(I*(b : ℂ))*θ⁻¹ (p : ZMod r))*(p : ℂ)^s)=
      proposition71PrimeCharacterPolynomial D b θ s := by
  unfold proposition71PrimeCharacterPolynomial
  apply sum_congr rfl
  intro p hp
  have hp0 : (p : ℂ)≠0 := Nat.cast_ne_zero.mpr ((lemma56_mem_paper_primes D p).mp hp).1.ne_zero
  rw [Complex.cpow_add _ _ hp0]
  ring

lemma proposition71_sigma_integrand_eq_double {r : ℕ}
    (D : ℕ) (c b σ : ℝ) (a : ℕ → ℂ) (h : ℝ) (d : ℕ)
    (S : Finset ℕ) (θ : DirichletCharacter ℂ r) (t : ℝ) :
    proposition71SigmaMellinIntegrand D c b σ a h d S θ t=
      proposition71DoubleMellinIntegrand D σ h (r : ℝ) S (lemma56PaperPrimes D)
        (fun l => (lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a) (d*l)*θ (l : ZMod r))
        (fun p => (p : ℂ)^(I*(b : ℂ))*θ⁻¹ (p : ZMod r)) t := by
  unfold proposition71SigmaMellinIntegrand proposition71DoubleMellinIntegrand
  rw [proposition71_kappa_character_polynomial_factor,proposition71_prime_character_polynomial_factor]

/-- Exact σ Mellin representation with the actual two character polynomials. -/
theorem proposition71_actual_sigma_mellin {D r : ℕ}
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) (hr : 0<r)
    (c b : ℝ) {σ h : ℝ} (hσ : 1/2≤σ) (hh : 0<h)
    (a : ℕ → ℂ) (d : ℕ) (S : Finset ℕ) (hS : ∀l∈S, 0<l)
    (θ : DirichletCharacter ℂ r) :
    proposition71SigmaOnSet D c b a h d S θ=
      ((1/(2*Real.pi) : ℝ) : ℂ)*∫t : ℝ,
        proposition71SigmaMellinIntegrand D c b σ a h d S θ t := by
  have he := proposition71_actual_double_mellin_sum hD hL hσ hh
    (by exact_mod_cast hr : (0:ℝ)<r) S (lemma56PaperPrimes D) hS
    (fun p hp => ((lemma56_mem_paper_primes D p).mp hp).1.pos)
    (fun l => (lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a) (d*l)*θ (l : ZMod r))
    (fun p => (p : ℂ)^(I*(b : ℂ))*θ⁻¹ (p : ZMod r))
  simpa only [←proposition71_sigma_integrand_eq_double,proposition71SigmaOnSet] using he

/-- Absolute integrability is proved for every character at the actual level. -/
theorem proposition71_sigma_mellin_integrable {D r : ℕ}
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) (hr : 0<r)
    (c b : ℝ) {σ h : ℝ} (hσ : 1/2≤σ) (hh : 0<h)
    (a : ℕ → ℂ) (d : ℕ) (S : Finset ℕ) (hS : ∀l∈S, 0<l)
    (θ : DirichletCharacter ℂ r) :
    Integrable (proposition71SigmaMellinIntegrand D c b σ a h d S θ) := by
  have hi := proposition71_double_mellin_integrand_integrable hD hL hσ hh
    (by exact_mod_cast hr : (0:ℝ)<r) S (lemma56PaperPrimes D) hS
    (fun p hp => ((lemma56_mem_paper_primes D p).mp hp).1.pos)
    (fun l => (lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a) (d*l)*θ (l : ZMod r))
    (fun p => (p : ℂ)^(I*(b : ℂ))*θ⁻¹ (p : ZMod r))
  apply hi.congr
  exact ae_of_all _ (fun t => (proposition71_sigma_integrand_eq_double D c b σ a h d S θ t).symm)

/-- On the Mellin line Re(s)=1 the full extracted scale is exactly hr. -/
theorem proposition71_sigma_mellin_norm {r : ℕ} (hr : 0<r)
    (D : ℕ) (c b : ℝ) (a : ℕ → ℂ) {h : ℝ} (hh : 0<h) (d : ℕ)
    (S : Finset ℕ) (θ : DirichletCharacter ℂ r) (t : ℝ) :
    ‖proposition71SigmaMellinIntegrand D c b 1 a h d S θ t‖=
      ‖lemma54PaperDeltaMellin D ((1 : ℂ)+(t : ℂ)*I)‖*(h*(r : ℝ))*
        ‖proposition71KappaCharacterPolynomial D c a d S θ ((1 : ℂ)+(t : ℂ)*I)‖*
        ‖proposition71PrimeCharacterPolynomial D b θ ((1 : ℂ)+(t : ℂ)*I)‖ := by
  unfold proposition71SigmaMellinIntegrand
  simp only [norm_mul,Complex.ofReal_one]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast mul_pos hh (by exact_mod_cast hr : (0:ℝ)<r))]
  simp

end ZhangLS.Spec
