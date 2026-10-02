import ZhangLS.Spec.Lemma153ActualDirichletSeries
import ZhangLS.Spec.Lemma153PaperParameters
/-! Actual shifted-L continuation bridge for Section15.3.
All agreement is proved on Re s>1 from absolutely convergent series/products.
No totalized quotient defines U outside that region. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma153_shifted_prime_monomial {p : ℕ} (hp : 0<p) (s γ : ℂ) :
    lemma32PrimeMonomial p (s-γ) = (p:ℂ)^γ*lemma32PrimeMonomial p s := by
  rw [sub_eq_add_neg,lemma152_monomial_add,lemma32_prime_monomial_eq_cpow hp (-γ),neg_neg]
  ring

lemma lemma153_actual_local_product_agreement {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (γ : ℂ) (hpar : Lemma153SmallParameters β γ)
    (hM : lemma152EulerProduct χ β (1-γ) ≠ 0) (q : Nat.Primes)
    (s : ℂ) (hs : 1<s.re) :
    lemma153PrimeFactor χ β γ q s * (1-lemma32PrimeMonomial q.val s)⁻¹^2 *
        (1-χ.evalNat q.val*lemma32PrimeMonomial q.val (s-γ))⁻¹^2 =
      ∑' n : ℕ, lemma153Coefficient χ β γ (lemma153GeneralMEulerProduct χ β) (q.val^n)*
        lemma32PrimeMonomial q.val s^n := by
  have hγs : 1<(s-γ).re := by simpa [hpar.gamma_re] using hs
  have hx : ‖lemma32PrimeMonomial q.val s‖ < 1 :=
    (lemma152_monomial_norm_half q.property s hs.le).trans_lt (by norm_num)
  have hy : ‖lemma32PrimeMonomial q.val (s-γ)‖ < 1 :=
    (lemma152_monomial_norm_half q.property (s-γ) hγs.le).trans_lt (by norm_num)
  have hxn := lemma83_one_sub_ne_zero hx
  have hvn : 1-χ.evalNat q.val*lemma32PrimeMonomial q.val (s-γ) ≠ 0 :=
    lemma83_one_sub_ne_zero (lt_of_le_of_lt (by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (χ.evalNat_norm_le_one _)) hy)
  have he := lemma153_actual_prime_factor_extraction χ β hpar.beta_re γ hpar.gamma_re q hM s (by linarith)
  have hm := lemma153_shifted_prime_monomial q.property.pos s γ
  rw [show χ.evalNat q.val*(q.val:ℂ)^γ*lemma32PrimeMonomial q.val s =
    χ.evalNat q.val*lemma32PrimeMonomial q.val (s-γ) by rw [hm]; ring] at he
  rw [← he]
  field_simp

/-- The normally convergent product is now proved to be the repaired actual
U₁ⱼ associated to the original varpi, not merely a local Euler model. -/
lemma lemma153_actual_shifted_continuation {D : ℕ} (hD : D ≠ 0)
    (χ : RealPrimitiveCharacter D) (β : Fin 2 → ℂ) (γ : ℂ)
    (hpar : Lemma153SmallParameters β γ) (hM : lemma152EulerProduct χ β (1-γ) ≠ 0) :
    Lemma153ShiftedContinuation χ β γ (lemma153GeneralMEulerProduct χ β)
      (lemma153EulerProduct χ β γ) := by
  refine ⟨(lemma153_euler_product_analyticOnNhd hD χ β γ hpar).mono
    (fun s hs => by dsimp at *; linarith),?_⟩
  intro s hs
  refine ⟨lemma153_actual_lseries_summable χ β γ hpar hM s hs,?_⟩
  have hγs : 1<(s-γ).re := by simpa [hpar.gamma_re] using hs
  have hu := (lemma153_euler_product_multipliable hD χ β γ hpar s (by linarith)).hasProd
  have hz := lemma32_actual_zeta_monomial_euler_hasProd s hs
  have hl := lemma32_actual_L_monomial_euler_hasProd χ (s-γ) hγs
  have ha := lemma153_actual_dirichlet_series_hasProd χ β γ hpar hM s hs
  have hleft := (hu.mul (hz.mul hz)).mul (hl.mul hl)
  have he := hleft.congr_fun (fun q => by
    simpa only [pow_two] using (lemma153_actual_local_product_agreement χ β γ hpar hM q s hs).symm)
  simpa only [pow_two] using he.unique ha

/-- Uniform-in-character analytic continuation at exactly the original shifts.
The center asymptotic is deliberately not included until its perturbation
estimate has been proved. -/
lemma lemma153_paper_shifted_analytic_bridge {c : ℝ} (hc : 0<c) :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D,
      ∀ j : Fin 3,
        Lemma153ShiftedContinuation χ (lemma152PaperBeta D c) (lemma83PaperBeta D c j)
          (lemma153GeneralMEulerProduct χ (lemma152PaperBeta D c))
          (lemma153EulerProduct χ (lemma152PaperBeta D c) (lemma83PaperBeta D c j)) ∧
        AnalyticOnNhd ℂ (lemma153EulerProduct χ (lemma152PaperBeta D c) (lemma83PaperBeta D c j))
          {s : ℂ | 9/10 ≤ s.re} ∧
        ∀ s : ℂ, 9/10 ≤ s.re →
          ‖lemma153EulerProduct χ (lemma152PaperBeta D c) (lemma83PaperBeta D c j) s‖ ≤ lemma153DBound D := by
  obtain ⟨D₁,hD1,hpar⟩ := lemma153_small_parameters_threshold hc
  obtain ⟨D₂,hD2,hnonzero⟩ := lemma153_normalization_nonzero_threshold hc
  refine ⟨max D₁ D₂,hD1.trans (le_max_left _ _),?_⟩
  intro D hD χ j
  have hD1' : D₁≤D := (le_max_left _ _).trans hD
  have hD2' : D₂≤D := (le_max_right _ _).trans hD
  have hp := hpar D hD1' j
  have hM := hnonzero D hD2' χ j
  have hDne : D ≠ 0 := by omega
  refine ⟨lemma153_actual_shifted_continuation hDne χ _ _ hp hM,?_,?_⟩
  · exact (lemma153_euler_product_analyticOnNhd hDne χ _ _ hp).mono (fun s hs => by dsimp at *; linarith)
  · intro s hs
    exact lemma153_euler_product_norm_bound hDne χ _ _ hp s (by linarith)

end ZhangLS.Spec
