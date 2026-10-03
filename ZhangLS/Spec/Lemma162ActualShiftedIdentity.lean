import ZhangLS.Spec.Lemma162ActualRawExtraction

/-! Exact shifted factorization of the original arithmetic series on its
absolute-convergence half-plane. Holomorphic continuation of the raw product
is a separate obligation, not assumed by this identity. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex Filter Topology
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def lemma162ShiftedMainFactor {D : ℕ} (χ : RealPrimitiveCharacter D)
    (γ s : ℂ) : ℂ :=
  riemannZeta s^2*riemannZeta (s-γ)*dirichletLFunction χ s*dirichletLFunction χ (s-γ)^2

noncomputable def lemma162RawEulerProduct {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β γ s : ℂ) : ℂ := ∏' q : Nat.Primes, lemma162RawPrimeCorrection χ β γ q s

noncomputable def lemma162CorrectedEulerProduct {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β γ s : ℂ) : ℂ := lemma162RawEulerProduct χ β γ s/lemma161Star χ β (1-γ)

lemma lemma162_shifted_prime_monomial {p : ℕ} (hp : 0<p) (s γ : ℂ) :
    lemma32PrimeMonomial p (s-γ) = (p:ℂ)^γ*lemma32PrimeMonomial p s := by
  rw [sub_eq_add_neg,lemma152_monomial_add,lemma32_prime_monomial_eq_cpow hp (-γ),neg_neg]
  ring

lemma lemma162_shifted_main_factor_nonzero {D : ℕ} (χ : RealPrimitiveCharacter D)
    (γ : ℂ) (hγ : γ.re=0) (s : ℂ) (hs : 1<s.re) :
    lemma162ShiftedMainFactor χ γ s ≠ 0 := by
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  have ht : 1<(s-γ).re := by simpa [hγ] using hs
  have hL (w : ℂ) (hw : 1<w.re) : dirichletLFunction χ w ≠ 0 := by
    unfold dirichletLFunction
    rw [DirichletCharacter.LFunction_eq_LSeries χ.chi hw]
    exact DirichletCharacter.LSeries_ne_zero_of_one_lt_re χ.chi hw
  unfold lemma162ShiftedMainFactor
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero
    (pow_ne_zero 2 (riemannZeta_ne_zero_of_one_lt_re hs))
    (riemannZeta_ne_zero_of_one_lt_re ht)) (hL s hs)) (pow_ne_zero 2 (hL _ ht))

lemma lemma162_shifted_main_factor_hasProd {D : ℕ} (χ : RealPrimitiveCharacter D)
    (γ : ℂ) (hγ : γ.re=0) (s : ℂ) (hs : 1<s.re) :
    HasProd (fun q : Nat.Primes =>
      (lemma162ShiftedRemoval (χ.evalNat q.val) ((q.val:ℂ)^γ) (lemma32PrimeMonomial q.val s))⁻¹)
      (lemma162ShiftedMainFactor χ γ s) := by
  have ht : 1<(s-γ).re := by simpa [hγ] using hs
  have hz := lemma32_actual_zeta_monomial_euler_hasProd s hs
  have hzt := lemma32_actual_zeta_monomial_euler_hasProd (s-γ) ht
  have hl := lemma32_actual_L_monomial_euler_hasProd χ s hs
  have hlt := lemma32_actual_L_monomial_euler_hasProd χ (s-γ) ht
  apply ((((hz.pow 2).mul hzt).mul hl).mul (hlt.pow 2)).congr_fun
  intro q
  rw [lemma162_shifted_prime_monomial q.property.pos s γ]
  unfold lemma162ShiftedRemoval
  simp only [mul_inv_rev,inv_pow]
  ring

lemma lemma162_shifted_removal_hasProd {D : ℕ} (χ : RealPrimitiveCharacter D)
    (γ : ℂ) (hγ : γ.re=0) (s : ℂ) (hs : 1<s.re) :
    HasProd (fun q : Nat.Primes =>
      lemma162ShiftedRemoval (χ.evalNat q.val) ((q.val:ℂ)^γ) (lemma32PrimeMonomial q.val s))
      (lemma162ShiftedMainFactor χ γ s)⁻¹ := by
  have ht := lemma162_shifted_main_factor_hasProd χ γ hγ s hs
  have he := lemma162_shifted_main_factor_nonzero χ γ hγ s hs
  change Tendsto (fun S : Finset Nat.Primes => ∏ q ∈ S,
    lemma162ShiftedRemoval (χ.evalNat q.val) ((q.val:ℂ)^γ) (lemma32PrimeMonomial q.val s))
      atTop (𝓝 (lemma162ShiftedMainFactor χ γ s)⁻¹)
  have hh : Tendsto (fun S : Finset Nat.Primes =>
      (∏ q ∈ S, (lemma162ShiftedRemoval (χ.evalNat q.val) ((q.val:ℂ)^γ)
        (lemma32PrimeMonomial q.val s))⁻¹)⁻¹)
      atTop (𝓝 (lemma162ShiftedMainFactor χ γ s)⁻¹) := ht.inv₀ he
  simpa only [← Finset.prod_inv_distrib,inv_inv] using hh

lemma lemma162_raw_euler_hasProd_on_convergence {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re=0) (γ : ℂ) (hγ : γ.re=0)
    (hstar : lemma161Star χ β (1-γ) ≠ 0) (s : ℂ) (hs : 1<s.re) :
    HasProd (fun q : Nat.Primes => lemma162RawPrimeCorrection χ β γ q s)
      (lemma161Star χ β (1-γ)*(lemma162ShiftedMainFactor χ γ s)⁻¹*
        lemma162DirichletSeries χ β γ (lemma162GeneralMEulerProduct χ β) s) := by
  have hn := lemma162_normalizers_hasProd χ β hβ γ hγ
  have hr := lemma162_shifted_removal_hasProd χ γ hγ s hs
  have hf := lemma162_actual_dirichlet_series_hasProd χ β hβ γ hγ hstar s hs
  exact ((hn.mul hr).mul hf).congr_fun
    (fun q => lemma162_actual_raw_local_extraction χ β hβ γ hγ hstar q s hs)

/-- The actual source-series factorization, with no model coefficient and
without evaluating any zeta/L function at a pole or a nonsummable series. -/
lemma lemma162_actual_shifted_euler_identity {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re=0) (γ : ℂ) (hγ : γ.re=0)
    (hstar : lemma161Star χ β (1-γ) ≠ 0) (s : ℂ) (hs : 1<s.re) :
    lemma162CorrectedEulerProduct χ β γ s * lemma162ShiftedMainFactor χ γ s =
      lemma162DirichletSeries χ β γ (lemma162GeneralMEulerProduct χ β) s := by
  have hh := (lemma162_raw_euler_hasProd_on_convergence χ β hβ γ hγ hstar s hs).tprod_eq
  have he := lemma162_shifted_main_factor_nonzero χ γ hγ s hs
  unfold lemma162CorrectedEulerProduct lemma162RawEulerProduct
  rw [hh]
  field_simp

end ZhangLS.Spec
