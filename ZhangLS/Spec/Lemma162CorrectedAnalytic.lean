import ZhangLS.Spec.Lemma162RawMajorant

/-! The corrected product is now constructed analytically from the ACTUAL
raw prime factors. Its full-half-plane bound retains explicit D dependence. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex Filter Topology Set
open scoped Classical
set_option maxHeartbeats 2500000

lemma lemma162_raw_prime_differentiable {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β γ : ℂ) (q : Nat.Primes) : Differentiable ℂ (lemma162RawPrimeCorrection χ β γ q) := by
  intro s
  have hm := lemma32_prime_monomial_differentiable q.val s
  unfold lemma162RawPrimeCorrection
  split_ifs
  · fun_prop
  · unfold lemma162RawPolynomial lemma162RawP lemma162RawQ lemma162RawS
    fun_prop

lemma lemma162_raw_euler_multipliable {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re=0) (γ : ℂ) (hγ : γ.re=0) (s : ℂ) (hs : 9/10≤s.re) :
    Multipliable (fun q : Nat.Primes => lemma162RawPrimeCorrection χ β γ q s) := by
  have hsum : Summable (fun q : Nat.Primes => ‖lemma162RawPrimeCorrection χ β γ q s-1‖) :=
    (lemma162_raw_majorant_summable χ.modulus_ne_zero).of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun q => lemma162_actual_raw_error_majorized χ β hβ γ hγ q s hs)
  simpa only [add_sub_cancel] using multipliable_one_add_of_summable hsum

lemma lemma162_raw_products_locally_uniform {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re=0) (γ : ℂ) (hγ : γ.re=0) :
    TendstoLocallyUniformlyOn
      (fun S : Finset Nat.Primes => fun s : ℂ => ∏ q ∈ S, lemma162RawPrimeCorrection χ β γ q s)
      (lemma162RawEulerProduct χ β γ) atTop {s : ℂ | 9/10<s.re} := by
  have hh := Summable.hasProdLocallyUniformlyOn_one_add
    (f := fun q : Nat.Primes => fun s : ℂ => lemma162RawPrimeCorrection χ β γ q s-1)
    (isOpen_lt continuous_const Complex.continuous_re)
    (lemma162_raw_majorant_summable χ.modulus_ne_zero)
    (Filter.Eventually.of_forall fun q s hs => lemma162_actual_raw_error_majorized χ β hβ γ hγ q s hs.le)
    (fun q => (lemma162_raw_prime_differentiable χ β γ q).continuous.continuousOn.sub continuousOn_const)
  simpa only [hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn,add_sub_cancel,
    lemma162RawEulerProduct] using hh

lemma lemma162_raw_euler_analytic {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re=0) (γ : ℂ) (hγ : γ.re=0) :
    AnalyticOnNhd ℂ (lemma162RawEulerProduct χ β γ) {s : ℂ | 9/10<s.re} := by
  apply DifferentiableOn.analyticOnNhd ?_ (isOpen_lt continuous_const Complex.continuous_re)
  apply (lemma162_raw_products_locally_uniform χ β hβ γ hγ).differentiableOn
  · filter_upwards with S
    exact DifferentiableOn.fun_finsetProd fun q _ => (lemma162_raw_prime_differentiable χ β γ q).differentiableOn
  · exact isOpen_lt continuous_const Complex.continuous_re

lemma lemma162_corrected_euler_analytic {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re=0) (γ : ℂ) (hγ : γ.re=0) :
    AnalyticOnNhd ℂ (lemma162CorrectedEulerProduct χ β γ) {s : ℂ | 9/10<s.re} := by
  simpa only [lemma162CorrectedEulerProduct,div_eq_mul_inv] using
    (lemma162_raw_euler_analytic χ β hβ γ hγ).mul
      (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ => (lemma161Star χ β (1-γ))⁻¹) _)

/-- Explicit D-dependent bound. Ramified factors have NOT been silently
absorbed into an absolute uniform constant. -/
noncomputable def lemma162RawDBound (D : ℕ) : ℝ := Real.exp (∑' q : Nat.Primes, lemma162RawMajorant D q)

lemma lemma162_raw_d_bound_pos (D : ℕ) : 0<lemma162RawDBound D := Real.exp_pos _

lemma lemma162_raw_finite_product_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re=0) (γ : ℂ) (hγ : γ.re=0)
    (s : ℂ) (hs : 9/10≤s.re) (S : Finset Nat.Primes) :
    ‖∏ q ∈ S, lemma162RawPrimeCorrection χ β γ q s‖≤lemma162RawDBound D := by
  rw [norm_prod]
  apply (Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun q _ => ?_)).trans
  · apply (Real.prod_one_add_le_exp_sum S (fun q : Nat.Primes => lemma162_raw_majorant_nonneg D q)).trans
    apply Real.exp_le_exp.mpr
    exact (lemma162_raw_majorant_summable χ.modulus_ne_zero).sum_le_tsum S
      (fun q _ => lemma162_raw_majorant_nonneg D q)
  · have he := lemma162_actual_raw_error_majorized χ β hβ γ hγ q s hs
    have hn := norm_le_norm_sub_add (lemma162RawPrimeCorrection χ β γ q s) (1:ℂ)
    rw [norm_one] at hn
    linarith

lemma lemma162_raw_euler_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re=0) (γ : ℂ) (hγ : γ.re=0) (s : ℂ) (hs : 9/10≤s.re) :
    ‖lemma162RawEulerProduct χ β γ s‖≤lemma162RawDBound D := by
  have ht : Tendsto (fun S : Finset Nat.Primes => ∏ q ∈ S, lemma162RawPrimeCorrection χ β γ q s)
      atTop (𝓝 (lemma162RawEulerProduct χ β γ s)) :=
    (lemma162_raw_euler_multipliable χ β hβ γ hγ s hs).hasProd
  exact le_of_tendsto ht.norm (Filter.Eventually.of_forall fun S =>
    lemma162_raw_finite_product_bound χ β hβ γ hγ s hs S)

lemma lemma162_corrected_euler_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re=0) (γ : ℂ) (hγ : γ.re=0) (s : ℂ) (hs : 9/10≤s.re) :
    ‖lemma162CorrectedEulerProduct χ β γ s‖≤
      lemma162RawDBound D/‖lemma161Star χ β (1-γ)‖ := by
  rw [lemma162CorrectedEulerProduct,norm_div]
  exact div_le_div_of_nonneg_right (lemma162_raw_euler_bound χ β hβ γ hγ s hs) (norm_nonneg _)

/-- Full actual shifted analytic continuation, without a free analytic model
or an assumed coefficient/Euler identity. The center asymptotic is separate. -/
lemma lemma162_actual_shifted_continuation {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re=0) (γ : ℂ) (hγ : γ.re=0)
    (hstar : lemma161Star χ β (1-γ) ≠ 0) :
    Lemma162ShiftedContinuation χ β γ (lemma162GeneralMEulerProduct χ β)
      (lemma162CorrectedEulerProduct χ β γ) := by
  refine ⟨lemma162_corrected_euler_analytic χ β hβ γ hγ,?_⟩
  intro s hs
  refine ⟨lemma162_actual_lseries_summable χ β hβ γ hγ hstar s hs,?_⟩
  simpa only [lemma162ShiftedMainFactor,mul_assoc] using
    lemma162_actual_shifted_euler_identity χ β hβ γ hγ hstar s hs

end ZhangLS.Spec
