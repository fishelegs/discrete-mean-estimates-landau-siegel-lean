import ZhangLS.Spec.Lemma151ActualWeightedPrimeBudget
import ZhangLS.Spec.Lemma32ActualSeriesIdentity

/-! Absolute Euler majorant for the genuine Section 15 coefficient.
The first-prime coefficient 4 is retained; only the p^-2 correction enters
an absolute constant. No pointwise tau4 domination is used. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ZhangLS.Spec
open Finset Complex Filter Topology
open scoped Classical

noncomputable def actual151WeightedEulerPrimeConstant : ℝ :=
  40000+actual151WeightedPrimeTailConstant

lemma actual151_weighted_euler_prime_constant_nonneg :
    0≤actual151WeightedEulerPrimeConstant := by
  have := actual151_weighted_prime_tail_constant_nonneg
  unfold actual151WeightedEulerPrimeConstant
  linarith

noncomputable def actual151WeightedEulerConstant : ℝ :=
  Real.exp (∑' q : Nat.Primes,actual151WeightedEulerPrimeConstant*(q.val:ℝ)^(-2:ℝ))

lemma actual151_weighted_euler_constant_pos : 0<actual151WeightedEulerConstant :=
  Real.exp_pos _

lemma actual151_weighted_euler_majorant_summable :
    Summable (fun q : Nat.Primes => actual151WeightedEulerPrimeConstant*(q.val:ℝ)^(-2:ℝ)) :=
  ((Real.summable_nat_rpow.mpr (by norm_num : (-2:ℝ)< -1)).subtype Nat.Prime).mul_left _

lemma actual151_weighted_finite_correction_bound (S : Finset Nat.Primes) :
    (∏ q∈S,(1+actual151WeightedEulerPrimeConstant*(q.val:ℝ)^(-2:ℝ)))≤
      actual151WeightedEulerConstant := by
  apply (Real.prod_one_add_le_exp_sum S (fun q : Nat.Primes =>
    mul_nonneg actual151_weighted_euler_prime_constant_nonneg
      (Real.rpow_nonneg (Nat.cast_nonneg _) _))).trans
  apply Real.exp_le_exp.mpr
  exact actual151_weighted_euler_majorant_summable.sum_le_tsum S
    (fun q _ => mul_nonneg actual151_weighted_euler_prime_constant_nonneg
      (Real.rpow_nonneg (Nat.cast_nonneg _) _))

lemma actual151_one_add_four_le_inv_four {r : ℝ} (hr0 : 0≤r) (hr1 : r<1) :
    1+4*r≤((1-r)⁻¹)^4 := by
  have hd : 0<1-r := sub_pos.mpr hr1
  have hi : 1+r≤(1-r)⁻¹ := by
    rw [←one_div]
    apply (le_div_iff₀ hd).mpr
    nlinarith only [sq_nonneg r]
  calc
    _ ≤ (1+r)^4 := by
      simpa only [Nat.cast_ofNat] using one_add_mul_le_pow (by linarith : -2≤r) 4
    _ ≤ _ := pow_le_pow_left₀ (by positivity) hi 4

lemma actual151_prime_monomial_real (p : ℕ) (σ : ℝ) :
    lemma32PrimeMonomial p (σ:ℂ) = (‖lemma32PrimeMonomial p (σ:ℂ)‖:ℂ) := by
  rw [lemma32_prime_monomial_norm]
  simp only [Complex.ofReal_re]
  unfold lemma32PrimeMonomial
  rw [show (-(σ:ℂ)*(Real.log (p:ℝ):ℂ)) = ((-σ*Real.log (p:ℝ):ℝ):ℂ) by
    push_cast; rfl]
  exact (Complex.ofReal_exp _).symm

/-- The absolute local Euler factor is dominated by the fourth zeta factor
and a genuinely summable p^-2 correction, uniformly at all primes. -/
theorem actual151_weighted_local_euler_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2→ℂ) (γ : ℂ) (hpar : Lemma153SmallParameters β γ)
    (hM : lemma152EulerProduct χ β (1-γ)≠0) (q : Nat.Primes)
    (σ : ℝ) (hσ : 1<σ) :
    (∑' n : ℕ,
      ‖lemma153Coefficient χ β γ (lemma153GeneralMEulerProduct χ β) (q.val^n)*
        lemma32PrimeMonomial q.val (σ:ℂ)^n‖)≤
      ‖(1-lemma32PrimeMonomial q.val (σ:ℂ))⁻¹‖^4 *
        (1+actual151WeightedEulerPrimeConstant*(q.val:ℝ)^(-2:ℝ)) := by
  let z := lemma32PrimeMonomial q.val (σ:ℂ)
  let r : ℝ := ‖z‖
  let u : ℝ := (q.val:ℝ)⁻¹
  have hr0 : 0≤r := norm_nonneg _
  have hu0 : 0≤u := by dsimp [u]; positivity
  have hru : r≤u := by
    dsimp [r,z,u]
    rw [lemma83_prime_monomial_norm_rpow q.property.pos]
    simp only [Complex.ofReal_re]
    rw [←Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast q.property.one_lt.le) (by linarith)
  have hu : u≤1/2 := by
    dsimp [u]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2)
      (show (2:ℝ)≤q.val by exact_mod_cast q.property.two_le)
  have hr : r≤1/2 := hru.trans hu
  have hr1 : r<1 := by linarith
  have hK := actual151_weighted_prime_tail_constant_nonneg
  have hpow : r^2≤u^2 := pow_le_pow_left₀ hr0 hru 2
  have hcorr : 40000*r/(q.val:ℝ)+actual151WeightedPrimeTailConstant*r^2≤
      actual151WeightedEulerPrimeConstant*u^2 := by
    have h1 : 40000*r*u≤40000*u*u := by gcongr
    have h2 := mul_le_mul_of_nonneg_left hpow hK
    dsimp [actual151WeightedEulerPrimeConstant]
    rw [div_eq_mul_inv]
    change 40000*r*u+actual151WeightedPrimeTailConstant*r^2≤_
    nlinarith only [h1,h2]
  have hbase := actual151_one_add_four_le_inv_four hr0 hr1
  have hpowone : 1≤((1-r)⁻¹)^4 := by linarith
  have hcorr0 : 0≤actual151WeightedEulerPrimeConstant*u^2 :=
    mul_nonneg actual151_weighted_euler_prime_constant_nonneg (sq_nonneg _)
  have htotal : 1+4*r+actual151WeightedEulerPrimeConstant*u^2≤
      ((1-r)⁻¹)^4*(1+actual151WeightedEulerPrimeConstant*u^2) := by
    have hh := mul_le_mul_of_nonneg_right hpowone hcorr0
    nlinarith only [hbase,hh]
  have hzreal : z=(r:ℂ) := actual151_prime_monomial_real q.val σ
  have hcast : (1-z) = ((1-r:ℝ):ℂ) := by
    rw [hzreal]
    push_cast
    rfl
  have hnorm : ‖(1-z)⁻¹‖=(1-r)⁻¹ := by
    rw [norm_inv,hcast,Complex.norm_of_nonneg (by linarith : 0≤1-r)]
  have hu2 : (q.val:ℝ)^(-2:ℝ)=u^2 := by
    dsimp [u]
    rw [Real.rpow_neg (Nat.cast_nonneg _) 2,Real.rpow_two,inv_pow]
  have hb := actual151_weighted_local_norm_series χ β γ hpar hM q z hr
  change (∑' n : ℕ,‖lemma153Coefficient χ β γ
    (lemma153GeneralMEulerProduct χ β) (q.val^n)*z^n‖)≤_
  calc
    _ ≤ 1+4*r+40000*r/(q.val:ℝ)+actual151WeightedPrimeTailConstant*r^2 := hb
    _ ≤ 1+4*r+actual151WeightedEulerPrimeConstant*u^2 := by linarith only [hcorr]
    _ ≤ ((1-r)⁻¹)^4*(1+actual151WeightedEulerPrimeConstant*u^2) := htotal
    _ = _ := by rw [←hnorm,←hu2]

/-- Uniform absolute Dirichlet-series majorant for actual A=chi*tau2*varpi.
The exponent four comes from the exact prime term, not the coarse local norm
constant used solely for absolute convergence. -/
theorem actual151_weighted_abs_euler_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2→ℂ) (γ : ℂ) (hpar : Lemma153SmallParameters β γ)
    (hM : lemma152EulerProduct χ β (1-γ)≠0) (σ : ℝ) (hσ : 1<σ) :
    (∑' n : ℕ,‖LSeries.term
      (lemma153Coefficient χ β γ (lemma153GeneralMEulerProduct χ β)) (σ:ℂ) n‖)≤
      actual151WeightedEulerConstant*‖riemannZeta (σ:ℂ)‖^4 := by
  let f : ℕ→ℝ := fun n => ‖LSeries.term
    (lemma153Coefficient χ β γ (lemma153GeneralMEulerProduct χ β)) (σ:ℂ) n‖
  have hsσ : 1<(σ:ℂ).re := by simpa only [Complex.ofReal_re] using hσ
  have hs : Summable f := (lemma153_actual_lseries_summable χ β γ hpar hM (σ:ℂ) hsσ).norm
  have hf1 : f 1=1 := by
    simp [f,LSeries.term,lemma153_coefficient_one χ β γ
      (lemma153GeneralMEulerProduct χ β) (by simpa using hM)]
  have hfmul {m n : ℕ} (h : m.Coprime n) : f (m*n)=f m*f n := by
    dsimp [f]
    rw [lemma153_actual_term_mul χ β γ hpar hM (σ:ℂ) h,norm_mul]
  have hA : HasProd (fun q : Nat.Primes => ∑' n : ℕ,f (q.val^n)) (∑' n : ℕ,f n) :=
    EulerProduct.eulerProduct_hasProd hf1 (fun h => hfmul h)
      (by simpa only [f,norm_norm] using hs) (by simp [f])
  have hZ := ((lemma32_actual_zeta_monomial_euler_hasProd (σ:ℂ) hsσ).norm).pow 4
  have hfinite (S : Finset Nat.Primes) :
      (∏ q∈S,∑' n : ℕ,f (q.val^n))≤actual151WeightedEulerConstant*
        ∏ q∈S,‖(1-lemma32PrimeMonomial q.val (σ:ℂ))⁻¹‖^4 := by
    calc
      _ ≤ ∏ q∈S,(‖(1-lemma32PrimeMonomial q.val (σ:ℂ))⁻¹‖^4 *
          (1+actual151WeightedEulerPrimeConstant*(q.val:ℝ)^(-2:ℝ))) := by
        apply prod_le_prod (fun _ _ => tsum_nonneg (fun _ => norm_nonneg _))
        intro q hq
        simpa only [f,lemma153_actual_prime_power_term χ β γ q.property.pos (σ:ℂ)] using
          actual151_weighted_local_euler_bound χ β γ hpar hM q σ hσ
      _ = (∏ q∈S,‖(1-lemma32PrimeMonomial q.val (σ:ℂ))⁻¹‖^4)*
          (∏ q∈S,(1+actual151WeightedEulerPrimeConstant*(q.val:ℝ)^(-2:ℝ))) := prod_mul_distrib
      _ ≤ (∏ q∈S,‖(1-lemma32PrimeMonomial q.val (σ:ℂ))⁻¹‖^4)*
          actual151WeightedEulerConstant := mul_le_mul_of_nonneg_left
            (actual151_weighted_finite_correction_bound S) (prod_nonneg (fun _ _ => by positivity))
      _ = _ := mul_comm _ _
  exact le_of_tendsto_of_tendsto hA (tendsto_const_nhds.mul hZ)
    (Filter.Eventually.of_forall hfinite)

lemma actual151_norm_term_real (a : ℕ→ℂ) (σ : ℝ) (hσ : σ≠0) (n : ℕ) :
    ‖LSeries.term a (σ:ℂ) n‖=‖a n‖/(n:ℝ)^σ := by
  by_cases hn : n=0
  · simp [hn,Real.zero_rpow hσ]
  · simp only [LSeries.norm_term_eq,hn,if_false,Complex.ofReal_re]

/-- Real positive-term form ready for the finite-prefix Rankin bound. -/
theorem actual151_weighted_abs_real_series_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2→ℂ) (γ : ℂ) (hpar : Lemma153SmallParameters β γ)
    (hM : lemma152EulerProduct χ β (1-γ)≠0) (σ : ℝ) (hσ : 1<σ) :
    (∑' n : ℕ,‖lemma153Coefficient χ β γ (lemma153GeneralMEulerProduct χ β) n‖/(n:ℝ)^σ)≤
      actual151WeightedEulerConstant*‖riemannZeta (σ:ℂ)‖^4 := by
  simpa only [actual151_norm_term_real _ σ (by linarith : σ≠0)] using
    actual151_weighted_abs_euler_bound χ β γ hpar hM σ hσ

end ZhangLS.Spec
