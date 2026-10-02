import ZhangLS.Spec.Lemma153DownstreamPaper
/-! Actual M normalization has an absolute product bound; exact zero-center
cancellation retains every ramified prime. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset Filter Topology
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma153_M_uniform_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (hβ : ∀ i, (β i).re=0) (s : ℂ) (hs : 9/10≤s.re) :
    ‖lemma152EulerProduct χ β s‖≤lemma152ProductBound := by
  have hp := (lemma152_euler_product_multipliable χ β hβ s hs).hasProd
  apply le_of_tendsto hp.norm
  filter_upwards with S
  calc
    _ ≤ ∏ q ∈ S, (1+lemma152CorrectionConstant*(q.val:ℝ)^(-(19/10:ℝ))) := by
      apply prod_le_prod (fun _ _ => norm_nonneg _)
      exact fun q _ => lemma152_prime_norm_le χ β hβ q s hs
    _ ≤ _ := lemma152_finite_majorant_product_le S

lemma lemma153_general_M_normalization_uniform_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (hβ : ∀ i, (β i).re=0) (γ : ℂ) (hγ : γ.re=0) :
    ‖lemma153GeneralMEulerProduct χ β 1 1 (1-γ)‖≤lemma152ProductBound := by
  rw [lemma153_general_m_baseline]
  apply lemma153_M_uniform_bound χ β hβ
  simp [hγ]
  norm_num

lemma lemma153_actual_U_center_uniform_bound {D : ℕ} (hD : D≠0)
    (χ : RealPrimitiveCharacter D) (β : Fin 2 → ℂ) (γ : ℂ)
    (hpar : Lemma153SmallParameters β γ) :
    ‖lemma153EulerProduct χ β γ 1‖≤lemma153UnramifiedProductBound := by
  have hp := (lemma153_euler_product_multipliable hD χ β γ hpar 1 (by norm_num)).hasProd
  apply le_of_tendsto hp.norm
  filter_upwards with S
  calc
    _ ≤ ∏ q ∈ S, (1+100000*(q.val:ℝ)^(-(3/2:ℝ))) := by
      apply prod_le_prod (fun _ _ => norm_nonneg _)
      exact fun q _ => lemma153_prime_center_norm_le χ β γ hpar q
    _ ≤ _ := lemma153_finite_center_majorant_product_le S

lemma lemma153_main_U_uniform_bound {D : ℕ} (hD : D≠0) (χ : RealPrimitiveCharacter D) :
    ‖lemma153MainTerm χ‖≤lemma153UnramifiedProductBound := by
  rw [←lemma153_zero_product_equals_main hD]
  exact lemma153_actual_U_center_uniform_bound hD χ _ _ lemma153_zero_parameters

lemma lemma153_ramified_totient_hasProd {D : ℕ} (hD : D≠0) :
    HasProd (fun q : Nat.Primes => if q.val ∣ D then 1-(q.val:ℂ)⁻¹ else 1)
      ((Nat.totient D:ℂ)/(D:ℂ)) := by
  have hp := lemma153_finite_ite_hasProd (lemma153PrimeDivisorSet D)
    (fun q : Nat.Primes => 1-(q.val:ℂ)⁻¹)
  have he : (∏ q ∈ lemma153PrimeDivisorSet D, (1-(q.val:ℂ)⁻¹)) =
      (Nat.totient D:ℂ)/(D:ℂ) := by
    rw [lemma153_prime_divisor_set_prod hD (fun p : ℕ => 1-(p:ℂ)⁻¹)]
    apply (eq_div_iff (Nat.cast_ne_zero.mpr hD)).mpr
    have hh := congrArg (fun r : ℚ => (r:ℂ)) (Nat.totient_eq_mul_prod_factors D)
    push_cast at hh
    simpa [mul_comm] using hh.symm
  rw [he] at hp
  exact hp.congr_fun (fun q => by simp only [lemma153_mem_prime_divisor_set hD q])

lemma lemma153_zero_MU_prime_cancellation {D : ℕ} (χ : RealPrimitiveCharacter D) (q : Nat.Primes) :
    lemma152PrimeFactor χ (fun _ => 0) q 1 * lemma153PrimeFactor χ (fun _ => 0) 0 q 1 =
      (if q.val ∣ D then 1-(q.val:ℂ)⁻¹ else 1)*
        lemma171LocalCorrection χ q.val (lemma32PrimeMonomial q.val 1) := by
  have hu : ‖(q.val:ℂ)⁻¹‖<1 := by
    rw [norm_inv,Complex.norm_natCast]
    exact (inv_lt_one₀ (Nat.cast_pos.mpr q.property.pos)).mpr (by exact_mod_cast q.property.one_lt)
  rw [lemma153_zero_center_factor,lemma153_prime_zero_center,
    lemma83_prime_monomial_one q.property.pos,lemma171_local_correction χ q.property _ hu]
  by_cases hd : q.val ∣ D
  · simp [hd,pow_two]
  · have hx : ‖(q.val:ℂ)^(-2:ℤ)‖<1 := by
      simpa [zpow_neg,zpow_ofNat,norm_pow] using pow_lt_one₀ (norm_nonneg ((q.val:ℂ)⁻¹)) hu (by norm_num : (2:ℕ)≠0)
    have hxn := lemma83_one_sub_ne_zero hx
    have hχn : 1-χ.evalNat q.val*(q.val:ℂ)^(-2:ℤ)≠0 :=
      lemma83_one_sub_ne_zero (lt_of_le_of_lt (by
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (χ.evalNat_norm_le_one _)) hx)
    simp only [if_neg hd,one_mul]
    simp only [zpow_neg,zpow_ofNat] at hxn hχn ⊢
    field_simp [hχn,hxn]
    exact div_self (by simpa only [div_eq_mul_inv] using hχn)

/-- Exact center cancellation corresponding to TeX4367–4370. -/
lemma lemma153_zero_MU_exact_cancellation {D : ℕ} (hD : D≠0)
    (χ : RealPrimitiveCharacter D) :
    lemma152MainTerm χ*lemma153MainTerm χ =
      ((Nat.totient D:ℂ)/(D:ℂ))*lemma171AnalyticCorrection D 1 := by
  have hm := (lemma152_euler_product_multipliable χ (fun _=>0) (by simp) 1 (by norm_num)).hasProd
  have hu := (lemma153_euler_product_multipliable hD χ (fun _=>0) 0 lemma153_zero_parameters 1 (by norm_num)).hasProd
  have ha := (lemma153_ramified_totient_hasProd hD).mul (lemma171_local_corrections_hasProd χ 1 (by norm_num))
  have he := ((hm.mul hu).congr_fun (fun q => (lemma153_zero_MU_prime_cancellation χ q).symm)).unique ha
  simpa only [←lemma153_zero_center_equals_main,←lemma153_zero_product_equals_main hD] using he

lemma lemma153_zero_MU_LDeriv_main_term {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1<D) :
    lemma152MainTerm χ*lemma153MainTerm χ*LDerivAtOne χ^2 =
      (lemma171MainTerm χ:ℂ)*((Nat.totient D:ℂ)/(D:ℂ)) := by
  rw [lemma153_zero_MU_exact_cancellation (by omega),lemma171_main_term_complex χ hD]
  ring

end ZhangLS.Spec
