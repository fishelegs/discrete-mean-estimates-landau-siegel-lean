import ZhangLS.Spec.Lemma162CorrectedAnalytic
import ZhangLS.Spec.Lemma162PaperArithmeticBridge
import ZhangLS.Spec.Lemma153RamifiedStrip

/-! Contour-usable bounds: the unramified raw product is absolutely bounded,
and the actual finite ramified factors yield the explicit loglog^18 strip loss. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex Filter Topology
open scoped Classical
set_option maxHeartbeats 2500000

noncomputable def lemma162UnramifiedProductBound : ℝ := Real.exp (∑' q : Nat.Primes, lemma162UnramifiedMajorant q)

lemma lemma162_unramified_product_bound_pos : 0<lemma162UnramifiedProductBound := Real.exp_pos _

lemma lemma162_raw_euler_separated_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re=0) (γ : ℂ) (hγ : γ.re=0) (s : ℂ) (hs : 9/10≤s.re) :
    ‖lemma162RawEulerProduct χ β γ s‖≤lemma162UnramifiedProductBound*
      ‖∏ p ∈ D.primeFactors, (1-lemma32PrimeMonomial p s)^2‖ := by
  let g : Nat.Primes → ℂ := fun q => if q.val∣D then 1 else lemma162RawPrimeCorrection χ β γ q s
  have hge (q : Nat.Primes) : ‖g q-1‖≤lemma162UnramifiedMajorant q := by
    dsimp [g]
    split_ifs with hq
    · simp only [sub_self,norm_zero]
      exact lemma162_unramified_majorant_nonneg q
    · exact lemma162_unramified_raw_error_majorized χ β hβ γ hγ q hq s hs
  have hgm : Multipliable g := by
    have hh := lemma162_unramified_majorant_summable.of_nonneg_of_le (fun _ => norm_nonneg _) hge
    simpa only [add_sub_cancel] using multipliable_one_add_of_summable hh
  have hgn : ‖∏' q : Nat.Primes, g q‖≤lemma162UnramifiedProductBound := by
    apply le_of_tendsto hgm.hasProd.norm
    filter_upwards with S
    calc
      _ ≤ ∏ q ∈ S, (1+lemma162UnramifiedMajorant q) := by
        apply prod_le_prod (fun _ _ => norm_nonneg _)
        intro q hq
        have hh := norm_le_norm_sub_add (g q) (1:ℂ)
        rw [norm_one] at hh
        linarith [hge q]
      _ ≤ Real.exp (∑ q ∈ S, lemma162UnramifiedMajorant q) :=
        Real.prod_one_add_le_exp_sum S lemma162_unramified_majorant_nonneg
      _ ≤ lemma162UnramifiedProductBound := by
        apply Real.exp_le_exp.mpr
        exact lemma162_unramified_majorant_summable.sum_le_tsum S
          (fun q _ => lemma162_unramified_majorant_nonneg q)
  have hf := lemma153_finite_ite_hasProd (lemma153PrimeDivisorSet D)
    (fun q : Nat.Primes => (1-lemma32PrimeMonomial q.val s)^2)
  have hp : HasProd (fun q : Nat.Primes => lemma162RawPrimeCorrection χ β γ q s)
      ((∏ q ∈ lemma153PrimeDivisorSet D, (1-lemma32PrimeMonomial q.val s)^2)*(∏' q : Nat.Primes, g q)) := by
    apply (hf.mul hgm.hasProd).congr_fun
    intro q
    simp only [lemma153_mem_prime_divisor_set χ.modulus_ne_zero q]
    by_cases hq : q.val∣D
    · have hv := χ.evalNat_eq_zero_of_dvd_modulus hq q.property.ne_one
      simp [g,hq,lemma162RawPrimeCorrection,hv]
    · simp [g,hq]
  have he := hp.unique (lemma162_raw_euler_multipliable χ β hβ γ hγ s hs).hasProd
  change _ = lemma162RawEulerProduct χ β γ s at he
  rw [←he,norm_mul,lemma153_prime_divisor_set_prod χ.modulus_ne_zero (fun p => (1-lemma32PrimeMonomial p s)^2)]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hgn
    (norm_nonneg (∏ p ∈ D.primeFactors, (1-lemma32PrimeMonomial p s)^2))

lemma lemma162_corrected_strip_bound {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 3≤D)
    (β : ℂ) (hβ : β.re=0) (γ : ℂ) (hγ : γ.re=0) (s : ℂ)
    (hs : 9/10≤s.re) (hstrip : 1-(Real.log D)⁻¹≤s.re) :
    ‖lemma162CorrectedEulerProduct χ β γ s‖≤
      (lemma162UnramifiedProductBound*(Real.exp (3/Real.log 2))^2)*
        (1+Real.log (Real.log D))^18/‖lemma161Star χ β (1-γ)‖ := by
  rw [lemma162CorrectedEulerProduct,norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  apply (lemma162_raw_euler_separated_bound χ β hβ γ hγ s hs).trans
  have h := lemma153_ramified_strip_product hD s hstrip
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h lemma162_unramified_product_bound_pos.le

noncomputable def lemma162ThinStripConstant : ℝ :=
  2*lemma162UnramifiedProductBound*(Real.exp (3/Real.log 2))^2/lemma161MainLowerBound

lemma lemma162_thin_strip_constant_pos : 0<lemma162ThinStripConstant := by
  unfold lemma162ThinStripConstant
  have h1 := lemma162_unramified_product_bound_pos
  have h2 := lemma161_main_lower_bound_pos
  positivity

/-- Absolute strip constant fixed before c′. The threshold is chosen before
D, χ, j and s; the loglog loss is visible rather than hidden in O(1). -/
theorem lemma162_paper_thin_strip_bound (c : ℝ) (hc : 0<c) :
    ∃ D₀ : ℕ, 3≤D₀ ∧ lemma23SectionFourModulusThreshold≤D₀ ∧
      ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D, ∀ j : Fin 2, ∀ s : ℂ,
        9/10≤s.re → 1-(Real.log D)⁻¹≤s.re →
          ‖lemma162CorrectedEulerProduct χ (lemma52PaperBetaOne D c) (lemma162PaperShift D c j) s‖≤
            lemma162ThinStripConstant*(1+Real.log (Real.log D))^18 := by
  obtain ⟨D₁,hD₁,hstar⟩ := lemma161_uniform_nonzero c hc
  obtain ⟨D₂,hsection,hshift⟩ := lemma52_exists_shift_threshold hc
  refine ⟨max 3 (max D₁ D₂),le_max_left _ _,hsection.trans
    ((le_max_right D₁ D₂).trans (le_max_right 3 _)),?_⟩
  intro D hD χ j s hs hstrip
  have h1 : D₁≤D := (le_max_left _ _).trans ((le_max_right _ _).trans hD)
  have h2 : D₂≤D := (le_max_right _ _).trans ((le_max_right _ _).trans hD)
  have h3 : 3≤D := (le_max_left _ _).trans hD
  have hL := (lemma44_parameters_at_explicit_threshold (hsection.trans h2)).1
  have ha := (lemma44_alpha_pos_le_one hL).1
  have hsmall := hshift D h2
  have hγ := lemma162_paper_shift_re D c j
  have hγn : ‖lemma162PaperShift D c j‖≤3*lemma44PaperAlpha D := lemma83_paper_beta_norm hL hc hsmall _
  have hdist : ‖(1-lemma162PaperShift D c j)-1‖<5*lemma44PaperAlpha D := by
    rw [show (1-lemma162PaperShift D c j)-1 = -lemma162PaperShift D c j by ring,norm_neg]
    linarith
  have hN := hstar D h1 χ _ hdist
  apply (lemma162_corrected_strip_bound χ h3 _ (lemma161_paper_beta_re D c) _ hγ s hs hstrip).trans
  calc
    _ ≤ (lemma162UnramifiedProductBound*(Real.exp (3/Real.log 2))^2)*
        (1+Real.log (Real.log D))^18/(lemma161MainLowerBound/2) := by
      apply div_le_div_of_nonneg_left
      · exact mul_nonneg (mul_nonneg lemma162_unramified_product_bound_pos.le (sq_nonneg _)) (by positivity)
      · exact div_pos lemma161_main_lower_bound_pos (by norm_num)
      · exact hN
    _ = _ := by unfold lemma162ThinStripConstant; ring

end ZhangLS.Spec
