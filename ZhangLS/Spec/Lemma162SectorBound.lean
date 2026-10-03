import ZhangLS.Spec.Lemma162ThinStripBound
import ZhangLS.Spec.Lemma32RamificationNorm

/-! An absolute bound on the actual corrected V in a neighborhood of 1.
The infinite vertical strip keeps its explicit loglog loss in the preceding
module; the local sector needed for Cauchy has an absolute bound. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset Filter Topology Set
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma162_ramified_sector_bound (D : ℕ) (s : ℂ) (hs : 0<s.re)
    (hphase : |s.im| *lemma23PaperL D≤1) :
    ‖∏ p ∈ D.primeFactors, (1-lemma32PrimeMonomial p s)^2‖≤1 := by
  rw [norm_prod]
  apply prod_le_one (fun _ _ => norm_nonneg _)
  intro p hp
  rw [norm_pow]
  apply pow_le_one₀ (norm_nonneg _) _
  apply lemma32_ramified_prime_factor_norm (Nat.prime_of_mem_primeFactors hp).one_lt s hs
  have hl : 0≤Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le)
  have hlog : Real.log (p:ℝ)≤lemma23PaperL D :=
    Real.log_le_log (Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors hp).pos)
      (Nat.cast_le.mpr (Nat.le_of_mem_primeFactors hp))
  calc
    _ = |s.im| *Real.log (p:ℝ) := by rw [abs_mul,abs_of_nonneg hl]
    _ ≤ |s.im| *lemma23PaperL D := mul_le_mul_of_nonneg_left hlog (abs_nonneg _)
    _ ≤ 1 := hphase

lemma lemma162_raw_sector_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re=0) (γ : ℂ) (hγ : γ.re=0) (s : ℂ)
    (hs : 9/10≤s.re) (hphase : |s.im| *lemma23PaperL D≤1) :
    ‖lemma162RawEulerProduct χ β γ s‖≤lemma162UnramifiedProductBound := by
  apply (lemma162_raw_euler_separated_bound χ β hβ γ hγ s hs).trans
  exact mul_le_of_le_one_right lemma162_unramified_product_bound_pos.le
    (lemma162_ramified_sector_bound D s (by linarith) hphase)

noncomputable def lemma162SectorConstant : ℝ :=
  2*lemma162UnramifiedProductBound/lemma161MainLowerBound

lemma lemma162_sector_constant_pos : 0<lemma162SectorConstant := by
  unfold lemma162SectorConstant
  exact div_pos (mul_pos (by norm_num) lemma162_unramified_product_bound_pos)
    lemma161_main_lower_bound_pos

/-- The absolute constant is fixed before c′; the threshold is fixed before
D, χ, j and s. It applies to the actual corrected Euler product. -/
theorem lemma162_paper_sector_bound (c : ℝ) (hc : 0<c) :
    ∃ D₀ : ℕ, 3≤D₀ ∧ lemma23SectionFourModulusThreshold≤D₀ ∧
      ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D, ∀ j : Fin 2, ∀ s : ℂ,
        9/10≤s.re → |s.im| *lemma23PaperL D≤1 →
          ‖lemma162CorrectedEulerProduct χ (lemma52PaperBetaOne D c) (lemma162PaperShift D c j) s‖≤
            lemma162SectorConstant := by
  obtain ⟨D₁,hD₁,hstar⟩ := lemma161_uniform_nonzero c hc
  obtain ⟨D₂,hsection,hshift⟩ := lemma52_exists_shift_threshold hc
  refine ⟨max 3 (max D₁ D₂),le_max_left _ _,hsection.trans
    ((le_max_right D₁ D₂).trans (le_max_right 3 _)),?_⟩
  intro D hD χ j s hs hphase
  have h1 : D₁≤D := (le_max_left _ _).trans ((le_max_right _ _).trans hD)
  have h2 : D₂≤D := (le_max_right _ _).trans ((le_max_right _ _).trans hD)
  have hL := (lemma44_parameters_at_explicit_threshold (hsection.trans h2)).1
  have ha := (lemma44_alpha_pos_le_one hL).1
  have hγn : ‖lemma162PaperShift D c j‖≤3*lemma44PaperAlpha D :=
    lemma83_paper_beta_norm hL hc (hshift D h2) _
  have hdist : ‖(1-lemma162PaperShift D c j)-1‖<5*lemma44PaperAlpha D := by
    rw [show (1-lemma162PaperShift D c j)-1 = -lemma162PaperShift D c j by ring,norm_neg]
    linarith
  have hN := hstar D h1 χ _ hdist
  rw [lemma162CorrectedEulerProduct,norm_div]
  calc
    _ ≤ lemma162UnramifiedProductBound/(lemma161MainLowerBound/2) :=
      div_le_div₀ lemma162_unramified_product_bound_pos.le (lemma162_raw_sector_bound χ _
        (lemma161_paper_beta_re D c) _ (lemma162_paper_shift_re D c j) s hs hphase)
        (div_pos lemma161_main_lower_bound_pos (by norm_num)) hN
    _ = _ := by unfold lemma162SectorConstant; ring

lemma lemma162_disk_in_sector {D : ℕ} (hL : 3≤lemma23PaperL D) (s : ℂ)
    (hs : ‖s-1‖≤(10*lemma23PaperL D)⁻¹) :
    9/10<s.re ∧ |s.im| *lemma23PaperL D≤1 := by
  have hL0 : 0<lemma23PaperL D := by linarith
  have hr : (10*lemma23PaperL D)⁻¹≤1/30 := by
    simpa only [one_div] using inv_anti₀ (by norm_num : (0:ℝ)<30) (by linarith : 30≤10*lemma23PaperL D)
  have hre := (Complex.abs_re_le_norm (s-1)).trans (hs.trans hr)
  simp only [Complex.sub_re,Complex.one_re] at hre
  have him : |s.im|≤(10*lemma23PaperL D)⁻¹ := by
    simpa using (Complex.abs_im_le_norm (s-1)).trans hs
  refine ⟨by have := (abs_le.mp hre).1; linarith,?_⟩
  calc
    _ ≤ (10*lemma23PaperL D)⁻¹*lemma23PaperL D := mul_le_mul_of_nonneg_right him hL0.le
    _ = 1/10 := by field_simp
    _ ≤ 1 := by norm_num

/-- Explicit closed disk for Cauchy: radius 1/(10 log D), absolute bound. -/
theorem lemma162_paper_disk_bound (c : ℝ) (hc : 0<c) :
    ∃ D₀ : ℕ, 3≤D₀ ∧ lemma23SectionFourModulusThreshold≤D₀ ∧
      ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D, ∀ j : Fin 2,
        AnalyticOnNhd ℂ
          (lemma162CorrectedEulerProduct χ (lemma52PaperBetaOne D c) (lemma162PaperShift D c j))
          (Metric.closedBall 1 ((10*lemma23PaperL D)⁻¹)) ∧
        ∀ s : ℂ, ‖s-1‖≤(10*lemma23PaperL D)⁻¹ →
          ‖lemma162CorrectedEulerProduct χ (lemma52PaperBetaOne D c) (lemma162PaperShift D c j) s‖≤
            lemma162SectorConstant := by
  obtain ⟨D₀,hD₀,hsection,hbound⟩ := lemma162_paper_sector_bound c hc
  refine ⟨D₀,hD₀,hsection,?_⟩
  intro D hD χ j
  have hL := (lemma44_parameters_at_explicit_threshold (hsection.trans hD)).1
  refine ⟨?_,?_⟩
  · intro s hs
    have hsn : ‖s-1‖≤(10*lemma23PaperL D)⁻¹ := by simpa [Metric.mem_closedBall,dist_eq_norm] using hs
    exact lemma162_corrected_euler_analytic χ _ (lemma161_paper_beta_re D c) _
      (lemma162_paper_shift_re D c j) s (lemma162_disk_in_sector hL s hsn).1
  · intro s hs
    have hh := lemma162_disk_in_sector hL s hs
    exact hbound D hD χ j s hh.1.le hh.2

end ZhangLS.Spec
