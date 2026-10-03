import ZhangLS.Spec.Proposition71PrimeGaussRestoration
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Actual prime-summed Gauss correction and nonunit restoration

The two literal correction series are bounded through every original short
index and prime. The strict PT⁻² count, exact prime mass, and a proved log/T
rate supply the saving; no p-divisible branch or outer weight is discarded.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset Filter
open scoped Classical Topology
set_option maxHeartbeats 4500000
set_option maxRecDepth 4096

noncomputable def proposition71AdditiveDeltaMean (D : ℕ) (c : ℝ) (a₁ a₂ : ℕ → ℂ) : ℂ :=
  ∑p : lemma33PrimeIndex D,
    (-I*(((p.val : ℝ)*lemma51PaperT0 D : ℝ) : ℂ)^lemma52PaperBetaThree D c)*
      proposition71PrimeAdditiveDeltaMean (p := p.val) D c a₁ a₂

lemma proposition71_prime_count_times_P_le_mass (D : ℕ) :
    (Fintype.card (lemma33PrimeIndex D) : ℝ)*lemma23PaperP D≤lemma33ActualPrimeMass D := by
  calc
    _=∑_p : lemma33PrimeIndex D, lemma23PaperP D := by simp
    _≤∑p : lemma33PrimeIndex D, (p.val : ℝ) :=
      sum_le_sum (fun p hp => ((lemma33_mem_prime_window.mp p.property).2.1).le)
    _=_ := rfl

/-- All genuine corrections, including every p-divisible long term, are
bounded by actual mass · L^575 · T⁻². -/
theorem proposition71_original_gauss_restoration_bound {D : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) {B₁ B₂ : ℝ} (hB₁ : 0≤B₁) (hB₂ : 0≤B₂)
    (c : ℝ) (a₁ a₂ : ℕ → ℂ) (ha₁ : Lemma81AdmissibleSequence D B₁ a₁)
    (ha₂ : ∀n, ‖a₂ n‖≤B₂) :
    ‖proposition71OriginalDeltaOneMean D c a₁ a₂-proposition71AdditiveDeltaMean D c a₁ a₂‖≤
      7*tauDeltaAbsoluteConstant*B₁*B₂*lemma33ActualPrimeMass D*
        lemma23PaperL D^575*lemma56PaperT D^(-2 : ℤ) := by
  have hL3 : 3≤lemma23PaperL D := by linarith
  have hLp : 0< lemma23PaperL D := by linarith
  have hP : 0< lemma23PaperP D := Real.exp_pos _
  have hC := tauDelta_absolute_constant_pos.le
  have hM : 0≤lemma33ActualPrimeMass D := by unfold lemma33ActualPrimeMass; exact sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hcount : (Fintype.card (lemma33PrimeIndex D) : ℝ)≤lemma33ActualPrimeMass D/lemma23PaperP D :=
    (le_div_iff₀ hP).mpr (proposition71_prime_count_times_P_le_mass D)
  have hshort := proposition71_strict_indices_card_le_cutoff D
  have hcut0 : 0≤lemma81Cutoff D := (Nat.cast_nonneg _).trans hshort
  rw [proposition71_original_delta_mean_eq_prime_average hD hB₁ c a₁ a₂ ha₁]
  unfold proposition71PrimeAveragedDeltaMean proposition71AdditiveDeltaMean
  rw [←sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _≤∑_p : lemma33PrimeIndex D,
        7*tauDeltaAbsoluteConstant*B₁*B₂*((lemma81PolynomialIndices D).card : ℝ)*lemma23PaperL D^575 := by
      apply sum_le_sum
      intro p hp
      have hp' : p.val∈lemma56PaperPrimes D := by simpa only [lemma35_prime_windows_eq] using p.property
      have hb := proposition71_prime_gauss_restoration_bound hD hL hp' hB₁ hB₂ c a₁ a₂ ha₁ ha₂
      have hw : ‖-I*(((p.val : ℝ)*lemma51PaperT0 D : ℝ) : ℂ)^lemma52PaperBetaThree D c‖=1 := by
        rw [norm_mul,norm_neg,norm_I,lemma81_actual_phase_norm_one c hLp,one_mul]
      rw [mul_assoc,←mul_sub,norm_mul,hw,one_mul]
      exact hb
    _=(7*tauDeltaAbsoluteConstant*B₁*B₂*((lemma81PolynomialIndices D).card : ℝ)*lemma23PaperL D^575)*
        (Fintype.card (lemma33PrimeIndex D) : ℝ) := by simp [mul_comm]
    _≤(7*tauDeltaAbsoluteConstant*B₁*B₂*lemma81Cutoff D*lemma23PaperL D^575)*
        (lemma33ActualPrimeMass D/lemma23PaperP D) := by gcongr
    _=_ := by
      unfold lemma81Cutoff
      field_simp

/-- Uniform original-weight o(prime mass) for both Gauss corrections. There is
no character assumption or (A) in this correction estimate itself. -/
theorem proposition71_original_gauss_restoration_little_o
    (B₁ B₂ : ℝ) (hB₁ : 0<B₁) (hB₂ : 0<B₂) (ε : ℝ) (hε : 0<ε) :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D → ∀ c : ℝ,
      ∀ a₁ a₂ : ℕ → ℂ, Lemma81AdmissibleSequence D B₁ a₁ →
      Lemma81AdmissibleSequence D B₂ a₂ →
      ‖proposition71OriginalDeltaOneMean D c a₁ a₂-proposition71AdditiveDeltaMean D c a₁ a₂‖≤
        ε*lemma33ActualPrimeMass D := by
  let C := 7*tauDeltaAbsoluteConstant*B₁*B₂
  have hC : 0<C := by dsimp [C]; exact mul_pos (mul_pos (mul_pos (by norm_num) tauDelta_absolute_constant_pos) hB₁) hB₂
  have hsmall := (isLittleO_log_rpow_rpow_atTop (s := (1 : ℝ)) (575 : ℝ) (by norm_num)).bound
    (show 0<ε/C by positivity)
  have hnat := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hsmall
  obtain ⟨Na,hNa⟩ := eventually_atTop.mp hnat
  refine ⟨max 2 (max Na ⌈Real.exp 2000⌉₊),le_max_left _ _,?_⟩
  intro D hD c a₁ a₂ ha₁ ha₂
  have hD2 : 2≤D := (le_max_left _ _).trans hD
  have hDa := (le_max_left _ _).trans ((le_max_right _ _).trans hD)
  have hDe := (le_max_right _ _).trans ((le_max_right _ _).trans hD)
  have hDp : 0<(D : ℝ) := by exact_mod_cast (show 0<D by omega)
  have hL : 2000≤lemma23PaperL D := by
    have he : Real.exp 2000≤(D : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hDe)
    simpa only [lemma23PaperL,Real.log_exp] using Real.log_le_log (Real.exp_pos 2000) he
  have hLp : 0< lemma23PaperL D := by linarith
  have hpoly : lemma23PaperL D^575≤(ε/C)*(D : ℝ) := by
    have hh := hNa D hDa
    simp only [Real.rpow_natCast,Real.rpow_ofNat,Real.rpow_one,Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (Real.log_natCast_nonneg D) 575),
      abs_of_nonneg (Nat.cast_nonneg D : (0 : ℝ)≤D)] at hh
    exact hh
  have hT : lemma56PaperT D^(-2 : ℤ)≤(D : ℝ)⁻¹ := by
    simpa [Real.exp_neg,lemma23PaperL,Real.exp_log hDp] using
      lemma81_T_inverse_square_le_exp_neg_log (by linarith : 3≤lemma23PaperL D)
  have hs : C*lemma23PaperL D^575*lemma56PaperT D^(-2 : ℤ)≤ε := by
    calc
      _≤C*((ε/C)*(D : ℝ))*(D : ℝ)⁻¹ := by gcongr
      _=_ := by field_simp
  have hb := proposition71_original_gauss_restoration_bound (by omega) hL hB₁.le hB₂.le c a₁ a₂ ha₁ ha₂.1
  have hM : 0≤lemma33ActualPrimeMass D := by unfold lemma33ActualPrimeMass; exact sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  apply hb.trans
  have hh := mul_le_mul_of_nonneg_right hs hM
  convert hh using 1 <;> dsimp [C] <;> ring

/-- The actual Θ₁ has now been reduced to the unrestricted additive Δ₁ mean.
The primitive Gauss corrections and nonunit restoration have been proved small. -/
theorem proposition71_original_additive_delta_reduction :
    ∀ B₁ B₂ : ℝ, 0<B₁ → 0<B₂ → ∀ ε : ℝ, 0<ε →
      ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ → ∀ c : ℝ,
      ∀ a₁ a₂ : ℕ → ℂ, Lemma81AdmissibleSequence D B₁ a₁ → Lemma81AdmissibleSequence D B₂ a₂ →
      ‖lemma81ThetaOne χ c a₁ a₂-proposition71AdditiveDeltaMean D c a₁ a₂‖≤ε*lemma33ActualPrimeMass D := by
  intro B₁ B₂ hB₁ hB₂ ε hε
  obtain ⟨Df,hDf,hfront⟩ := proposition71_original_delta_one_reduction B₁ B₂ hB₁ hB₂ (ε/2) (by positivity)
  obtain ⟨Dg,hDg,hgauss⟩ := proposition71_original_gauss_restoration_little_o B₁ B₂ hB₁ hB₂ (ε/2) (by positivity)
  refine ⟨max Df Dg,hDf.trans (le_max_left _ _),?_⟩
  intro D hD χ hA c a₁ a₂ ha₁ ha₂
  have hf := hfront D ((le_max_left _ _).trans hD) χ hA c a₁ a₂ ha₁ ha₂
  have hg := hgauss D ((le_max_right _ _).trans hD) c a₁ a₂ ha₁ ha₂
  have ht := dist_triangle (lemma81ThetaOne χ c a₁ a₂) (proposition71OriginalDeltaOneMean D c a₁ a₂)
    (proposition71AdditiveDeltaMean D c a₁ a₂)
  simp only [dist_eq_norm] at ht
  exact ht.trans ((add_le_add hf hg).trans_eq (by ring))

end ZhangLS.Spec
