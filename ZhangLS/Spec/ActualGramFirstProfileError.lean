import ZhangLS.Spec.ActualGramMainKernelBridge
import ZhangLS.Spec.ActualGramMovingErrorIntegral
import ZhangLS.Spec.Proposition71Support

/-! Actual first profile error from the proved original K1 bounds, including
all moving small-x layers. The fixed smoothing density is mu=6, whose scaled
shift is exactly 3*pi*i/2 before any asymptotic estimate. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Classical Interval

theorem actualGram_first_profile_error_uniform (c : ℝ) (hc : 0<c) :
    ∃ N : ℕ, 2≤N ∧ ∀ D : ℕ, N≤D → ∀ χ : RealPrimitiveCharacter D,
    NormalizedAssumptionA χ → ∀ j : Fin 3, ∀ q : ℕ, 0<q →
    ∀ f f' f'' : ℝ → ℂ, ∀ b C : ℝ, 0≤C →
    (∀ x, HasDerivAt f (f' x) x) → (∀ x, HasDerivAt f' (f'' x) x) → Continuous f'' →
    (∀ v, b≤v → f v=0) → f' b=0 →
    let B := Real.log (lemma23PaperP D)
    let t := Real.log q/B
    let ell : ℂ := 3*I*(Real.pi : ℂ)/2
    t≤b →
    (∀ v ∈ Icc t b, ‖actualGramRampDensity ell f f' f'' v‖≤C) →
    (∀ v ∈ Icc t b, Real.exp (B*v)/(q : ℝ)<lemma81Cutoff D) →
    ‖actualGramFirst χ c j (fun n => f (Real.log n/B)) q -
      (LDerivAtOne χ/(B : ℂ))*(-f' t-(B : ℂ)*lemma83PaperBeta D c j*f t)‖ ≤
      (C*actualGramFirstBoundaryBudget D*(Real.log (lemma56PaperT D)/B)+
        (C*lemma82ErrorConstant*lemma23PaperL D^(-6 : ℤ))*(b-t))/B := by
  obtain ⟨N,hN,hth⟩ := lemma82_uniform_threshold c hc
  refine ⟨N,hN,?_⟩
  intro D hDN χ hA j q hq f f' f'' b C hC hf hf' hf'' hz hfpb
  dsimp only
  let B : ℝ := Real.log (lemma23PaperP D)
  let t : ℝ := Real.log q/B
  let ell : ℂ := 3*I*(Real.pi : ℂ)/2
  let h := actualGramRampDensity ell f f' f''
  let K : ℝ → ℂ := fun v => lemma82ShiftedSum χ c j 6 (Real.exp (B*v)/(q : ℝ))
  let M : ℝ → ℂ := fun v => lemma82MainTerm D c j 6 (Real.exp (B*v)/(q : ℝ))
  intro htb hbound hcut
  have hparams := hth D hDN
  have hD : 1<D := by omega
  have hL : 2000≤lemma23PaperL D := hparams.2.1
  have hLp : 0<lemma23PaperL D := by linarith
  have hsmall := hparams.2.2.1
  have hB : 0<B := actualGram_original_log_scale_pos hD
  have hqR : (0 : ℝ)<q := Nat.cast_pos.mpr hq
  have hell : (B : ℂ)*lemma82SmoothingBeta D 6=ell := actualGram_original_mu6_scaled hD
  have hT : 0≤Real.log (lemma56PaperT D) := by
    rw [lemma56PaperT,Real.log_exp]
    exact Real.rpow_nonneg (by linarith) _
  have hδ : 0≤Real.log (lemma56PaperT D)/B := div_nonneg hT hB.le
  have hcden : Continuous h := actualGram_ramp_density_continuous ell f f' f'' hf hf' hf''
  have hkc : ContinuousOn K (Icc t b) := by
    have hh := actualGram_log_smoothed_continuousOn D
      (fun n => χ.evalNat n/(n : ℂ)^(1-lemma83PaperBeta D c j))
      (lemma82SmoothingBeta D 6) hB hqR (fun v hv => (hcut v hv).le)
    simpa only [actualGram_log_kernel_first] using hh
  have hmc : Continuous M := by
    dsimp [M]
    simp_rw [actualGram_first_main_kernel D c j 6 hB hqR]
    fun_prop
  have hie : IntervalIntegrable (fun v => h v*(K v-LDerivAtOne χ*M v)) volume t b :=
    (hcden.continuousOn.mul (hkc.sub (continuous_const.mul hmc).continuousOn)).intervalIntegrable_of_Icc htb
  have hiK : IntervalIntegrable (fun v => h v*K v) volume t b :=
    (hcden.continuousOn.mul hkc).intervalIntegrable_of_Icc htb
  have hiM : IntervalIntegrable (fun v => h v*(LDerivAtOne χ*M v)) volume t b :=
    (hcden.mul (continuous_const.mul hmc)).intervalIntegrable t b
  have hactual : actualGramFirst χ c j (fun n => f (Real.log n/B)) q =
      (B : ℂ)⁻¹*(∫ v in t..b, h v*K v) := by
    have hh := actualGram_log_superposition_from_product D
      (fun n => χ.evalNat n/(n : ℂ)^(1-lemma83PaperBeta D c j))
      (lemma82SmoothingBeta D 6) f f' f'' hB hqR htb hf hf' hf'' hz hfpb
      (fun v hv => (hcut v hv).le)
    simpa only [actualGramFirst,Nat.cast_mul,actualGram_log_kernel_first,hell] using hh
  have hmain : (∫ v in t..b, h v*M v) =
      -f' t-(B : ℂ)*lemma83PaperBeta D c j*f t := by
    have hh := actualGram_first_main_superposition D c j 6 f f' f'' hB hqR
      hf hf' hf'' (hz b le_rfl) hfpb
    simpa only [hell] using hh
  have her : actualGramFirst χ c j (fun n => f (Real.log n/B)) q -
      (LDerivAtOne χ/(B : ℂ))*(-f' t-(B : ℂ)*lemma83PaperBeta D c j*f t) =
      (B : ℂ)⁻¹*(∫ v in t..b, h v*(K v-LDerivAtOne χ*M v)) := by
    have he : (fun v => h v*(K v-LDerivAtOne χ*M v)) =
        (fun v => h v*K v-h v*(LDerivAtOne χ*M v)) := by funext v; ring
    rw [hactual,he,intervalIntegral.integral_sub hiK hiM]
    have hm : (∫ v in t..b, h v*(LDerivAtOne χ*M v)) =
        LDerivAtOne χ*(∫ v in t..b, h v*M v) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro v hv
      ring
    rw [hm,hmain]
    ring
  rw [her]
  have hE₀ : 0≤C*actualGramFirstBoundaryBudget D := by
    apply mul_nonneg hC
    unfold actualGramFirstBoundaryBudget
    positivity
  have hE₁ : 0≤C*lemma82ErrorConstant*lemma23PaperL D^(-6 : ℤ) := by
    have := lemma82_error_constant_pos
    positivity
  apply actualGram_scaled_moving_layer_bound _ htb hδ hE₀ hE₁ hB hie
  · intro v hv hsmallv
    have hb := (actualGram_log_moving_band hB hqR (show 0 < lemma56PaperT D from Real.exp_pos _) v).mpr ⟨hv.1,hsmallv⟩
    have hxP : Real.exp (B*v)/(q : ℝ)<lemma23PaperP D :=
      (hcut v hv).trans_le (proposition71_cutoff_le_P D)
    have he := actualGram_first_small_error χ hD hL hc hsmall j 6 hb.1 hb.2 hxP
    rw [norm_mul]
    exact mul_le_mul (hbound v hv) he (norm_nonneg _) hC
  · intro v hv hlargev
    have hx0 : 0<Real.exp (B*v)/(q : ℝ) := by positivity
    have hx1 : 1≤Real.exp (B*v)/(q : ℝ) := by
      apply (le_div_iff₀ hqR).mpr
      have he : Real.log (q : ℝ)≤B*v := by
        have hh := (div_le_iff₀ hB).mp hv.1
        simpa only [mul_comm] using hh
      simpa only [one_mul,Real.exp_log hqR] using Real.exp_le_exp.mpr he
    have hxT : lemma56PaperT D<Real.exp (B*v)/(q : ℝ) := by
      by_contra! hn
      have hb := (actualGram_log_moving_band hB hqR (show 0 < lemma56PaperT D from Real.exp_pos _) v).mp ⟨hx1,hn⟩
      exact (not_le_of_gt hlargev) hb.2
    have hxP : Real.exp (B*v)/(q : ℝ)<lemma23PaperP D :=
      (hcut v hv).trans_le (proposition71_cutoff_le_P D)
    have he := lemma82_at_parameters χ hD hL hA hc hsmall hx1 hxP
      (hparams.2.2.2 _ hxT) j 6
    rw [norm_mul]
    exact (mul_le_mul (hbound v hv) he (norm_nonneg _) hC).trans_eq (by ring)

/-- The actual first profile sum has the strong L^3/log(P) bound obtained
from the proved global original K1 estimate. The fixed density norm and
interval length stay explicit; no arithmetic main approximation is an input. -/
theorem actualGram_first_profile_norm_uniform (c : ℝ) (hc : 0<c) :
    ∃ N : ℕ, 2≤N ∧ ∀ D : ℕ, N≤D → ∀ χ : RealPrimitiveCharacter D,
    NormalizedAssumptionA χ → ∀ j : Fin 3, ∀ q : ℕ, 0<q →
    ∀ f f' f'' : ℝ → ℂ, ∀ b C : ℝ, 0≤C →
    (∀ x, HasDerivAt f (f' x) x) → (∀ x, HasDerivAt f' (f'' x) x) → Continuous f'' →
    (∀ v, b≤v → f v=0) → f' b=0 →
    let B := Real.log (lemma23PaperP D)
    let t := Real.log q/B
    let ell : ℂ := 3*I*(Real.pi : ℂ)/2
    t≤b →
    (∀ v ∈ Icc t b, ‖actualGramRampDensity ell f f' f'' v‖≤C) →
    (∀ v ∈ Icc t b, Real.exp (B*v)/(q : ℝ)<lemma81Cutoff D) →
    ‖actualGramFirst χ c j (fun n => f (Real.log n/B)) q‖ ≤
      (C*lemma84CompanionConstant*lemma23PaperL D^3)*(b-t)/B := by
  obtain ⟨N,hN,hglobal⟩ := lemma84_companion_global c hc
  refine ⟨N,hN,?_⟩
  intro D hDN χ hA j q hq f f' f'' b C hC hf hf' hf'' hz hfpb
  dsimp only
  let B : ℝ := Real.log (lemma23PaperP D)
  let t : ℝ := Real.log q/B
  let ell : ℂ := 3*I*(Real.pi : ℂ)/2
  let h := actualGramRampDensity ell f f' f''
  let K : ℝ → ℂ := fun v => lemma82ShiftedSum χ c j 6 (Real.exp (B*v)/(q : ℝ))
  intro htb hbound hcut
  have hD : 1<D := by omega
  have hB : 0<B := actualGram_original_log_scale_pos hD
  have hqR : (0 : ℝ)<q := Nat.cast_pos.mpr hq
  have hell : (B : ℂ)*lemma82SmoothingBeta D 6=ell := actualGram_original_mu6_scaled hD
  have hactual : actualGramFirst χ c j (fun n => f (Real.log n/B)) q =
      (B : ℂ)⁻¹*(∫ v in t..b, h v*K v) := by
    have hh := actualGram_log_superposition_from_product D
      (fun n => χ.evalNat n/(n : ℂ)^(1-lemma83PaperBeta D c j))
      (lemma82SmoothingBeta D 6) f f' f'' hB hqR htb hf hf' hf'' hz hfpb
      (fun v hv => (hcut v hv).le)
    simpa only [actualGramFirst,Nat.cast_mul,actualGram_log_kernel_first,hell] using hh
  have htb' : t≤b := htb
  have hint : ‖∫ v in t..b, h v*K v‖ ≤
      (C*lemma84CompanionConstant*lemma23PaperL D^3)*(b-t) := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := t) (b := b) (f := fun v => h v*K v)
      (C := C*lemma84CompanionConstant*lemma23PaperL D^3) (by
        intro v hv
        dsimp only
        have hv' : v ∈ Ioc t b := by simpa only [Set.uIoc_of_le htb'] using hv
        have hvc : v ∈ Icc t b := ⟨hv'.1.le,hv'.2⟩
        have hx1 : 1≤Real.exp (B*v)/(q : ℝ) := by
          apply (le_div_iff₀ hqR).mpr
          have he : Real.log (q : ℝ)≤B*v := by
            have hh := (div_le_iff₀ hB).mp hvc.1
            simpa only [mul_comm] using hh
          simpa only [one_mul,Real.exp_log hqR] using Real.exp_le_exp.mpr he
        have hxP := (hcut v hvc).trans_le (proposition71_cutoff_le_P D)
        have hk := hglobal D hDN χ hA j 6 _ hx1 hxP
        rw [norm_mul]
        exact (mul_le_mul (hbound v hvc) hk (norm_nonneg _) hC).trans_eq (by ring))
    simpa only [abs_of_nonneg (sub_nonneg.mpr htb')] using hh
  rw [hactual,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hB]
  exact (mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr hB.le)).trans_eq (by ring)

end ZhangLS.Spec
