import ZhangLS.Spec.Proposition141PrimeCorrectionBounds

/-! All original prime shifts and exterior Gauss weights for both front corrections. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace ZhangLS.Spec
open Complex Finset Filter
open scoped Classical

lemma proposition141_indices_card_bound {D:ℕ} (hD:1<D) :
    ((proposition141Indices D).card:ℝ)≤2*lemma61PaperP4 D := by
  have hsub:proposition141Indices D⊆Icc 1 ⌊2*lemma61PaperP4 D⌋₊ := by
    intro n hn
    have hs := (proposition141_mem_indices D n).mp hn
    exact mem_Icc.mpr ⟨hs.1,Nat.le_floor hs.2⟩
  have hc := card_le_card hsub
  simp only [Nat.card_Icc,add_tsub_cancel_right] at hc
  exact (by exact_mod_cast hc : ((proposition141Indices D).card:ℝ)≤⌊2*lemma61PaperP4 D⌋₊).trans
    (Nat.floor_le (by have := (lemma61_P4_pos hD).le; positivity))

lemma proposition141_prime_correction_card_budget {D p:ℕ} (hD:1<D)
    (hmod:2*(D:ℝ)^2*lemma61PaperP4 D≤lemma23PaperP D)
    (hp:p∈lemma56PaperPrimes D) :
    (D:ℝ)*(proposition141Indices D).card≤(p:ℝ)/(D:ℝ) := by
  have hDR:0<(D:ℝ) := by exact_mod_cast (by omega : 0<D)
  have hc := mul_le_mul_of_nonneg_left (proposition141_indices_card_bound hD) (sq_nonneg (D:ℝ))
  have hpP := ((lemma56_mem_paper_primes D p).mp hp).2.1
  apply (le_div_iff₀ hDR).mpr
  nlinarith

/-- Both correction signs remain in the literal combined source expression. -/
theorem proposition141_prime_corrections_combined_bound {D p:ℕ}
    (hD:1<D) (hL:2000≤lemma23PaperL D)
    (hmod:2*(D:ℝ)^2*lemma61PaperP4 D≤lemma23PaperP D)
    (hp:p∈lemma56PaperPrimes D) {Bκ Ba:ℝ} (hBκ:0≤Bκ) (hBa:0≤Ba)
    {κ a:ℕ→ℂ} (hκ:Proposition141KappaBound Bκ κ) (ha:Proposition141AdmissibleSequence D Ba a) :
    ‖(p:ℂ)⁻¹*proposition141PrimeSmallCorrection D p κ a-
      proposition141PrimeDivisibleCorrection D p κ a‖≤
        7*tauDeltaAbsoluteConstant*Bκ*Ba*(p:ℝ)*lemma23PaperL D^575/(D:ℝ) := by
  have hs := proposition141_prime_small_correction_bound hD hL hmod hp hBκ hBa hκ ha
  have hv := proposition141_prime_divisible_correction_bound hD hL hmod hp hBκ hBa hκ ha
  have hpp := ((lemma56_mem_paper_primes D p).mp hp).1
  have hpR:0<(p:ℝ) := by exact_mod_cast hpp.pos
  have hc := tauDelta_absolute_constant_pos.le
  have hsmall:‖(p:ℂ)⁻¹*proposition141PrimeSmallCorrection D p κ a‖≤
      2*tauDeltaAbsoluteConstant*Bκ*Ba*(D:ℝ)*(proposition141Indices D).card*lemma23PaperL D^575 := by
    rw [norm_mul,norm_inv,Complex.norm_natCast]
    apply (mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hpR.le)).trans_eq
    field_simp
  have hcard := proposition141_prime_correction_card_budget hD hmod hp
  apply (norm_sub_le _ _).trans
  apply (add_le_add hsmall hv).trans
  calc
    _=(7*tauDeltaAbsoluteConstant*Bκ*Ba*lemma23PaperL D^575)*
      ((D:ℝ)*(proposition141Indices D).card) := by ring
    _≤(7*tauDeltaAbsoluteConstant*Bκ*Ba*lemma23PaperL D^575)*((p:ℝ)/(D:ℝ)) := by gcongr
    _=_ := by ring

noncomputable def proposition141PrimeFrontCorrectionTotal {D:ℕ} (χ:RealPrimitiveCharacter D)
    (β:ℂ) (κ a:ℕ→ℂ) : ℂ :=
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  gaussSum χ.chi ZMod.stdAddChar/(D:ℂ)*
    ∑p∈lemma33PrimeWindow D,proposition141ShiftWeight D p β*χ.chi (p:ZMod D)*
      ((p:ℂ)⁻¹*proposition141PrimeSmallCorrection D p κ a-
        proposition141PrimeDivisibleCorrection D p κ a)

/-- Includes the genuine full complex shift and exterior τ(χ)/D factor. -/
theorem proposition141_prime_front_total_bound {D:ℕ} (χ:RealPrimitiveCharacter D)
    (hD:1<D) (hL:2000≤lemma23PaperL D)
    (hmod:2*(D:ℝ)^2*lemma61PaperP4 D≤lemma23PaperP D)
    {β:ℂ} (hβ:‖β‖<5*lemma44PaperAlpha D)
    {Bκ Ba:ℝ} (hBκ:0≤Bκ) (hBa:0≤Ba) {κ a:ℕ→ℂ}
    (hκ:Proposition141KappaBound Bκ κ) (ha:Proposition141AdmissibleSequence D Ba a) :
    ‖proposition141PrimeFrontCorrectionTotal χ β κ a‖≤
      (7*Real.exp 60*tauDeltaAbsoluteConstant)*Bκ*Ba*lemma33ActualPrimeMass D*
        lemma23PaperL D^575/(D:ℝ) := by
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  have hc := tauDelta_absolute_constant_pos.le
  have hgauss:‖gaussSum χ.chi ZMod.stdAddChar/(D:ℂ)‖≤1 := by
    rw [proposition141_principal_gauss_normalization]
    have hd1:(1:ℝ)≤D := by exact_mod_cast (by omega : 1≤D)
    have hs:1≤Real.sqrt (D:ℝ) := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hd1
    exact inv_le_one_of_one_le₀ hs
  have hpoint (p:ℕ) (hp:p∈lemma56PaperPrimes D) :
      ‖proposition141ShiftWeight D p β*χ.chi (p:ZMod D)*
        ((p:ℂ)⁻¹*proposition141PrimeSmallCorrection D p κ a-
          proposition141PrimeDivisibleCorrection D p κ a)‖≤
      (7*Real.exp 60*tauDeltaAbsoluteConstant)*Bκ*Ba*(p:ℝ)*lemma23PaperL D^575/(D:ℝ) := by
    have hb := proposition141_prime_corrections_combined_bound hD hL hmod hp hBκ hBa hκ ha
    have hshift:‖proposition141ShiftWeight D p β‖≤Real.exp 60 := by
      simpa only [proposition141ShiftWeight,Complex.ofReal_mul,Complex.ofReal_natCast]
        using proposition141_prime_t0_shift_norm hL hβ hp
    rw [norm_mul,norm_mul]
    calc
      _≤Real.exp 60*1*(7*tauDeltaAbsoluteConstant*Bκ*Ba*(p:ℝ)*lemma23PaperL D^575/(D:ℝ)) := by
        gcongr
        exact χ.chi.norm_le_one _
      _=_ := by ring
  unfold proposition141PrimeFrontCorrectionTotal
  rw [norm_mul,proposition141_prime_windows_equal]
  calc
    _≤1*‖∑p∈lemma56PaperPrimes D,proposition141ShiftWeight D p β*χ.chi (p:ZMod D)*
        ((p:ℂ)⁻¹*proposition141PrimeSmallCorrection D p κ a-
          proposition141PrimeDivisibleCorrection D p κ a)‖ :=
      mul_le_mul_of_nonneg_right hgauss (norm_nonneg _)
    _≤∑p∈lemma56PaperPrimes D,
        (7*Real.exp 60*tauDeltaAbsoluteConstant)*Bκ*Ba*(p:ℝ)*lemma23PaperL D^575/(D:ℝ) := by
      simpa only [one_mul] using (norm_sum_le _ _).trans (sum_le_sum hpoint)
    _=_ := by
      rw [proposition141_actual_prime_masses_equal]
      unfold lemma56PrimeMass
      simp only [sum_mul,mul_sum,sum_div]

/-- Uniform negligible error for the literal +1/p and p-divisibility corrections. -/
theorem proposition141_uniform_prime_front_saving (Bκ Ba:ℝ) (hBκ:0<Bκ) (hBa:0<Ba)
    (ε:ℝ) (hε:0<ε) :
    ∃D₀:ℕ,2≤D₀ ∧ ∀{D:ℕ} (χ:RealPrimitiveCharacter D),D₀≤D →
      ∀β:ℂ,‖β‖<5*lemma44PaperAlpha D → ∀κ a:ℕ→ℂ,
      Proposition141KappaBound Bκ κ → Proposition141AdmissibleSequence D Ba a →
        ‖proposition141PrimeFrontCorrectionTotal χ β κ a‖≤ε*lemma33ActualPrimeMass D := by
  let K := (7*Real.exp 60*tauDeltaAbsoluteConstant)*Bκ*Ba
  have hc := tauDelta_absolute_constant_pos
  have hK:0<K := by dsimp [K]; positivity
  have hlittle := (Real.isLittleO_pow_log_id_atTop (n:=575)).comp_tendsto
    (tendsto_natCast_atTop_atTop (R:=ℝ))
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hlittle.bound (div_pos hε hK))
  obtain ⟨Ns,hNs2,hNs⟩ := proposition141_uniform_support_modulus_bound
  let D₀ := max Ns (max N ⌈Real.exp 2000⌉₊)
  refine ⟨D₀,hNs2.trans (le_max_left _ _),?_⟩
  intro D χ hlarge β hβ κ a hκ ha
  have hNsD:Ns≤D := by dsimp [D₀] at hlarge; omega
  have hND:N≤D := by dsimp [D₀] at hlarge; omega
  have hNe:⌈Real.exp 2000⌉₊≤D := by dsimp [D₀] at hlarge; omega
  have hD:1<D := by have := hNs2.trans hNsD; omega
  have hDR:0<(D:ℝ) := by exact_mod_cast (by omega : 0<D)
  have hL:2000≤lemma23PaperL D := by
    have hh:Real.exp 2000≤(D:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hNe)
    simpa only [lemma23PaperL,Real.log_exp] using Real.log_le_log (Real.exp_pos _) hh
  have hpow:lemma23PaperL D^575≤(ε/K)*(D:ℝ) := by
    have hh := hN D hND
    simpa only [Function.comp_apply,id_eq,Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (Real.log_natCast_nonneg D) 575),
      abs_of_nonneg (show (0:ℝ)≤D by positivity),lemma23PaperL] using hh
  have hM:0≤lemma33ActualPrimeMass D := by
    rw [proposition141_actual_prime_masses_equal]
    exact lemma56_prime_mass_nonneg D
  apply (proposition141_prime_front_total_bound χ hD hL (hNs D hNsD) hβ hBκ.le hBa.le hκ ha).trans
  change K*lemma33ActualPrimeMass D*lemma23PaperL D^575/(D:ℝ)≤_
  calc
    _≤K*lemma33ActualPrimeMass D*((ε/K)*(D:ℝ))/(D:ℝ) := by gcongr
    _=_ := by field_simp

end ZhangLS.Spec
