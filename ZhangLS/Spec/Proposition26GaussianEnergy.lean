import ZhangLS.Spec.Proposition26H2Energy
import ZhangLS.Spec.Proposition26GaussianPolynomialBridge

/-! Actual Gaussian-to-tent energy transfer. The fixed normalized profiles
enter the proved BV norm before the exact quadratic rescaling. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ZhangLS.Spec
open Complex Finset Filter MeasureTheory Set
open scoped Classical Topology

lemma proposition26_short_energy_continuous {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (Y : (ψ:lemma33CharacterIndex D)→ℂ→ℂ) :
    Continuous (fun v:ℝ => proposition26Energy χ c Y
      (fun ψ s => lemma112ShortPolynomial χ ψ.2 (s+I*(v:ℂ)))) := by
  unfold proposition26Energy
  apply continuous_finsetSum
  intro ψ hψ
  apply continuous_finsetSum
  intro ρ hρ
  have h := (lemma112_short_polynomial_differentiable χ ψ.2).continuous
  fun_prop

lemma proposition26_short_cutoff_le {D : ℕ} (hL : 64≤lemma23PaperL D) :
    lemma112PaperP1 D≤lemma81Cutoff D := by
  have hP : 1≤lemma23PaperP D := Real.one_le_exp_iff.mpr (by
    have : 0≤lemma23PaperL D := by linarith
    positivity)
  exact (Real.rpow_le_rpow_of_exponent_le hP
    (by norm_num : (63/125:ℝ)≤101/200)).trans (proposition26_P505_le_polynomial_cutoff hL)

/-- The genuine smoothed defect has energy O(𝒫 L⁻⁸⁶). The L¹⁵ Gaussian
mass, L⁻¹²¹ transfer factor, and L²⁰ polynomial energy are all retained. -/
theorem proposition26_smoothed_energy_of_bv {c : ℝ} (hc : Lemma52CompatibleConstant c)
    (hNorm : Proposition26BVNormAt c) :
    ∃K:ℝ,0<K ∧ ∃N:ℕ,2≤N ∧ ∀D:ℕ,N≤D →
      ∀χ:RealPrimitiveCharacter D,NormalizedAssumptionA χ →
        ∀Y:(ψ:lemma33CharacterIndex D)→ℂ→ℂ,
          (∀ψ∈lemma81GoodFamily χ,Lemma23ActualBranch ψ.2 (Y ψ)) →
          proposition26Energy χ c Y (fun ψ s => proposition26SmoothedDefect χ ψ.2 s)≤
            K*lemma33ActualPrimeMass D*lemma23PaperL D^(-86:ℤ) := by
  obtain ⟨K,hK,Nm,hNm,hm⟩ := hNorm 1 (by norm_num)
  obtain ⟨C,hC,htransfer⟩ := proposition26_smoothed_energy_transfer
  obtain ⟨Nt,ht⟩ := htransfer c hc
  have hlog : Tendsto (fun D:ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  obtain ⟨Nl,hl⟩ := eventually_atTop.mp (hlog.eventually_ge_atTop 64)
  refine ⟨C*K*(2*Real.sqrt Real.pi),by positivity,max Nm (max Nt Nl),
    hNm.trans (le_max_left _ _),?_⟩
  intro D hD χ hA Y hY
  have hDm := (le_max_left _ _).trans hD
  have hRest := (le_max_right _ _).trans hD
  have hDt := (le_max_left _ _).trans hRest
  have hDl := (le_max_right _ _).trans hRest
  have hL := hl D hDl
  have hLp : 0< lemma23PaperL D := by linarith
  have hcut := proposition26_short_cutoff_le hL
  have hpoint (v:ℝ) (hv:|v|≤lemma23PaperL D^20) :
      proposition26Energy χ c Y (fun ψ s => lemma112ShortPolynomial χ ψ.2 (s+I*(v:ℂ)))≤
        K*lemma33ActualPrimeMass D*lemma23PaperL D^20 := by
    have hh := hm D hDm χ hA v hv (proposition26CutoffIndicator (lemma112PaperP1 D))
      (proposition26_cutoff_indicator_variation _) (proposition26_cutoff_indicator_support hcut) Y hY
    have hind : proposition26CutoffIndicator (lemma112PaperP1 D) =
        (fun n:ℕ => if (n:ℝ)<lemma112PaperP1 D then (1:ℂ) else 0) := by
      funext n
      unfold proposition26CutoffIndicator
      split_ifs <;> norm_num
    rw [hind] at hh
    simpa only [proposition26Energy,proposition26_short_polynomial_eq_twisted χ _ hcut] using hh
  have hg := proposition26_error_gaussian_continuous D
  have he := proposition26_short_energy_continuous χ c Y
  have hH : -(lemma23PaperL D^20)≤lemma23PaperL D^20 := neg_le_self (by positivity)
  have hint : (∫ v in (-(lemma23PaperL D^20))..(lemma23PaperL D^20),
      proposition26Energy χ c Y (fun ψ s => lemma112ShortPolynomial χ ψ.2 (s+I*(v:ℂ)))*
        proposition26ErrorGaussian D v)≤
      (K*lemma33ActualPrimeMass D*lemma23PaperL D^20)*
        (2*Real.sqrt Real.pi*lemma23PaperL D^15) := by
    calc
      _ ≤ ∫ v in (-(lemma23PaperL D^20))..(lemma23PaperL D^20),
          (K*lemma33ActualPrimeMass D*lemma23PaperL D^20)*proposition26ErrorGaussian D v :=
        intervalIntegral.integral_mono_on hH ((he.mul hg).intervalIntegrable _ _)
          ((continuous_const.mul hg).intervalIntegrable _ _) (fun v hv =>
            mul_le_mul_of_nonneg_right (hpoint v (abs_le.mpr hv)) (Real.exp_pos _).le)
      _ = (K*lemma33ActualPrimeMass D*lemma23PaperL D^20)*
          (∫ v in (-(lemma23PaperL D^20))..(lemma23PaperL D^20),proposition26ErrorGaussian D v) :=
        intervalIntegral.integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (proposition26_error_finite_gaussian_mass hLp)
        (by unfold lemma33ActualPrimeMass; positivity)
  apply (ht D hDt χ Y hY).trans
  apply (mul_le_mul_of_nonneg_left hint (by positivity : 0≤C*lemma23PaperL D^(-121:ℤ))).trans_eq
  simp only [zpow_neg,zpow_ofNat]
  field_simp [hLp.ne']
  <;> ring

/-- A pointwise Gaussian tail decays faster than the normalization scale. -/
lemma proposition26_gaussian_tail_decay {L:ℝ} (hL:64≤L) :
    Real.exp (-(L^10))≤L^(-24:ℤ) := by
  have hLp : 0<L := by linarith
  have he : Real.exp (-(L^10))≤Real.exp (-(L^10)/8) :=
    Real.exp_le_exp.mpr (by nlinarith only [pow_nonneg hLp.le 10])
  exact he.trans ((lemma112_exp_remainder_le_polynomial hL).trans
    (zpow_le_zpow_right₀ (by linarith : 1≤L) (by norm_num : (-53:ℤ)≤-24)))

/-- Exact finite-energy normalization, including the true additive tail.
The inputs here are local algebra and two already proved energy bounds. -/
lemma proposition26_normalized_tail_energy {D:ℕ} (χ:RealPrimitiveCharacter D)
    (c:ℝ) (Y:(ψ:lemma33CharacterIndex D)→ℂ→ℂ)
    (hw:∀ψ∈lemma81GoodFamily χ,∀ρ∈lemma81ZeroFinset D ψ.2,0≤proposition26Weight c Y ψ ρ)
    (hL:0<lemma23PaperL D) (F Q T:(ψ:lemma33CharacterIndex D)→ℂ→ℂ)
    (heq:∀ψ∈lemma81GoodFamily χ,∀ρ∈lemma81ZeroFinset D ψ.2,
      F ψ ρ=((lemma23PaperL D^(-24:ℤ):ℝ):ℂ)*Q ψ ρ+T ψ ρ)
    {Kq Ku B:ℝ} (_hKq:0≤Kq) (_hKu:0≤Ku) (_hB:0≤B)
    (hq:proposition26Energy χ c Y Q≤Kq*lemma33ActualPrimeMass D*lemma23PaperL D^20)
    (hu:proposition26Energy χ c Y (fun _ _ =>1)≤Ku*lemma33ActualPrimeMass D*lemma23PaperL D^20)
    (ht:∀ψ∈lemma81GoodFamily χ,∀ρ∈lemma81ZeroFinset D ψ.2,
      ‖T ψ ρ‖≤B*lemma23PaperL D^(-24:ℤ)) :
    proposition26Energy χ c Y F≤
      2*(Kq+B^2*Ku)*lemma33ActualPrimeMass D*lemma23PaperL D^(-28:ℤ) := by
  have hcon := proposition26_energy_congr_on_zeros χ c Y F
    (fun ψ s => ((lemma23PaperL D^(-24:ℤ):ℝ):ℂ)*Q ψ s+T ψ s)
    (fun ψ hψ ρ hρ => congrArg norm (heq ψ hψ ρ hρ))
  rw [hcon]
  have he := proposition26_energy_add χ c Y hw
    (fun ψ s => ((lemma23PaperL D^(-24:ℤ):ℝ):ℂ)*Q ψ s) T
  rw [proposition26_energy_homogeneity,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (zpow_pos hL _)] at he
  have htail := proposition26_energy_pointwise_constant χ c Y hw T
    (B*lemma23PaperL D^(-24:ℤ)) ht
  have htail' := htail.trans (mul_le_mul_of_nonneg_left hu
    (sq_nonneg (B*lemma23PaperL D^(-24:ℤ))))
  apply he.trans
  calc
    _ ≤ 2*((lemma23PaperL D^(-24:ℤ))^2*(Kq*lemma33ActualPrimeMass D*lemma23PaperL D^20)+
        (B*lemma23PaperL D^(-24:ℤ))^2*(Ku*lemma33ActualPrimeMass D*lemma23PaperL D^20)) := by
      gcongr
    _ = _ := by
      simp only [zpow_neg,zpow_ofNat]
      field_simp [hL.ne']

/-- Both literal tent-to-Gaussian errors have the required O(𝒫 L⁻²⁸)
energy, by the fixed bound 16000 for their normalized BV profiles. -/
theorem proposition26_unsmoothing_energy_of_bv {c:ℝ} (hc:Lemma52CompatibleConstant c)
    (hNorm:Proposition26BVNormAt c) :
    ∃K:ℝ,0<K ∧ ∃N:ℕ,2≤N ∧ ∀D:ℕ,N≤D →
      ∀χ:RealPrimitiveCharacter D,NormalizedAssumptionA χ →
        ∀Y:(ψ:lemma33CharacterIndex D)→ℂ→ℂ,
          (∀ψ∈lemma81GoodFamily χ,Lemma23ActualBranch ψ.2 (Y ψ)) →
          proposition26Energy χ c Y (fun ψ s => proposition26J1 χ ψ.2 s-lemma112JtildeOne χ ψ.2 s)≤
            K*lemma33ActualPrimeMass D*lemma23PaperL D^(-28:ℤ) ∧
          proposition26Energy χ c Y (fun ψ s => proposition26J2 χ ψ.2 s-lemma112JtildeTwo χ ψ.2 s)≤
            K*lemma33ActualPrimeMass D*lemma23PaperL D^(-28:ℤ) := by
  obtain ⟨Kq,hKq,Nq,hNq,hq⟩ := hNorm 16000 (by norm_num)
  obtain ⟨Ku,hKu,Nu,hNu,hu⟩ := hNorm 1 (by norm_num)
  obtain ⟨Nw,hw⟩ := proposition26_actual_weight_data hc
  have hlog : Tendsto (fun D:ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  obtain ⟨Nl,hl⟩ := eventually_atTop.mp (hlog.eventually_ge_atTop 64)
  let B := 2*lemma44InverseSquareMass
  have hB : 0≤B := by dsimp [B,lemma44InverseSquareMass]; positivity
  refine ⟨2*(Kq+B^2*Ku),by positivity,max Nq (max Nu (max Nw Nl)),
    hNq.trans (le_max_left _ _),?_⟩
  intro D hD χ hA Y hY
  have hDq := (le_max_left _ _).trans hD
  have hr := (le_max_right _ _).trans hD
  have hDu := (le_max_left _ _).trans hr
  have hr' := (le_max_right _ _).trans hr
  have hDw := (le_max_left _ _).trans hr'
  have hDl := (le_max_right _ _).trans hr'
  have hL := hl D hDl
  have hLp : 0< lemma23PaperL D := by linarith
  have hD1 : 1<D := by have hh := hNq.trans hDq; omega
  have hzero : |(0:ℝ)|≤lemma23PaperL D^20 := by
    simpa only [abs_zero] using pow_nonneg hLp.le 20
  have hdata := hw D hDw χ Y hY
  have hweights := fun ψ hψ ρ hρ => (hdata ψ hψ ρ hρ).2.1
  have hP1 : 1<lemma112PaperP1 D :=
    Real.one_lt_rpow (Real.one_lt_exp_iff.mpr (pow_pos hLp 9)) (by norm_num)
  have hcut : 1<lemma81Cutoff D := hP1.trans_le (proposition26_short_cutoff_le hL)
  have hunit := hu D hDu χ hA 0 hzero (proposition26Indicator 2)
    (proposition26_indicator_variation 2) (proposition26_unit_profile_support hcut) Y hY
  simp only [proposition26_unit_polynomial χ _ _ hcut] at hunit
  have hq1 := hq D hDq χ hA 0 hzero (proposition26ErrorProfileOne D)
    (proposition26_error_profile_one_variation hD1) (proposition26_error_profile_one_support hL) Y hY
  have hq2 := hq D hDq χ hA 0 hzero (proposition26ErrorProfileTwo D)
    (proposition26_error_profile_two_variation hD1) (proposition26_error_profile_two_support hL) Y hY
  constructor
  · apply proposition26_normalized_tail_energy χ c Y hweights hLp
      (fun ψ s => proposition26J1 χ ψ.2 s-lemma112JtildeOne χ ψ.2 s)
      (fun ψ s => lemma81Polynomial D (proposition26TwistedCoefficient χ 0 (proposition26ErrorProfileOne D)) ψ.2 s)
      (fun ψ s => proposition26GaussianTailOne χ ψ.2 s)
      (fun ψ hψ ρ hρ => proposition26_J1_sub_Jtilde_polynomial χ ψ.2 hD1 hL ρ)
      hKq.le hKu.le hB hq1 hunit
    intro ψ hψ ρ hρ
    exact (proposition26_gaussian_tail_one_bound χ ψ.2 hD1 hL
      (by rw [(hdata ψ hψ ρ hρ).1]; norm_num)).trans
      (mul_le_mul_of_nonneg_left (proposition26_gaussian_tail_decay hL) hB)
  · apply proposition26_normalized_tail_energy χ c Y hweights hLp
      (fun ψ s => proposition26J2 χ ψ.2 s-lemma112JtildeTwo χ ψ.2 s)
      (fun ψ s => lemma81Polynomial D (proposition26TwistedCoefficient χ 0 (proposition26ErrorProfileTwo D)) ψ.2 s)
      (fun ψ s => proposition26GaussianTailTwo χ ψ.2 s)
      (fun ψ hψ ρ hρ => proposition26_J2_sub_Jtilde_polynomial χ ψ.2 hD1 hL ρ)
      hKq.le hKu.le hB hq2 hunit
    intro ψ hψ ρ hρ
    exact (proposition26_gaussian_tail_two_bound χ ψ.2 hD1 hL
      (by rw [(hdata ψ hψ ρ hρ).1]; norm_num)).trans
      (mul_le_mul_of_nonneg_left (proposition26_gaussian_tail_decay hL) hB)

end ZhangLS.Spec
