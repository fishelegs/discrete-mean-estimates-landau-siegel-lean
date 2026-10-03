import ZhangLS.Spec.Proposition141PrincipalAggregate
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! A uniform saving for the literal principal correction, independent of (A).
The τ₇(D) loss is genuine and is paid for with its proved fourth-root bound. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ZhangLS.Spec
open Complex Filter
open scoped Classical

noncomputable def proposition141PrincipalConstant : ℝ :=
  128*Real.exp 60*tauDeltaAbsoluteConstant*divisorPowerQuarterConstant 7

lemma proposition141_principal_constant_pos : 0<proposition141PrincipalConstant := by
  unfold proposition141PrincipalConstant
  have := tauDelta_absolute_constant_pos
  have := divisorPower_quarter_constant_pos 7
  positivity

lemma proposition141_principal_quarter_identity {x:ℝ} (hx:0<x) :
    x^(1/4:ℝ)/Real.sqrt x=(x^(1/4:ℝ))⁻¹ := by
  rw [Real.sqrt_eq_rpow,←Real.rpow_sub hx,show (1/4:ℝ)-1/2=-(1/4:ℝ) by norm_num,
    Real.rpow_neg hx.le]

/-- Every original prime, divisor, d and k weight remains in this saving. -/
theorem proposition141_principal_total_quarter_bound {D:ℕ} (χ:RealPrimitiveCharacter D)
    (hD:1<D) (hL:2000≤lemma23PaperL D)
    (hmod:2*(D:ℝ)^2*lemma61PaperP4 D≤lemma23PaperP D)
    {β:ℂ} (hβ:‖β‖<5*lemma44PaperAlpha D)
    {Bκ Ba:ℝ} (hBκ:0≤Bκ) (hBa:0≤Ba) {κ a:ℕ→ℂ}
    (hκ:Proposition141KappaBound Bκ κ) (ha:Proposition141AdmissibleSequence D Ba a) :
    ‖proposition141PrincipalTotal χ β κ a‖≤
      proposition141PrincipalConstant*Bκ*Ba*lemma33ActualPrimeMass D*
        lemma23PaperL D^638/(D:ℝ)^(1/4:ℝ) := by
  have hb := proposition141_principal_total_bound χ hD hL hmod hβ hBκ hBa hκ ha
  have hDpos:0<(D:ℝ) := by exact_mod_cast (by omega : 0<D)
  have ht := divisorPower_tau_quarter (by norm_num : 1≤7) D
  have hM:0≤lemma33ActualPrimeMass D := by
    rw [proposition141_actual_prime_masses_equal]
    exact lemma56_prime_mass_nonneg D
  have hc := tauDelta_absolute_constant_pos.le
  apply hb.trans
  calc
    _≤(128*Real.exp 60*tauDeltaAbsoluteConstant)*Bκ*Ba*lemma33ActualPrimeMass D*
        lemma23PaperL D^638*(divisorPowerQuarterConstant 7*(D:ℝ)^(1/4:ℝ))/Real.sqrt (D:ℝ) := by gcongr
    _=((128*Real.exp 60*tauDeltaAbsoluteConstant)*Bκ*Ba*lemma33ActualPrimeMass D*
        lemma23PaperL D^638*divisorPowerQuarterConstant 7)*
          ((D:ℝ)^(1/4:ℝ)/Real.sqrt (D:ℝ)) := by ring
    _=_ := by rw [proposition141_principal_quarter_identity hDpos]; unfold proposition141PrincipalConstant; ring

/-- The asymptotic threshold is chosen before characters, both sequences and β.
No Proposition14.1 conclusion, character averaging estimate or not-(A) shortcut is used. -/
theorem proposition141_uniform_principal_saving (Bκ Ba:ℝ) (hBκ:0<Bκ) (hBa:0<Ba)
    (ε:ℝ) (hε:0<ε) :
    ∃D₀:ℕ,2≤D₀ ∧ ∀{D:ℕ} (χ:RealPrimitiveCharacter D),D₀≤D →
      ∀β:ℂ,‖β‖<5*lemma44PaperAlpha D → ∀κ a:ℕ→ℂ,
      Proposition141KappaBound Bκ κ → Proposition141AdmissibleSequence D Ba a →
        ‖proposition141PrincipalTotal χ β κ a‖≤ε*lemma33ActualPrimeMass D := by
  let K := proposition141PrincipalConstant*Bκ*Ba
  have hK:0<K := by dsimp [K]; exact mul_pos (mul_pos proposition141_principal_constant_pos hBκ) hBa
  have heps:0<ε/K := div_pos hε hK
  have hlittle := (isLittleO_log_rpow_rpow_atTop (638:ℝ) (by norm_num : (0:ℝ)<1/4)).comp_tendsto
    (tendsto_natCast_atTop_atTop (R:=ℝ))
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hlittle.bound heps)
  obtain ⟨Ns,hNs2,hNs⟩ := proposition141_uniform_support_modulus_bound
  let D₀ := max Ns (max N ⌈Real.exp 2000⌉₊)
  refine ⟨D₀,hNs2.trans (le_max_left _ _),?_⟩
  intro D χ hlarge β hβ κ a hκ ha
  have hNsD:Ns≤D := by dsimp [D₀] at hlarge; omega
  have hND:N≤D := by dsimp [D₀] at hlarge; omega
  have hNe:⌈Real.exp 2000⌉₊≤D := by dsimp [D₀] at hlarge; omega
  have hD:1<D := by have := hNs2.trans hNsD; omega
  have hDpos:0<(D:ℝ) := by exact_mod_cast (by omega : 0<D)
  have hL:2000≤lemma23PaperL D := by
    have hh:Real.exp 2000≤(D:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hNe)
    simpa only [lemma23PaperL,Real.log_exp] using Real.log_le_log (Real.exp_pos _) hh
  have hpow:lemma23PaperL D^638≤(ε/K)*(D:ℝ)^(1/4:ℝ) := by
    have hh := hN D hND
    apply (le_abs_self _).trans
    simpa only [Function.comp_apply,Real.rpow_natCast,Real.rpow_ofNat,Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (Real.log_natCast_nonneg D) 638),
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg D) (1/4:ℝ)),lemma23PaperL] using hh
  have hM:0≤lemma33ActualPrimeMass D := by
    rw [proposition141_actual_prime_masses_equal]
    exact lemma56_prime_mass_nonneg D
  have hq:(D:ℝ)^(1/4:ℝ)≠0 := (Real.rpow_pos_of_pos hDpos _).ne'
  apply (proposition141_principal_total_quarter_bound χ hD hL (hNs D hNsD) hβ hBκ.le hBa.le hκ ha).trans
  change K*lemma33ActualPrimeMass D*lemma23PaperL D^638/(D:ℝ)^(1/4:ℝ)≤_
  calc
    _≤K*lemma33ActualPrimeMass D*((ε/K)*(D:ℝ)^(1/4:ℝ))/(D:ℝ)^(1/4:ℝ) := by gcongr
    _=_ := by field_simp

end ZhangLS.Spec
