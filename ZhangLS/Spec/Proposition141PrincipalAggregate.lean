import ZhangLS.Spec.Proposition141PrincipalRows
import ZhangLS.Spec.Lemma32QuadraticGaussNorm

/-! All outer arithmetic and prime weights for the actual principal correction. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical ComplexConjugate ArithmeticFunction.zeta

lemma proposition141_principal_support_scales {D D₁ D₂ p k:ℕ}
    (hD:1<D) (hL:2000≤lemma23PaperL D)
    (hmod:2*(D:ℝ)^2*lemma61PaperP4 D≤lemma23PaperP D)
    (hDD:D=D₁*D₂) (hD₁:0<D₁) (hp:p∈lemma56PaperPrimes D)
    (hk:k∈proposition141Indices D) :
    0<D₂ ∧ 1≤(D₂:ℝ)*(p:ℝ)*(k:ℝ) ∧
      (D₂:ℝ)*(p:ℝ)*(k:ℝ)≤lemma23PaperP D^10 ∧ k≤⌊lemma23PaperP D⌋₊ := by
  have hD₂ : 0<D₂ := by nlinarith
  have hk' := (proposition141_mem_indices D k).mp hk
  have hp' := (lemma56_mem_paper_primes D p).mp hp
  have hD1 : (1:ℝ)≤D := by exact_mod_cast (by omega : 1≤D)
  have hD₂D : (D₂:ℝ)≤D := by exact_mod_cast (show D₂≤D by nlinarith)
  have hDsq : (D:ℝ)≤(D:ℝ)^2 := le_self_pow₀ hD1 (by norm_num)
  have hP4 : 0≤lemma61PaperP4 D := (lemma61_P4_pos hD).le
  have hN : (D₂:ℝ)*(k:ℝ)≤lemma23PaperP D := by
    calc
      _≤(D:ℝ)*(2*lemma61PaperP4 D) := mul_le_mul hD₂D hk'.2 (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      _≤2*(D:ℝ)^2*lemma61PaperP4 D := by nlinarith
      _≤_ := hmod
  have hkP : (k:ℝ)≤lemma23PaperP D := by
    have hD₂1:(1:ℝ)≤D₂ := by exact_mod_cast hD₂
    have hh := mul_le_mul_of_nonneg_right hD₂1 (Nat.cast_nonneg k)
    simp only [one_mul] at hh
    exact hh.trans hN
  have hL1:1≤lemma23PaperL D := by linarith
  have hP2:2≤lemma23PaperP D := by
    have hh := Real.add_one_le_exp (lemma23PaperL D^9)
    have h9 := one_le_pow₀ hL1 (n:=9)
    change 2≤Real.exp (lemma23PaperL D^9)
    linarith
  have hpmax:(p:ℝ)≤2*lemma23PaperP D := by
    have hh := lemma56_paper_prime_weight_parameters hL
    linarith [hh.2.2.2.1]
  refine ⟨hD₂,?_,?_,Nat.le_floor hkP⟩
  · have hp1:(1:ℝ)≤p := by exact_mod_cast hp'.1.pos
    have hk1:(1:ℝ)≤k := by exact_mod_cast hk'.1
    have h₂1:(1:ℝ)≤D₂ := by exact_mod_cast hD₂
    calc
      (1:ℝ)=1*1*1 := by norm_num
      _≤_ := by gcongr
  · calc
      _=((D₂:ℝ)*(k:ℝ))*(p:ℝ) := by ring
      _≤lemma23PaperP D*(2*lemma23PaperP D) := by gcongr
      _≤lemma23PaperP D^3 := by nlinarith [sq_nonneg (lemma23PaperP D)]
      _≤_ := pow_le_pow_right₀ (by linarith : 1≤lemma23PaperP D) (by norm_num)

lemma proposition141_principal_harmonic_budget {D:ℕ}
    (hL:1≤lemma23PaperL D)
    (hbox:proposition141Indices D⊆Icc 1 ⌊lemma23PaperP D⌋₊) :
    (∑d∈proposition141Indices D,∑k∈proposition141Indices D,
      ((lemma34Tau 5 d:ℝ)/(d:ℝ))*((lemma34Tau 2 k:ℝ)/(k:ℝ)))≤
        128*lemma23PaperL D^63 := by
  let X := ⌊lemma23PaperP D⌋₊
  have hX := proposition141_floor_P_log_seven hL
  have h5 := proposition71_tau_harmonic_bound 5 X hX.1
  have h2 := proposition71_tau_harmonic_bound 2 X hX.1
  have hd : (∑d∈proposition141Indices D,(lemma34Tau 5 d:ℝ)/(d:ℝ))≤
      (1+Real.log (X:ℝ))^5 :=
    (sum_le_sum_of_subset_of_nonneg hbox (fun _ _ _=>by positivity)).trans h5
  have hk : (∑k∈proposition141Indices D,(lemma34Tau 2 k:ℝ)/(k:ℝ))≤
      (1+Real.log (X:ℝ))^2 :=
    (sum_le_sum_of_subset_of_nonneg hbox (fun _ _ _=>by positivity)).trans h2
  calc
    _=(∑d∈proposition141Indices D,(lemma34Tau 5 d:ℝ)/(d:ℝ))*
      (∑k∈proposition141Indices D,(lemma34Tau 2 k:ℝ)/(k:ℝ)) := by simp_rw [sum_mul,mul_sum]
    _≤(1+Real.log (X:ℝ))^5*(1+Real.log (X:ℝ))^2 := by
      exact mul_le_mul hd hk (sum_nonneg (fun _ _=>by positivity)) (by positivity)
    _=(1+Real.log (X:ℝ))^7 := by ring
    _≤_ := hX.2

/-- Per-prime source principal correction with the actual two divisor factors. -/
theorem proposition141_principal_correction_bound {D D₁ D₂ p:ℕ}
    (hD:1<D) (hL:2000≤lemma23PaperL D)
    (hmod:2*(D:ℝ)^2*lemma61PaperP4 D≤lemma23PaperP D)
    (hDD:D=D₁*D₂) (hD₁:0<D₁) (hp:p∈lemma56PaperPrimes D)
    {Bκ Ba:ℝ} (hBκ:0≤Bκ) (hBa:0≤Ba) {κ a:ℕ→ℂ}
    (hκ:Proposition141KappaBound Bκ κ) (ha:Proposition141AdmissibleSequence D Ba a) :
    ‖proposition141PrincipalCorrection D D₁ D₂ p κ a‖≤
      (128*tauDeltaAbsoluteConstant)*Bκ*Ba*(lemma34Tau 5 D₁:ℝ)*(lemma34Tau 2 D₂:ℝ)*
        (p:ℝ)*lemma23PaperL D^638 := by
  let C := tauDeltaAbsoluteConstant*Bκ*Ba*(lemma34Tau 5 D₁:ℝ)*(lemma34Tau 2 D₂:ℝ)*
    (p:ℝ)*lemma23PaperL D^575
  have hc := tauDelta_absolute_constant_pos.le
  have hC:0≤C := by dsimp [C]; positivity
  have hbox : proposition141Indices D⊆Icc 1 ⌊lemma23PaperP D⌋₊ := by
    intro k hk
    exact mem_Icc.mpr ⟨((proposition141_mem_indices D k).mp hk).1,
      (proposition141_principal_support_scales hD hL hmod hDD hD₁ hp hk).2.2.2⟩
  have hpoint (d:ℕ) (hd:d∈proposition141Indices D) (k:ℕ) (hk:k∈proposition141Indices D) :
      ‖if k.Coprime D₁ then proposition141PrincipalRow D D₁ D₂ p d k κ a else 0‖≤
        C*((lemma34Tau 5 d:ℝ)/(d:ℝ))*((lemma34Tau 2 k:ℝ)/(k:ℝ)) := by
    split_ifs
    · have hs := proposition141_principal_support_scales hD hL hmod hDD hD₁ hp hk
      exact proposition141_principal_row_bound hD hL hBκ hBa hκ ha hD₁ hs.1
        ((proposition141_mem_indices D d).mp hd).1 ((proposition141_mem_indices D k).mp hk).1
        hs.2.1 hs.2.2.1
    · simp only [norm_zero]; positivity
  unfold proposition141PrincipalCorrection
  calc
    _≤∑d∈proposition141Indices D,∑k∈proposition141Indices D,
      ‖if k.Coprime D₁ then proposition141PrincipalRow D D₁ D₂ p d k κ a else 0‖ :=
        (norm_sum_le _ _).trans (sum_le_sum (fun d _=>norm_sum_le _ _))
    _≤∑d∈proposition141Indices D,∑k∈proposition141Indices D,
      C*((lemma34Tau 5 d:ℝ)/(d:ℝ))*((lemma34Tau 2 k:ℝ)/(k:ℝ)) :=
        sum_le_sum (fun d hd=>sum_le_sum (fun k hk=>hpoint d hd k hk))
    _=C*(∑d∈proposition141Indices D,∑k∈proposition141Indices D,
      ((lemma34Tau 5 d:ℝ)/(d:ℝ))*((lemma34Tau 2 k:ℝ)/(k:ℝ))) := by simp only [mul_sum,mul_assoc]
    _≤C*(128*lemma23PaperL D^63) :=
      mul_le_mul_of_nonneg_left (proposition141_principal_harmonic_budget (by linarith) hbox) hC
    _=_ := by dsimp [C]; ring

/-- Exact Dirichlet convolution: no complementary-divisor factor is omitted. -/
theorem proposition141_principal_divisor_convolution (D:ℕ) :
    (∑D₁∈D.divisors,(lemma34Tau 5 D₁:ℝ)*(lemma34Tau 2 (D/D₁):ℝ))=
      (lemma34Tau 7 D:ℝ) := by
  have hn : (∑d∈D.divisors,lemma34Tau 5 d*lemma34Tau 2 (D/d))=lemma34Tau 7 D := by
    change (∑d∈D.divisors,(ArithmeticFunction.zeta^5) d*(ArithmeticFunction.zeta^2) (D/d))=
      (ArithmeticFunction.zeta^7) D
    rw [show (7:ℕ)=5+2 by norm_num,pow_add,ArithmeticFunction.mul_apply]
    exact (Nat.sum_divisorsAntidiagonal (fun a b => (ArithmeticFunction.zeta^5) a*(ArithmeticFunction.zeta^2) b)).symm
  exact_mod_cast hn

end ZhangLS.Spec

namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

/-- Full source principal contribution, with the original complex shift and exterior Gauss factor. -/
noncomputable def proposition141PrincipalTotal {D:ℕ} (χ:RealPrimitiveCharacter D)
    (β:ℂ) (κ a:ℕ→ℂ) : ℂ :=
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  gaussSum χ.chi ZMod.stdAddChar/(D:ℂ) *
    ∑p∈lemma33PrimeWindow D,proposition141ShiftWeight D p β*χ.chi (p:ZMod D)*
      ∑D₁∈D.divisors,proposition141PrincipalCorrection D D₁ (D/D₁) p κ a

lemma proposition141_principal_gauss_normalization {D:ℕ} (χ:RealPrimitiveCharacter D) :
    letI : NeZero D := ⟨χ.modulus_ne_zero⟩
    ‖gaussSum χ.chi ZMod.stdAddChar/(D:ℂ)‖=(Real.sqrt (D:ℝ))⁻¹ := by
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  rw [norm_div,lemma32_actual_quadratic_gauss_norm,Complex.norm_natCast]
  have hD:0<(D:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero χ.modulus_ne_zero
  have hs:Real.sqrt (D:ℝ)≠0 := (Real.sqrt_pos.mpr hD).ne'
  have he := Real.sq_sqrt hD.le
  field_simp
  exact he

/-- Complete finite outer sums, with the exact τ₇ convolution and the Gauss normalization. -/
theorem proposition141_principal_total_bound {D:ℕ} (χ:RealPrimitiveCharacter D)
    (hD:1<D) (hL:2000≤lemma23PaperL D)
    (hmod:2*(D:ℝ)^2*lemma61PaperP4 D≤lemma23PaperP D)
    {β:ℂ} (hβ:‖β‖<5*lemma44PaperAlpha D)
    {Bκ Ba:ℝ} (hBκ:0≤Bκ) (hBa:0≤Ba) {κ a:ℕ→ℂ}
    (hκ:Proposition141KappaBound Bκ κ) (ha:Proposition141AdmissibleSequence D Ba a) :
    ‖proposition141PrincipalTotal χ β κ a‖≤
      (128*Real.exp 60*tauDeltaAbsoluteConstant)*Bκ*Ba*lemma33ActualPrimeMass D*
        lemma23PaperL D^638*(lemma34Tau 7 D:ℝ)/Real.sqrt (D:ℝ) := by
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  let C := (128*tauDeltaAbsoluteConstant)*Bκ*Ba*lemma23PaperL D^638
  have hc := tauDelta_absolute_constant_pos.le
  have hC:0≤C := by dsimp [C]; positivity
  have hpoint (p:ℕ) (hp:p∈lemma56PaperPrimes D) :
      ‖proposition141ShiftWeight D p β*χ.chi (p:ZMod D)*
        ∑D₁∈D.divisors,proposition141PrincipalCorrection D D₁ (D/D₁) p κ a‖≤
      Real.exp 60*C*(p:ℝ)*(lemma34Tau 7 D:ℝ) := by
    have hshift:‖proposition141ShiftWeight D p β‖≤Real.exp 60 := by
      simpa only [proposition141ShiftWeight,Complex.ofReal_mul,Complex.ofReal_natCast]
        using proposition141_prime_t0_shift_norm hL hβ hp
    have hs : ‖∑D₁∈D.divisors,proposition141PrincipalCorrection D D₁ (D/D₁) p κ a‖≤
        C*(p:ℝ)*(lemma34Tau 7 D:ℝ) := by
      calc
        _≤∑D₁∈D.divisors,‖proposition141PrincipalCorrection D D₁ (D/D₁) p κ a‖ := norm_sum_le _ _
        _≤∑D₁∈D.divisors,C*(p:ℝ)*((lemma34Tau 5 D₁:ℝ)*(lemma34Tau 2 (D/D₁):ℝ)) := by
          apply sum_le_sum
          intro D₁ hdiv
          have hd := (Nat.mem_divisors.mp hdiv).1
          have hDD:D=D₁*(D/D₁) := (Nat.mul_div_cancel' hd).symm
          have hD₁:0<D₁ := Nat.pos_of_dvd_of_pos hd (by omega)
          convert proposition141_principal_correction_bound hD hL hmod hDD hD₁ hp hBκ hBa hκ ha using 1 <;> dsimp [C] <;> ring
        _=_ := by rw [←mul_sum,proposition141_principal_divisor_convolution]
    rw [norm_mul,norm_mul]
    calc
      _≤Real.exp 60*1*(C*(p:ℝ)*(lemma34Tau 7 D:ℝ)) := by
        gcongr
        exact χ.chi.norm_le_one _
      _=_ := by ring
  unfold proposition141PrincipalTotal
  rw [norm_mul,proposition141_principal_gauss_normalization,
    proposition141_prime_windows_equal]
  calc
    _≤(Real.sqrt (D:ℝ))⁻¹*(∑p∈lemma56PaperPrimes D,
      Real.exp 60*C*(p:ℝ)*(lemma34Tau 7 D:ℝ)) := by
      apply mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (sum_le_sum hpoint))
      positivity
    _=(Real.sqrt (D:ℝ))⁻¹*(Real.exp 60*C*(lemma34Tau 7 D:ℝ)*lemma56PrimeMass D) := by
      unfold lemma56PrimeMass
      simp only [mul_sum]
      apply sum_congr rfl
      intro p hp
      ring
    _=_ := by rw [proposition141_actual_prime_masses_equal]; dsimp [C]; ring

end ZhangLS.Spec
