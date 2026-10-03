import ZhangLS.Spec.Proposition26ArithmeticBV
import ZhangLS.Spec.Proposition26ParameterBudget
import ZhangLS.Spec.Lemma83OriginalFiniteXiMajorant
import ZhangLS.Spec.Proposition26ArithmeticEnergy

/-! Actual finite-β arithmetic closure for the coarse Section 11 BV norm.
Both Λ and the μ*ξ envelope are proved inputs, not assumptions. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

noncomputable def proposition26ArithmeticBVConstant : ℝ :=
  2*proposition26LambdaConstant*lemma83OriginalXiMajorantConstant*
    (14*Real.exp 16+2)^2*proposition26TotientSquareMass

lemma proposition26_arithmetic_bv_constant_pos : 0<proposition26ArithmeticBVConstant := by
  unfold proposition26ArithmeticBVConstant
  positivity [proposition26_lambda_constant_pos,lemma83_original_xi_majorant_constant_pos,
    proposition26_totient_square_mass_pos]

/-- Genuine source S_j bound O(V² L¹¹), uniform up to the original L²⁰
frequency range. No unprocessed zero-mean or arithmetic norm remains. -/
theorem proposition26_actual_arithmetic_bv {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (hL : 8≤lemma23PaperL D) {c : ℝ} (hc : 0<c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10)
    (hfreq : lemma23PaperL D^20+4≤(D:ℝ)) {v : ℝ} (hv : |v|≤lemma23PaperL D^20)
    {w : ℕ→ℂ} {V : ℝ} (hw : Proposition26VariationBound w V)
    (hcut : ∀n:ℕ,lemma81Cutoff D≤(n:ℝ) → w n=0) (j : Fin 3) :
    ‖proposition71ArithmeticSum D c j (proposition26TwistedCoefficient χ v w)
      (lemma81ConjugateSequence (proposition26TwistedCoefficient χ v w))‖ ≤
      proposition26ArithmeticBVConstant*V^2*lemma23PaperL D^11 := by
  have hL3 : 3≤lemma23PaperL D := by linarith
  have hLp : 0< lemma23PaperL D := by linarith
  have hLambdaPos := proposition26_lambda_constant_pos
  have hXiPos := lemma83_original_xi_majorant_constant_pos
  have hPhiPos := proposition26_totient_square_mass_pos
  have hP : 1≤lemma23PaperP D := Real.one_le_exp_iff.mpr (by positivity)
  have hN : 1≤⌊lemma23PaperP D⌋₊ := (Nat.one_le_floor_iff _).mpr hP
  have hNP := Nat.floor_le (show 0≤lemma23PaperP D from (Real.exp_pos _).le)
  have hf := proposition26_frequency_point_budget hL3 hc hsmall hfreq hv j
  have hb := proposition26_arithmetic_bv_bound χ hD hL c v j hw hcut hf.1 hf.2
    proposition26LambdaConstant lemma83OriginalXiMajorantConstant
    proposition26_lambda_constant_pos.le lemma83_original_xi_majorant_constant_pos.le
    (fun d hd r hr => proposition26_actual_lambda_uniform hL3 hc hsmall j hd hr)
    (fun d r n => lemma83XiMoebius (lemma83PaperBeta D c) j d r n)
    (fun d hd r hr n hn => by
      rw [lemma83_xi_eq_sum_moebius]
      exact (Nat.sum_divisorsAntidiagonal (fun a _ =>
        lemma83XiMoebius (lemma83PaperBeta D c) j d r a) (n:=n)).symm)
    (fun d hd r hr => by
      have h := lemma83_original_xi_finite_mass hL3 hc hsmall j d r _
        ((proposition71_mem_indices D r).mp hr).1 hN hNP
      simpa only [mul_div_assoc] using h)
  have hlog : Real.log (⌊lemma23PaperP D⌋₊:ℝ)≤lemma23PaperL D^9 := by
    simpa only [lemma23PaperP,Real.log_exp] using
      Real.log_le_log (by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hN) hNP
  have hlog' : 1+Real.log (⌊lemma23PaperP D⌋₊:ℝ)≤2*lemma23PaperL D^9 := by
    have hh := one_le_pow₀ (by linarith : 1≤lemma23PaperL D) (n:=9)
    linarith
  apply hb.trans
  calc
    _ ≤ (proposition26LambdaConstant*lemma83OriginalXiMajorantConstant*
          (((14*Real.exp 16+2)*lemma23PaperL D)*V)^2)*
        (2*lemma23PaperL D^9)*proposition26TotientSquareMass := by
      gcongr
    _ = _ := by unfold proposition26ArithmeticBVConstant; ring

end ZhangLS.Spec

/-! The original prime-mass weighted BV norm, proved through the completed
original mean theorem and finite-β source arithmetic. No desired norm
bound is an assumption. The same c is fixed before all profile bounds. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ZhangLS.Spec
open Complex Finset Filter
open scoped Classical Topology

/-- The actual uniform BV zero-norm property, proved below from source arithmetic. -/
def Proposition26BVNormAt (c : ℝ) : Prop :=
  ∀V:ℝ,0<V → ∃K:ℝ,0<K ∧ ∃N:ℕ,2≤N ∧
    ∀D:ℕ,N≤D → ∀χ:RealPrimitiveCharacter D,NormalizedAssumptionA χ →
      ∀v:ℝ,|v|≤lemma23PaperL D^20 → ∀w:ℕ→ℂ,
        Proposition26VariationBound w V →
        (∀n:ℕ,lemma81Cutoff D≤(n:ℝ) → w n=0) →
        ∀Y:(ψ:lemma33CharacterIndex D)→ℂ→ℂ,
          (∀ψ∈lemma81GoodFamily χ,Lemma23ActualBranch ψ.2 (Y ψ)) →
          proposition26Energy χ c Y
            (fun ψ s => lemma81Polynomial D (proposition26TwistedCoefficient χ v w) ψ.2 s) ≤
            K*lemma33ActualPrimeMass D*lemma23PaperL D^20

/-- A coarse but sufficient genuine weighted norm O(𝒫 L²⁰), uniform in the
actual character, every supported bounded-variation profile, every allowed
frequency, and every genuine square-root branch. -/
theorem proposition26_uniform_bv_energy :
    ∃c:ℝ,0<c ∧ Lemma52CompatibleConstant c ∧ Proposition26BVNormAt c := by
  obtain ⟨c,hc,hcompat,henergy⟩ := proposition26_polynomial_energy_arithmetic
  refine ⟨c,hc,hcompat,?_⟩
  intro V hV
  obtain ⟨C,hC,hmean⟩ := henergy V hV
  obtain ⟨Nm,hNm,hm⟩ := hmean 1 (by norm_num)
  obtain ⟨Ns,hNs,hsmall⟩ := lemma52_exists_shift_threshold hc
  have ht : Tendsto (fun D:ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  obtain ⟨Nl,hNl⟩ := eventually_atTop.mp (ht.eventually_ge_atTop (2*(Nat.factorial 21:ℝ)+100))
  let A := proposition26ArithmeticBVConstant*V^2
  let K := 12*A/Real.pi+3*C*A+1
  have hA0 : 0≤A := by dsimp [A]; positivity [proposition26_arithmetic_bv_constant_pos]
  have hK : 0<K := by dsimp [K]; positivity [Real.pi_pos]
  refine ⟨K,hK,max Nm (max Ns Nl),hNm.trans (le_max_left _ _),?_⟩
  intro D hD χ hχA v hv w hw hcut Y hY
  have hDm := (le_max_left _ _).trans hD
  have hDs := (le_max_left _ _).trans ((le_max_right _ _).trans hD)
  have hDl := (le_max_right _ _).trans ((le_max_right _ _).trans hD)
  have hLbig := hNl D hDl
  have hL : 8≤lemma23PaperL D := by
    have hf : 0≤(Nat.factorial 21:ℝ) := by positivity
    linarith
  have hLp : 0< lemma23PaperL D := by linarith
  have hD2 : 2≤D := hNm.trans hDm
  have hD1 : 1<D := by omega
  have hfreq := proposition26_frequency_size (by omega : 0<D) (by linarith only [hLbig])
  have hs : ∀j:Fin 3, ‖proposition71ArithmeticSum D c j
      (proposition26TwistedCoefficient χ v w)
      (lemma81ConjugateSequence (proposition26TwistedCoefficient χ v w))‖≤A*lemma23PaperL D^11 :=
    fun j => proposition26_actual_arithmetic_bv χ hD1 hL hc (hsmall D hDs) hfreq hv hw hcut j
  have hsum : (∑j:Fin 3, ‖proposition71ArithmeticSum D c j
      (proposition26TwistedCoefficient χ v w)
      (lemma81ConjugateSequence (proposition26TwistedCoefficient χ v w))‖)≤3*A*lemma23PaperL D^11 := by
    exact (sum_le_sum (fun j hj => hs j)).trans_eq (by simp; ring)
  have he := (hm D hDm χ hχA (proposition26TwistedCoefficient χ v w)
    (proposition26_twisted_coefficient_admissible χ v hw hcut) Y hY).2
  have hα := (lemma44_alpha_pos_le_one (by linarith : 3≤lemma23PaperL D)).1
  have hM : 0≤lemma33ActualPrimeMass D := by unfold lemma33ActualPrimeMass; positivity
  apply he.trans
  calc
    _ ≤ lemma33ActualPrimeMass D*((4/lemma44PaperAlpha D+C*lemma23PaperL D^2)*
        (3*A*lemma23PaperL D^11)+1) := by gcongr
    _ = lemma33ActualPrimeMass D*((12*A/Real.pi)*lemma23PaperL D^20+
        (3*C*A)*lemma23PaperL D^13+1) := by
      rw [lemma44PaperAlpha,lemma23PaperP,Real.log_exp]
      field_simp <;> ring
    _ ≤ lemma33ActualPrimeMass D*((12*A/Real.pi)*lemma23PaperL D^20+
        (3*C*A)*lemma23PaperL D^20+lemma23PaperL D^20) := by
      have hL1 : 1≤lemma23PaperL D := by linarith
      have hp := pow_le_pow_right₀ hL1 (by norm_num : 13≤20)
      have h1 := one_le_pow₀ hL1 (n:=20)
      gcongr
    _ = _ := by dsimp [K]; ring

end ZhangLS.Spec
