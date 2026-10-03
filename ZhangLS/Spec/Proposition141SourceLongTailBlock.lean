import ZhangLS.Spec.Proposition141LongTailSigma
import ZhangLS.Spec.Proposition141SourceSmallAggregate
import ZhangLS.Spec.Proposition141OffLocalBlock

/-! # The actual small-conductor omitted-long-index block -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

noncomputable def proposition141SourceLongTailBlock {D:ℕ}
    (χ:RealPrimitiveCharacter D) (β:ℂ) (κ a:ℕ→ℂ) (D₁ D₂ d h:ℕ) : ℝ :=
  ∑r∈proposition141SourceSmallModuli D D₁ D₂ d h a,
    ‖a (d*(r*h/D₂))‖*(D₂:ℝ)*((d:ℝ)*(h:ℝ)*((r*h).totient:ℝ)*Real.sqrt (r:ℝ))⁻¹*
      ∑θ∈proposition141SmallPrimitiveFamily χ h r,
        ‖proposition141SigmaLongTail χ θ β κ D₁ d h‖

/-- A single original source block has a fully paid P^11 tail bound.
Neither the primitive-character count nor any D₁/D₂ factor is omitted. -/
theorem proposition141_source_long_tail_block_bound {D D₁ D₂ d h:ℕ}
    (χ:RealPrimitiveCharacter D) (β:ℂ) (κ a:ℕ→ℂ) {Bκ Ba:ℝ}
    (hD:1<D) (hL:2000≤lemma23PaperL D) (hβ:‖β‖<5*lemma44PaperAlpha D)
    (hBκ:0≤Bκ) (hBa:0≤Ba) (hκ:Proposition141KappaBound Bκ κ)
    (ha:Proposition141AdmissibleSequence D Ba a)
    (hmod:2*(D:ℝ)^2*lemma61PaperP4 D≤lemma23PaperP D)
    (hDD:D=D₁*D₂) (hD₁:0<D₁) (hd:0<d) (hh:0<h)
    (hdP:(d:ℝ)≤lemma23PaperP D) :
    proposition141SourceLongTailBlock χ β κ a D₁ D₂ d h ≤
      (2^40*proposition141OffLocalTailConstant)*Bκ*Ba*lemma56PrimeMass D*
        lemma23PaperP D^11*Real.exp (-lemma23PaperL D^10/2) := by
  have hD₂:0<D₂ := by
    by_contra hn
    have hz:D₂=0 := by omega
    rw [hz,mul_zero] at hDD
    omega
  have hDP := proposition141_modulus_le_P (by omega : 0<D) (by linarith : 1≤lemma23PaperL D)
  have hD₁P : (D₁:ℝ)≤lemma23PaperP D := by
    have hn:D₁≤D := by rw [hDD]; exact Nat.le_mul_of_pos_right _ hD₂
    exact (by exact_mod_cast hn : (D₁:ℝ)≤D).trans hDP
  have hD₂P : (D₂:ℝ)≤lemma23PaperP D := by
    have hn:D₂≤D := by rw [hDD]; exact Nat.le_mul_of_pos_left _ hD₁
    exact (by exact_mod_cast hn : (D₂:ℝ)≤D).trans hDP
  let Q := proposition141SourceSmallModuli D D₁ D₂ d h a
  let K := proposition141OffLocalTailConstant*Bκ*(lemma34Tau 5 D₁:ℝ)*(lemma34Tau 5 d:ℝ)*
    lemma56PrimeMass D*lemma23PaperP D^6*Real.exp (-lemma23PaperL D^10/2)
  have hM := lemma56_prime_mass_nonneg D
  have hC := proposition141_offlocal_tail_constant_pos.le
  have hP : 0≤lemma23PaperP D := (Real.exp_pos _).le
  have hK : 0≤K := by dsimp [K]; positivity
  have hsupp (r:ℕ) (hr:r∈Q) : r≤⌊lemma23PaperP D⌋₊ ∧ h*r≤⌊lemma23PaperP D⌋₊ := by
    have hp := proposition141_source_small_moduli_mem hr
    have hdiv:D₂∣h*r := by simpa only [Nat.mul_comm] using hp.2.2.1
    have han:a (d*(h*r/D₂))≠0 := by simpa only [Nat.mul_comm] using hp.2.2.2.2
    exact (proposition141_source_outer_support ha hD hmod hDD hD₁ hd hh
      (by omega : 0<r) hdiv han).2.2
  have hcard : (Q.card:ℝ)≤lemma23PaperP D := by
    have hsub:Q⊆Icc 1 ⌊lemma23PaperP D⌋₊ := by
      intro r hr
      have hp := proposition141_source_small_moduli_mem hr
      exact mem_Icc.mpr ⟨by omega,(hsupp r hr).1⟩
    have hb : Q.card≤⌊lemma23PaperP D⌋₊ := by simpa using card_le_card hsub
    exact (by exact_mod_cast hb : (Q.card:ℝ)≤⌊lemma23PaperP D⌋₊).trans (Nat.floor_le hP)
  have hrow (r:ℕ) (hr:r∈Q) :
      ‖a (d*(r*h/D₂))‖*(D₂:ℝ)*((d:ℝ)*(h:ℝ)*((r*h).totient:ℝ)*Real.sqrt (r:ℝ))⁻¹*
        (∑θ∈proposition141SmallPrimitiveFamily χ h r,
          ‖proposition141SigmaLongTail χ θ β κ D₁ d h‖) ≤ Ba*(D₂:ℝ)*lemma23PaperP D*K := by
    have hp := proposition141_source_small_moduli_mem hr
    have hrp:0<r := by omega
    letI : NeZero r := ⟨by omega⟩
    have hrP:(r:ℝ)≤lemma23PaperP D :=
      (by exact_mod_cast (hsupp r hr).1 : (r:ℝ)≤⌊lemma23PaperP D⌋₊).trans (Nat.floor_le hP)
    have hhrP:((h*r:ℕ):ℝ)≤lemma23PaperP D :=
      (by exact_mod_cast (hsupp r hr).2 : ((h*r:ℕ):ℝ)≤⌊lemma23PaperP D⌋₊).trans (Nat.floor_le hP)
    have hf : (∑θ∈proposition141SmallPrimitiveFamily χ h r,
        ‖proposition141SigmaLongTail χ θ β κ D₁ d h‖)≤lemma23PaperP D*K := by
      apply (sum_le_sum (fun θ _=>(proposition141_actual_long_tail_bound χ θ hD hL hβ hBκ hκ hD₁ hd hh hp.1 hhrP).2)).trans
      simp only [sum_const,nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ hK
      have hcount := proposition141_primitive_subfamily_card (proposition141SmallPrimitiveFamily χ h r)
        (fun θ hθ=>(mem_filter.mp hθ).2.1)
      exact (by exact_mod_cast hcount.trans (Nat.totient_le r) :
        ((proposition141SmallPrimitiveFamily χ h r).card:ℝ)≤r).trans hrP
    have hquot:0<r*h/D₂ := Nat.div_pos (Nat.le_of_dvd (Nat.mul_pos hrp hh) hp.2.2.1) hD₂
    have ha' := ha.1 _ (Nat.mul_pos hd hquot)
    have hden : 1≤(d:ℝ)*(h:ℝ)*((r*h).totient:ℝ)*Real.sqrt (r:ℝ) := by
      have hd1 : (1:ℝ)≤d := by exact_mod_cast hd
      have hh1 : (1:ℝ)≤h := by exact_mod_cast hh
      have hφ1 : (1:ℝ)≤(r*h).totient := by exact_mod_cast Nat.totient_pos.mpr (Nat.mul_pos hrp hh)
      have hr1 : (1:ℝ)≤r := by exact_mod_cast hrp
      have hs1 : 1≤Real.sqrt (r:ℝ) := Real.one_le_sqrt.mpr hr1
      calc
        (1:ℝ)=1*1*1*1 := by ring
        _≤_ := by gcongr
    have hinv : ((d:ℝ)*(h:ℝ)*((r*h).totient:ℝ)*Real.sqrt (r:ℝ))⁻¹≤1 := by
      rw [←one_div]
      exact (div_le_one (lt_of_lt_of_le zero_lt_one hden)).mpr hden
    calc
      _≤Ba*(D₂:ℝ)*1*(lemma23PaperP D*K) := by gcongr
      _=_ := by ring
  have hb : proposition141SourceLongTailBlock χ β κ a D₁ D₂ d h≤Ba*(D₂:ℝ)*lemma23PaperP D^2*K := by
    unfold proposition141SourceLongTailBlock
    apply (sum_le_sum hrow).trans
    simp only [sum_const,nsmul_eq_mul]
    have hh' := mul_le_mul_of_nonneg_right hcard (show 0≤Ba*(D₂:ℝ)*lemma23PaperP D*K by positivity)
    convert hh' using 1; ring
  apply hb.trans
  have ht1 := proposition141_tau_five_le_prime_scale hD₁P
  have htd := proposition141_tau_five_le_prime_scale hdP
  dsimp [K]
  calc
    _≤Ba*lemma23PaperP D*lemma23PaperP D^2*
        (proposition141OffLocalTailConstant*Bκ*(2^20*lemma23PaperP D)*(2^20*lemma23PaperP D)*
          lemma56PrimeMass D*lemma23PaperP D^6*Real.exp (-lemma23PaperL D^10/2)) := by gcongr
    _=_ := by ring

end ZhangLS.Spec
