import ZhangLS.Spec.Proposition141LargeConductorBlock

/-! # The actual short coefficient and source congruence in a large block

The modulus family keeps D₂ | hr, (hr/D₂,D₁)=1 and the literal nonzero
coefficient a*(d hr/D₂). Nonemptiness supplies the original support cutoff;
empty blocks are treated exactly, rather than assuming that cutoff globally.
-/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

noncomputable def proposition141SourceLargeModuli (D₁ D₂ d h:ℕ) (R:ℝ) (a:ℕ→ℂ) : Finset ℕ :=
  (primitiveDyadicModuli R).filter
    (fun r=>D₂∣h*r ∧ (h*r/D₂).Coprime D₁ ∧ a (d*(h*r/D₂))≠0)

noncomputable def proposition141SourceLargeBlock {D:ℕ}
    (χ:RealPrimitiveCharacter D) (β:ℂ) (κ a:ℕ→ℂ) (D₁ D₂ d h:ℕ) (R:ℝ) : ℝ :=
  ∑r∈proposition141SourceLargeModuli D₁ D₂ d h R a,
    ‖a (d*(h*r/D₂))‖*(D₂:ℝ)*((d:ℝ)*(h:ℝ)*((h*r).totient:ℝ)*Real.sqrt (r:ℝ))⁻¹*
      ∑θ∈(univ:Finset (DirichletCharacter ℂ r)).filter (fun θ=>θ.IsPrimitive),
        ‖proposition141FiniteSmallCharacterSum χ θ β κ D₁ d h r (proposition141LocalizedIndices D R h)‖

lemma proposition141_source_large_moduli_mem {D₁ D₂ d h r:ℕ} {R:ℝ} {a:ℕ→ℂ}
    (hr:r∈proposition141SourceLargeModuli D₁ D₂ d h R a) :
    1<r ∧ R≤(r:ℝ) ∧ (r:ℝ)<2*R ∧ D₂∣h*r ∧ (h*r/D₂).Coprime D₁ ∧ a (d*(h*r/D₂))≠0 := by
  have hp := mem_filter.mp hr
  have hdy := mem_primitiveDyadicModuli.mp hp.1
  exact ⟨hdy.1,hdy.2.1,hdy.2.2,hp.2⟩

/-- The actual a* factor is bounded only after its quotient index is proved
positive. It remains explicitly in the definition of the source block. -/
theorem proposition141_source_large_block_le {D D₁ D₂ d h:ℕ}
    (χ:RealPrimitiveCharacter D) (β:ℂ) (κ:ℕ→ℂ) {Ba:ℝ} {a:ℕ→ℂ}
    (ha:Proposition141AdmissibleSequence D Ba a) (hD₂:0<D₂) (hd:0<d) (hh:0<h) (R:ℝ) :
    proposition141SourceLargeBlock χ β κ a D₁ D₂ d h R ≤
      Ba*proposition141LocalizedConductorBlock χ β κ D₁ D₂ d h R
        (proposition141SourceLargeModuli D₁ D₂ d h R a) := by
  unfold proposition141SourceLargeBlock proposition141LocalizedConductorBlock
  simp only [mul_sum]
  apply sum_le_sum
  intro r hr
  have hp := proposition141_source_large_moduli_mem hr
  have hquot : 0<h*r/D₂ := Nat.div_pos (Nat.le_of_dvd (Nat.mul_pos hh (by omega : 0<r)) hp.2.2.2.1) hD₂
  have ha' := ha.1 (d*(h*r/D₂)) (Nat.mul_pos hd hquot)
  have hw : 0≤(D₂:ℝ)*((d:ℝ)*(h:ℝ)*((h*r).totient:ℝ)*Real.sqrt (r:ℝ))⁻¹*
      ∑θ∈(univ:Finset (DirichletCharacter ℂ r)).filter (fun θ=>θ.IsPrimitive),
        ‖proposition141FiniteSmallCharacterSum χ θ β κ D₁ d h r (proposition141LocalizedIndices D R h)‖ := by positivity
  have hb := mul_le_mul_of_nonneg_right ha' hw
  simpa only [mul_assoc,mul_sum] using hb

/-- Nonempty actual support, rather than an assumed size restriction,
forces the scale condition used by the proved large-sieve mean. -/
theorem proposition141_source_large_block_cutoff {D D₁ D₂ d h:ℕ}
    {Ba:ℝ} {a:ℕ→ℂ} (ha:Proposition141AdmissibleSequence D Ba a)
    (hDD:D=D₁*D₂) (hD₁:0<D₁) (hD₂:0<D₂) (hd:0<d) (hh:0<h)
    {R:ℝ} (hR:0≤R) (hQ:(proposition141SourceLargeModuli D₁ D₂ d h R a).Nonempty) :
    ((d*h:ℕ):ℝ)*R≤2*(D:ℝ)*lemma61PaperP4 D := by
  obtain ⟨r,hr⟩ := hQ
  have hp := proposition141_source_large_moduli_mem hr
  have hk : 0<h*r/D₂ := Nat.div_pos (Nat.le_of_dvd (Nat.mul_pos hh (by omega : 0<r)) hp.2.2.2.1) hD₂
  have hN : h*r=D₂*(h*r/D₂) := (Nat.mul_div_cancel' hp.2.2.2.1).symm
  exact proposition141_supported_conductor_scale ha hDD hD₁ hd hk hp.2.2.2.2.2 hN hR hp.2.1

/-- Uniform actual source-block bound, with no extra support-cutoff premise.
The large-conductor boundary is exactly D³ and the full complex β is allowed. -/
theorem proposition141_uniform_source_large_block :
    ∃D₀:ℕ,2≤D₀ ∧ ∀{D:ℕ} (χ:RealPrimitiveCharacter D),D₀≤D → NormalizedAssumptionA χ →
      ∀β:ℂ,‖β‖<5*lemma44PaperAlpha D → ∀Bκ Ba:ℝ,0≤Bκ → 0≤Ba →
      ∀κ a:ℕ→ℂ,Proposition141KappaBound Bκ κ → Proposition141AdmissibleSequence D Ba a →
      ∀D₁ D₂ d h:ℕ,D=D₁*D₂ → 0<D₁ → 0<d → 0<h → ∀R:ℝ,(D:ℝ)^3≤R →
      proposition141SourceLargeBlock χ β κ a D₁ D₂ d h R ≤
        proposition141LargeMeanConstant*Bκ*Ba*(lemma34Tau 5 D₁:ℝ)*lemma56PrimeMass D*lemma23PaperL D^3351*
          ((D₂:ℝ)/(D:ℝ)^(3/2:ℝ))*((lemma34Tau 5 d:ℝ)/(d:ℝ))*(h.totient:ℝ)⁻¹ := by
  obtain ⟨D₀,hD₀,hblock⟩ := proposition141_uniform_localized_conductor_block
  refine ⟨D₀,hD₀,?_⟩
  intro D χ hlarge hA β hβ Bκ Ba hBκ hBa κ a hκ ha D₁ D₂ d h hDD hD₁ hd hh R hR
  have hDp : 0<D := by have := hD₀.trans hlarge; omega
  have hD₂ : 0<D₂ := by
    by_contra hn
    have hz:D₂=0 := by omega
    rw [hz,mul_zero] at hDD
    omega
  have hDR : 0<(D:ℝ) := by exact_mod_cast hDp
  have hRp : 0<R := (pow_pos hDR 3).trans_le hR
  let Q := proposition141SourceLargeModuli D₁ D₂ d h R a
  by_cases hQ:Q.Nonempty
  · have hcut := proposition141_source_large_block_cutoff ha hDD hD₁ hD₂ hd hh hRp.le hQ
    have hb := hblock χ hlarge hA β hβ Bκ hBκ κ hκ D₁ D₂ d h hD₁ hd hh R hR hcut Q
      (fun r hr=>(proposition141_source_large_moduli_mem hr).1)
      (fun r hr=>(proposition141_source_large_moduli_mem hr).2.1)
      (fun r hr=>(proposition141_source_large_moduli_mem hr).2.2.1.le)
    apply (proposition141_source_large_block_le χ β κ ha hD₂ hd hh R).trans
    have hb' := mul_le_mul_of_nonneg_left hb hBa
    convert hb' using 1; ring
  · have he:Q=∅ := not_nonempty_iff_eq_empty.mp hQ
    have hz : proposition141SourceLargeBlock χ β κ a D₁ D₂ d h R=0 := by
      unfold proposition141SourceLargeBlock
      rw [show proposition141SourceLargeModuli D₁ D₂ d h R a=∅ from he,sum_empty]
    rw [hz]
    have hC := proposition141_large_mean_constant_pos.le
    have hM := lemma56_prime_mass_nonneg D
    have hL0 : 0≤lemma23PaperL D := Real.log_natCast_nonneg D
    positivity

end ZhangLS.Spec
