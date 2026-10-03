import ZhangLS.Spec.QuotientSourceConductorCover

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

/-- A positive natural series with proved finite support is the literal
closed finite sum. No convergence or truncation premise is introduced. -/
theorem quotientSource_tsum_pnat_eq_sum (X : ℕ) (F : ℕ→ℝ)
    (hzero : ∀ d : ℕ, 0<d → X<d → F d=0) :
    (∑' d : ℕ+, F (d:ℕ)) = ∑d∈Icc 1 X,F d := by
  let S : Finset ℕ+ := (Icc 1 X).preimage (fun d : ℕ+ => (d:ℕ))
    (fun _ _ _ _ he => PNat.eq he)
  calc
    _ = ∑d∈S,F (d:ℕ) := by
      apply tsum_eq_sum
      intro d hd
      apply hzero d d.property
      have hn : ¬(d:ℕ)∈Icc 1 X := by simpa [S] using hd
      have hp := d.property
      simp only [mem_Icc] at hn
      exact lt_of_not_ge (fun hle => hn ⟨d.property,hle⟩)
    _ = _ := by
      apply sum_preimage
      intro d hd hn
      exact False.elim (hn ⟨⟨d,(mem_Icc.mp hd).1⟩,rfl⟩)

/-- The actual source vanishes beyond the derived outer-d bound. -/
theorem quotientSource_actual_row_zero_of_outer {D D₁ D₂ d : ℕ}
    (χ : RealPrimitiveCharacter D) (β : ℂ) (κ : ℕ→ℂ) {Ba : ℝ} {a : ℕ→ℂ}
    (ha : Proposition141AdmissibleSequence D Ba a)
    (hD : 1<D) (hmod : 2*(D:ℝ)^2*lemma61PaperP4 D≤lemma23PaperP D)
    (hDD : D=D₁*D₂) (hD₁ : 0<D₁) (hd : 0<d)
    (hout : ⌊lemma23PaperP D⌋₊<d) :
    (∑' i : quotientConductorSource D₂, quotientConductorSourceTerm χ β κ a D₁ D₂ d i)=0 := by
  have hD₂ : 0<D₂ := by nlinarith
  suffices hz : ∀ i : quotientConductorSource D₂, quotientConductorSourceTerm χ β κ a D₁ D₂ d i=0 by
    simp only [hz,tsum_zero]
  intro i
  by_contra hne
  have ht : quotientConductorTargetTerm χ β κ a D₁ D₂ d
      (quotientConductorForward D₂ hD₂ i) ≠ 0 := by
    rwa [←quotientConductor_source_target_forward χ β κ a D₁ D₂ d hD₂]
  have hs := quotientConductor_target_outer_support χ β κ ha hD hmod hDD hD₁ hd _ ht
  omega

/-- One entire source row is controlled by the actual full-sigma small and
large conductor rows, with the literal short coefficient in every weight. -/
theorem quotientSource_actual_row_le_conductor {D D₁ D₂ d : ℕ}
    (χ : RealPrimitiveCharacter D) (β : ℂ) (κ : ℕ→ℂ) {Ba : ℝ} {a : ℕ→ℂ}
    (ha : Proposition141AdmissibleSequence D Ba a)
    (hD : 1<D) (hmod : 2*(D:ℝ)^2*lemma61PaperP4 D≤lemma23PaperP D)
    (hDD : D=D₁*D₂) (hD₁ : 0<D₁) (hd : 0<d) :
    (∑' i : quotientConductorSource D₂, quotientConductorSourceTerm χ β κ a D₁ D₂ d i) ≤
    ∑h∈Icc 1 ⌊lemma23PaperP D⌋₊,
      ((∑r∈proposition141SourceSmallModuli D D₁ D₂ d h a,
        quotientSourceSmallRowTerm χ β κ a D₁ D₂ d h r)+
      (∑j∈range (proposition141DyadicBlockCount D),
        proposition141SourceUnlocalizedLargeBlock χ β κ a D₁ D₂ d h (proposition141DyadicScale D j))) := by
  apply (quotientSource_actual_row_le_box χ β κ ha hD hmod hDD hD₁ hd).trans
  exact sum_le_sum (fun h _ => quotientSource_actual_conductor_row_le χ β κ a D₁ D₂ d h hD)

/-- Exactly the normalized pre-reindex source from the frozen transport
packet, retaining the positive d,k series, divisor-D₁ sum and full σ. -/
noncomputable def quotientSourceNormalizedSource {D : ℕ}
    (χ : RealPrimitiveCharacter D) (β : ℂ) (κ a : ℕ→ℂ) : ℝ :=
  ‖(lemma51PaperT0 D:ℂ)^β‖/Real.sqrt (D:ℝ)*
    (∑D₁∈D.divisors, ∑'d : ℕ+, ∑'k : ℕ+,
      ∑i : primitiveConductorFamilyIndex ((D/D₁)*(k:ℕ)),
        quotientConductorSourceTerm χ β κ a D₁ (D/D₁) (d:ℕ) ⟨k,i⟩)

/-- Pure positive assembly of the original source into the existing complete
majorant. The only size premise supplies the proved a*-support geometry;
κ and the entire complex β are unrestricted in this arithmetic step. -/
theorem quotientSource_normalized_le_complete_conductor {D : ℕ}
    (χ : RealPrimitiveCharacter D) (β : ℂ) (κ : ℕ→ℂ) {Ba : ℝ} {a : ℕ→ℂ}
    (ha : Proposition141AdmissibleSequence D Ba a)
    (hD : 1<D) (hmod : 2*(D:ℝ)^2*lemma61PaperP4 D≤lemma23PaperP D) :
    quotientSourceNormalizedSource χ β κ a ≤ proposition141CompleteConductorMajorant χ β κ a := by
  let X := ⌊lemma23PaperP D⌋₊
  let M := ∑D₁∈D.divisors,∑d∈Icc 1 X,∑h∈Icc 1 X,
    ((∑r∈proposition141SourceSmallModuli D D₁ (D/D₁) d h a,
      quotientSourceSmallRowTerm χ β κ a D₁ (D/D₁) d h r)+
    (∑j∈range (proposition141DyadicBlockCount D),
      proposition141SourceUnlocalizedLargeBlock χ β κ a D₁ (D/D₁) d h (proposition141DyadicScale D j)))
  have hM : ‖(lemma51PaperT0 D:ℂ)^β‖/Real.sqrt (D:ℝ)*M =
      proposition141CompleteConductorMajorant χ β κ a := by
    simp only [M,X,quotientSourceSmallRowTerm,proposition141CompleteConductorMajorant,
      proposition141NormalizedUnlocalizedSmallAggregate,proposition141NormalizedUnlocalizedLargeAggregate,
      sum_add_distrib,mul_add]
  rw [←hM]
  unfold quotientSourceNormalizedSource
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply sum_le_sum
  intro D₁ hdiv
  have hD₁ : 0<D₁ := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hdiv).1 (by omega)
  have hDD : D=D₁*(D/D₁) := (Nat.mul_div_cancel' (Nat.mem_divisors.mp hdiv).1).symm
  have he (d : ℕ+) := quotientSource_nested_source_eq χ β κ ha d.property (D₁:=D₁) (D₂:=D/D₁)
  have hts : (∑'d : ℕ+, ∑'k : ℕ+, ∑i : primitiveConductorFamilyIndex ((D/D₁)*(k:ℕ)),
      quotientConductorSourceTerm χ β κ a D₁ (D/D₁) (d:ℕ) ⟨k,i⟩) =
      ∑'d : ℕ+, ∑'i : quotientConductorSource (D/D₁),
        quotientConductorSourceTerm χ β κ a D₁ (D/D₁) (d:ℕ) i := tsum_congr he
  rw [hts]
  rw [quotientSource_tsum_pnat_eq_sum X _ (fun d hd hout =>
    quotientSource_actual_row_zero_of_outer χ β κ ha hD hmod hDD hD₁ hd hout)]
  exact sum_le_sum (fun d hd => quotientSource_actual_row_le_conductor χ β κ ha hD hmod hDD hD₁ (mem_Icc.mp hd).1)

end ZhangLS.Spec
