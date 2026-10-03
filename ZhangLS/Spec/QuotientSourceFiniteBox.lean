import ZhangLS.Spec.QuotientConductorSource
import ZhangLS.Spec.Proposition141CompleteConductorRate

set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

/-- Nonnegative finite sums may be enlarged through an injection on their
actual support. Zero summands need no artificial support condition. -/
theorem quotientSource_sum_le_of_support_injective {ι κ : Type*}
    (S : Finset ι) (T : Finset κ) (f : ι → ℝ) (g : κ → ℝ)
    (e : ι → κ) (he : Function.Injective e)
    (hmem : ∀ i ∈ S, f i ≠ 0 → e i ∈ T)
    (hle : ∀ i ∈ S, f i ≤ g (e i)) (hg : ∀ j, 0 ≤ g j) :
    ∑ i ∈ S, f i ≤ ∑ j ∈ T, g j := by
  let U := S.filter (fun i => f i ≠ 0)
  have hU : ∑ i ∈ S, f i = ∑ i ∈ U, f i := by
    symm
    simp only [U, sum_filter]
    apply sum_congr rfl
    intro i hi
    split_ifs with hz
    · rfl
    · exact (not_ne_iff.mp hz).symm
  rw [hU]
  calc
    _ ≤ ∑ i ∈ U, g (e i) := sum_le_sum (fun i hi => hle i (mem_filter.mp hi).1)
    _ = ∑ j ∈ U.image e, g j := (sum_image (fun _ _ _ _ h => he h)).symm
    _ ≤ ∑ j ∈ T, g j := sum_le_sum_of_subset_of_nonneg
      (by intro j hj; rcases mem_image.mp hj with ⟨i,hi,rfl⟩; exact hmem i (mem_filter.mp hi).1 (mem_filter.mp hi).2)
      (fun j _ _ => hg j)

/-- An ambient natural-number row retains every source predicate. -/
noncomputable def quotientSourceFlatTerm {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (κ a : ℕ → ℂ) (D₁ D₂ d h r : ℕ) (θ : DirichletCharacter ℂ r) : ℝ :=
  if D₂ ∣ r*h ∧ (r*h/D₂).Coprime D₁ ∧ 1<r ∧ θ.IsPrimitive ∧
      (∀ hDN : D ∣ r*h, θ.changeLevel (r.dvd_mul_right h) ≠ χ.chi.changeLevel hDN) then
    ‖a (d*(r*h/D₂))‖*(D₂:ℝ)*
      ((d:ℝ)*(h:ℝ)*((r*h).totient:ℝ)*Real.sqrt (r:ℝ))⁻¹*
        ‖proposition141Sigma χ θ β κ D₁ d h‖
  else 0

theorem quotientSource_flat_nonneg {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (κ a : ℕ → ℂ) (D₁ D₂ d h r : ℕ) (θ : DirichletCharacter ℂ r) :
    0 ≤ quotientSourceFlatTerm χ β κ a D₁ D₂ d h r θ := by
  unfold quotientSourceFlatTerm
  split_ifs <;> positivity

/-- The full ambient row index carries the literal primitive character. -/
abbrev quotientSourceRowIndex : Type := Σ _h : ℕ, Σ r : ℕ, DirichletCharacter ℂ r

def quotientSourceTargetRowMap {D₂ : ℕ} (i : quotientConductorTarget D₂) :
    quotientSourceRowIndex := ⟨i.2.1.val, i.1, i.2.2.val⟩

theorem quotientSource_target_row_injective {D₂ : ℕ} :
    Function.Injective (@quotientSourceTargetRowMap D₂) := by
  rintro ⟨⟨r,hr⟩,⟨⟨⟨h,hh⟩,hv⟩,⟨θ,hθ⟩⟩⟩ ⟨⟨s,hs⟩,⟨⟨⟨k,hk⟩,hw⟩,⟨η,hη⟩⟩⟩ he
  dsimp [quotientSourceTargetRowMap] at he
  cases he
  rfl

theorem quotientSource_target_eq_flat {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (κ a : ℕ → ℂ) (D₁ D₂ d : ℕ) (i : quotientConductorTarget D₂) :
    quotientConductorTargetTerm χ β κ a D₁ D₂ d i =
      quotientSourceFlatTerm χ β κ a D₁ D₂ d i.2.1.val i.1 i.2.2.val := by
  simp only [quotientConductorTargetTerm, quotientSourceFlatTerm,
    i.2.1.property, i.2.2.property, true_and, div_eq_mul_inv, mul_assoc]

/-- The k/divisor nesting is the single actual supported source series. -/
theorem quotientSource_nested_source_eq {D D₁ D₂ d : ℕ}
    (χ : RealPrimitiveCharacter D) (β : ℂ) (κ : ℕ → ℂ) {Ba : ℝ} {a : ℕ → ℂ}
    (ha : Proposition141AdmissibleSequence D Ba a) (hd : 0<d) :
    (∑' k : ℕ+, ∑ i : primitiveConductorFamilyIndex (D₂*(k:ℕ)),
      quotientConductorSourceTerm χ β κ a D₁ D₂ d ⟨k,i⟩) =
    ∑' i : quotientConductorSource D₂, quotientConductorSourceTerm χ β κ a D₁ D₂ d i := by
  have hs := quotientConductor_actual_source_summable χ β κ ha hd (D₁:=D₁) (D₂:=D₂)
  simpa only [tsum_fintype] using hs.tsum_sigma.symm

/-- Actual nonzero a* support, with its closed endpoint, puts the entire
source in the d,h,r≤floor(P) box used by the conductor aggregates. -/
theorem quotientSource_actual_row_le_box {D D₁ D₂ d : ℕ}
    (χ : RealPrimitiveCharacter D) (β : ℂ) (κ : ℕ → ℂ) {Ba : ℝ} {a : ℕ → ℂ}
    (ha : Proposition141AdmissibleSequence D Ba a)
    (hD : 1<D) (hmod : 2*(D:ℝ)^2*lemma61PaperP4 D≤lemma23PaperP D)
    (hDD : D=D₁*D₂) (hD₁ : 0<D₁) (hd : 0<d) :
    (∑' i : quotientConductorSource D₂, quotientConductorSourceTerm χ β κ a D₁ D₂ d i) ≤
    ∑ h ∈ Icc 1 ⌊lemma23PaperP D⌋₊, ∑ r ∈ Icc 1 ⌊lemma23PaperP D⌋₊,
      ∑ θ : DirichletCharacter ℂ r, quotientSourceFlatTerm χ β κ a D₁ D₂ d h r θ := by
  have hD₂ : 0<D₂ := by nlinarith
  rw [quotientConductor_actual_finite_sum_eq χ β κ ha hd hD₂]
  let T : Finset quotientSourceRowIndex :=
    (Icc 1 ⌊lemma23PaperP D⌋₊).sigma (fun _ =>
      (Icc 1 ⌊lemma23PaperP D⌋₊).sigma (fun r => (univ : Finset (DirichletCharacter ℂ r))))
  let G : quotientSourceRowIndex → ℝ := fun i => quotientSourceFlatTerm χ β κ a D₁ D₂ d i.1 i.2.1 i.2.2
  have he : (∑ j ∈ T, G j) =
      ∑ h ∈ Icc 1 ⌊lemma23PaperP D⌋₊, ∑ r ∈ Icc 1 ⌊lemma23PaperP D⌋₊,
        ∑ θ : DirichletCharacter ℂ r, quotientSourceFlatTerm χ β κ a D₁ D₂ d h r θ := by
    simp only [T, G, sum_sigma]
  rw [←he]
  apply quotientSource_sum_le_of_support_injective _ _ _ _ quotientSourceTargetRowMap
    quotientSource_target_row_injective
  · intro i hi hne
    have hs := quotientConductor_target_outer_support χ β κ ha hD hmod hDD hD₁ hd i hne
    simp only [T, quotientSourceTargetRowMap, mem_sigma, mem_Icc, mem_univ, and_true]
    exact ⟨⟨i.2.1.val.property,hs.2.1⟩,i.1.property,hs.2.2.1⟩
  · intro i hi
    exact (quotientSource_target_eq_flat χ β κ a D₁ D₂ d i).le
  · intro i
    exact quotientSource_flat_nonneg χ β κ a D₁ D₂ d i.1 i.2.1 i.2.2

end ZhangLS.Spec
