import ZhangLS.Spec.QuotientConductorIndex
import Mathlib.Data.Finset.Preimage

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

/-- Finite exact reindexing; this does not discard any endpoint. -/
theorem quotientConductor_finset_sum {A : Type*} [AddCommMonoid A]
    (D₂ : ℕ) (hD : 0 < D₂) (S : Finset (quotientConductorSource D₂))
    (F : quotientConductorTarget D₂ → A) :
    (∑ i ∈ S, F (quotientConductorForward D₂ hD i)) =
      ∑ j ∈ S.map (quotientConductorEquiv D₂ hD).toEmbedding, F j := by
  symm
  exact Finset.sum_map _ _ _

/-- An equivalence alone transports a single tsum; it does not exchange nesting. -/
theorem quotientConductor_tsum {A : Type*} [AddCommMonoid A] [TopologicalSpace A]
    (D₂ : ℕ) (hD : 0 < D₂) (F : quotientConductorTarget D₂ → A) :
    (∑' i : quotientConductorSource D₂, F (quotientConductorForward D₂ hD i)) =
      ∑' j : quotientConductorTarget D₂, F j :=
  (quotientConductorEquiv D₂ hD).tsum_eq F

/-- Literal k/divisor/primitive and r/h/primitive nested series. Every
exchange of infinite sums is justified by the displayed summability input. -/
theorem quotientConductor_nested_tsum {A : Type*}
    [NormedAddCommGroup A] [CompleteSpace A] (D₂ : ℕ) (hD : 0 < D₂)
    (F : quotientConductorTarget D₂ → A)
    (hF : Summable (fun i : quotientConductorSource D₂ => F (quotientConductorForward D₂ hD i))) :
    (∑' k : ℕ+, ∑' i : primitiveConductorFamilyIndex (D₂*(k:ℕ)),
      F (quotientConductorForward D₂ hD ⟨k,i⟩)) =
    ∑' r : ℕ+, ∑' h : {h : ℕ+ // D₂ ∣ (r:ℕ)*(h:ℕ)},
      ∑' θ : {θ : DirichletCharacter ℂ (r:ℕ) // θ.IsPrimitive}, F ⟨r,h,θ⟩ := by
  have hT : Summable F := (quotientConductorEquiv D₂ hD).summable_iff.mp hF
  rw [←hF.tsum_sigma]
  change (∑' i : quotientConductorSource D₂, F (quotientConductorForward D₂ hD i)) = _
  rw [quotientConductor_tsum D₂ hD F]
  change (∑' j : Σ r : ℕ+, Σ _h : {h : ℕ+ // D₂ ∣ (r:ℕ)*(h:ℕ)},
    {θ : DirichletCharacter ℂ (r:ℕ) // θ.IsPrimitive}, F j) = _
  rw [hT.tsum_sigma]
  apply tsum_congr
  intro r
  exact (hT.sigma_factor r).tsum_sigma

noncomputable def quotientConductorKBox (D : ℕ) : Finset ℕ+ :=
  (proposition141Indices D).preimage (fun k : ℕ+ => (k:ℕ))
    (fun _ _ _ _ he => PNat.eq he)

noncomputable def quotientConductorSourceBox (D D₂ : ℕ) : Finset (quotientConductorSource D₂) :=
  (quotientConductorKBox D).sigma (fun _ => univ)

@[simp] theorem quotientConductor_mem_sourceBox {D D₂ : ℕ} (i : quotientConductorSource D₂) :
    i ∈ quotientConductorSourceBox D D₂ ↔ (i.1:ℕ) ∈ proposition141Indices D := by
  change i ∈ (quotientConductorKBox D).sigma (fun k : ℕ+ =>
    (univ : Finset (primitiveConductorFamilyIndex (D₂*(k:ℕ))))) ↔ _
  exact (Finset.mem_sigma (a := i)).trans (by simp [quotientConductorKBox])

/-- The finite source support follows from the original closed a* cutoff.
There is no arbitrary finite truncation hypothesis. -/
theorem quotientConductor_source_finite_support {D D₂ d : ℕ} {Ba : ℝ} {a : ℕ → ℂ}
    (ha : Proposition141AdmissibleSequence D Ba a) (hd : 0 < d)
    {A : Type*} [Zero A] (F : quotientConductorSource D₂ → A)
    (hzero : ∀ i, a (d*(i.1:ℕ)) = 0 → F i = 0) : Function.HasFiniteSupport F := by
  apply (quotientConductorSourceBox D D₂).finite_toSet.subset
  intro i hi
  apply (quotientConductor_mem_sourceBox i).mpr
  have han : a (d*(i.1:ℕ)) ≠ 0 := by
    intro hz
    exact hi (hzero i hz)
  exact (proposition141_nonzero_product_indices ha hd i.1.property han).2

/-- Actual supported source functions are summable, before any nesting changes. -/
theorem quotientConductor_source_summable {D D₂ d : ℕ} {Ba : ℝ} {a : ℕ → ℂ}
    (ha : Proposition141AdmissibleSequence D Ba a) (hd : 0 < d)
    {A : Type*} [AddCommMonoid A] [TopologicalSpace A]
    (F : quotientConductorSource D₂ → A)
    (hzero : ∀ i, a (d*(i.1:ℕ)) = 0 → F i = 0) : Summable F :=
  summable_of_hasFiniteSupport (quotientConductor_source_finite_support ha hd F hzero)

/-- Exact finite-box formula derived from the coefficient, including the
closed original boundary, with no extra truncation assumption. -/
theorem quotientConductor_source_tsum_eq_sum {D D₂ d : ℕ} {Ba : ℝ} {a : ℕ → ℂ}
    (ha : Proposition141AdmissibleSequence D Ba a) (hd : 0 < d)
    {A : Type*} [AddCommMonoid A] [TopologicalSpace A]
    (F : quotientConductorSource D₂ → A)
    (hzero : ∀ i, a (d*(i.1:ℕ)) = 0 → F i = 0) :
    (∑' i, F i) = ∑ i ∈ quotientConductorSourceBox D D₂, F i := by
  apply tsum_eq_sum
  intro i hi
  apply hzero
  by_contra han
  exact hi ((quotientConductor_mem_sourceBox i).mpr
    (proposition141_nonzero_product_indices ha hd i.1.property han).2)

end ZhangLS.Spec
