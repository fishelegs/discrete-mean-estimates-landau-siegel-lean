import ZhangLS.Spec.QuotientConductorSums
import ZhangLS.Spec.Proposition141OffLocalSigma
import ZhangLS.Spec.Proposition141SmallConductorAggregate
import ZhangLS.Spec.Proposition141SourceOuterSupport

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

/-- The exact χ-induced exclusion is invariant under equality of the common
level. Both characters are actually induced to that level. -/
theorem quotientConductor_induced_exclusion {D N M r : ℕ}
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ r)
    (he : N=M) (hrN : r ∣ N) (hrM : r ∣ M) :
    (∀ hDN : D ∣ N, θ.changeLevel hrN ≠ χ.chi.changeLevel hDN) ↔
      (∀ hDM : D ∣ M, θ.changeLevel hrM ≠ χ.chi.changeLevel hDM) := by
  subst M
  rfl

/-- Literal pre-reindex primitive-divisor term, retaining a*(d*k), (k,D₁)=1,
principal removal, the genuine χ-induced exclusion and the full σ. -/
noncomputable def quotientConductorSourceTerm {D : ℕ}
    (χ : RealPrimitiveCharacter D) (β : ℂ) (κ a : ℕ → ℂ) (D₁ D₂ d : ℕ)
    (i : quotientConductorSource D₂) : ℝ :=
  if (i.1:ℕ).Coprime D₁ ∧ 1 < i.2.1.val ∧
      (∀ hDN : D ∣ D₂*(i.1:ℕ),
        i.2.2.val.changeLevel (Nat.mem_divisors.mp i.2.1.property).1 ≠ χ.chi.changeLevel hDN) then
    ‖a (d*(i.1:ℕ))‖ *
      (Real.sqrt (i.2.1.val:ℝ)/((d:ℝ)*(i.1:ℕ)*((D₂*(i.1:ℕ)).totient:ℝ))) *
      ‖proposition141Sigma χ i.2.2.val β κ D₁ d (D₂*(i.1:ℕ)/i.2.1.val)‖
  else 0

/-- Exact quotient-conductor term after k=r*h/D₂, with no additional
coprimality assumptions on h,r or D₁,D₂. -/
noncomputable def quotientConductorTargetTerm {D : ℕ}
    (χ : RealPrimitiveCharacter D) (β : ℂ) (κ a : ℕ → ℂ) (D₁ D₂ d : ℕ)
    (i : quotientConductorTarget D₂) : ℝ :=
  if ((i.1:ℕ)*(i.2.1.val:ℕ)/D₂).Coprime D₁ ∧ 1 < (i.1:ℕ) ∧
      (∀ hDN : D ∣ (i.1:ℕ)*(i.2.1.val:ℕ),
        i.2.2.val.changeLevel ((i.1:ℕ).dvd_mul_right (i.2.1.val:ℕ)) ≠ χ.chi.changeLevel hDN) then
    ‖a (d*((i.1:ℕ)*(i.2.1.val:ℕ)/D₂))‖ *
      ((D₂:ℝ)/((d:ℝ)*(i.2.1.val:ℕ)*(((i.1:ℕ)*(i.2.1.val:ℕ)).totient:ℝ)*Real.sqrt (i.1:ℝ))) *
      ‖proposition141Sigma χ i.2.2.val β κ D₁ d (i.2.1.val:ℕ)‖
  else 0

/-- Pointwise identity for the literal source functions, including every filter. -/
theorem quotientConductor_source_target_term {D : ℕ}
    (χ : RealPrimitiveCharacter D) (β : ℂ) (κ a : ℕ → ℂ) (D₁ D₂ d : ℕ)
    (hD : 0 < D₂) (i : quotientConductorTarget D₂) :
    quotientConductorSourceTerm χ β κ a D₁ D₂ d (quotientConductorBackward D₂ hD i) =
      quotientConductorTargetTerm χ β κ a D₁ D₂ d i := by
  rcases i with ⟨r,h,θ⟩
  have hk := quotientConductor_backward hD r.property h.val.property h.property
  have he : D₂*((r:ℕ)*(h.val:ℕ)/D₂) = (r:ℕ)*(h.val:ℕ) := Nat.mul_div_cancel' h.property
  have hx := quotientConductor_induced_exclusion χ θ.val he hk.2.1
    ((r:ℕ).dvd_mul_right (h.val:ℕ))
  have hw := quotientConductor_weight (d:=d) hD r.property he.symm
  dsimp [quotientConductorSourceTerm,quotientConductorTargetTerm,quotientConductorBackward]
  split_ifs with h₁ h₂ h₂
  · congr 2
    · simpa only [Nat.mul_comm] using hw
    · exact congrArg (fun n => proposition141Sigma χ θ.val β κ D₁ d n) hk.2.2
  · exact False.elim (h₂ ⟨h₁.1,h₁.2.1,hx.mp h₁.2.2⟩)
  · exact False.elim (h₁ ⟨h₂.1,h₂.2.1,hx.mpr h₂.2.2⟩)
  · rfl

/-- Source term vanishes with its actual original short coefficient. -/
theorem quotientConductor_source_term_zero {D : ℕ}
    (χ : RealPrimitiveCharacter D) (β : ℂ) (κ a : ℕ → ℂ) (D₁ D₂ d : ℕ)
    (i : quotientConductorSource D₂) (hz : a (d*(i.1:ℕ)) = 0) :
    quotientConductorSourceTerm χ β κ a D₁ D₂ d i = 0 := by
  simp [quotientConductorSourceTerm,hz]

/-- Absolute convergence of the outer source sum is a theorem of the original
closed coefficient support, not an extra hypothesis on a truncation. -/
theorem quotientConductor_actual_source_summable {D D₁ D₂ d : ℕ}
    (χ : RealPrimitiveCharacter D) (β : ℂ) (κ : ℕ → ℂ) {Ba : ℝ} {a : ℕ → ℂ}
    (ha : Proposition141AdmissibleSequence D Ba a) (hd : 0 < d) :
    Summable (quotientConductorSourceTerm χ β κ a D₁ D₂ d) :=
  quotientConductor_source_summable ha hd _
    (quotientConductor_source_term_zero χ β κ a D₁ D₂ d)

/-- The forward form of the literal identity, with the same primitive character. -/
theorem quotientConductor_source_target_forward {D : ℕ}
    (χ : RealPrimitiveCharacter D) (β : ℂ) (κ a : ℕ → ℂ) (D₁ D₂ d : ℕ)
    (hD : 0 < D₂) (i : quotientConductorSource D₂) :
    quotientConductorSourceTerm χ β κ a D₁ D₂ d i =
      quotientConductorTargetTerm χ β κ a D₁ D₂ d (quotientConductorForward D₂ hD i) := by
  simpa only [quotientConductor_backward_forward] using
    quotientConductor_source_target_term χ β κ a D₁ D₂ d hD
      (quotientConductorForward D₂ hD i)

/-- Exact one-series transport requires no convergence assumption. -/
theorem quotientConductor_actual_tsum_eq {D : ℕ}
    (χ : RealPrimitiveCharacter D) (β : ℂ) (κ a : ℕ → ℂ) (D₁ D₂ d : ℕ)
    (hD : 0 < D₂) :
    (∑' i : quotientConductorSource D₂, quotientConductorSourceTerm χ β κ a D₁ D₂ d i) =
      ∑' j : quotientConductorTarget D₂, quotientConductorTargetTerm χ β κ a D₁ D₂ d j := by
  calc
    _ = ∑' i : quotientConductorSource D₂,
        quotientConductorTargetTerm χ β κ a D₁ D₂ d (quotientConductorForward D₂ hD i) :=
      tsum_congr (quotientConductor_source_target_forward χ β κ a D₁ D₂ d hD)
    _ = _ := quotientConductor_tsum D₂ hD _

/-- The target finite box is the exact image of the original coefficient box. -/
noncomputable def quotientConductorTargetBox (D D₂ : ℕ) (hD : 0 < D₂) :
    Finset (quotientConductorTarget D₂) :=
  (quotientConductorSourceBox D D₂).map (quotientConductorEquiv D₂ hD).toEmbedding

@[simp] theorem quotientConductor_mem_targetBox {D D₂ : ℕ} (hD : 0 < D₂)
    (i : quotientConductorTarget D₂) :
    i ∈ quotientConductorTargetBox D D₂ hD ↔
      (i.1:ℕ)*(i.2.1.val:ℕ)/D₂ ∈ proposition141Indices D := by
  rw [quotientConductorTargetBox, Finset.mem_map]
  constructor
  · rintro ⟨j,hj,hji⟩
    have hb : quotientConductorBackward D₂ hD i = j := by
      rw [←hji]
      exact quotientConductor_backward_forward D₂ hD j
    have hm := (quotientConductor_mem_sourceBox j).mp hj
    simpa only [←hb, quotientConductor_backward_k] using hm
  · intro hi
    refine ⟨quotientConductorBackward D₂ hD i, ?_, ?_⟩
    · exact (quotientConductor_mem_sourceBox _).mpr hi
    · exact quotientConductor_forward_backward D₂ hD i

/-- The original closed support is transported literally, without weakening
n ≤ 2P₄ to a strict endpoint or adding any coprimality condition. -/
theorem quotientConductor_actual_target_closed_support {D D₁ D₂ d : ℕ}
    (χ : RealPrimitiveCharacter D) (β : ℂ) (κ : ℕ → ℂ) {Ba : ℝ} {a : ℕ → ℂ}
    (ha : Proposition141AdmissibleSequence D Ba a) (i : quotientConductorTarget D₂)
    (hi : quotientConductorTargetTerm χ β κ a D₁ D₂ d i ≠ 0) :
    ((d*((i.1:ℕ)*(i.2.1.val:ℕ)/D₂):ℕ):ℝ) ≤ 2*lemma61PaperP4 D := by
  apply proposition141_nonzero_support ha
  intro hz
  exact hi (by simp [quotientConductorTargetTerm,hz])

/-- Target summability is derived from the actual a* cutoff. -/
theorem quotientConductor_actual_target_summable {D D₁ D₂ d : ℕ}
    (χ : RealPrimitiveCharacter D) (β : ℂ) (κ : ℕ → ℂ) {Ba : ℝ} {a : ℕ → ℂ}
    (ha : Proposition141AdmissibleSequence D Ba a) (hd : 0 < d) (hD : 0 < D₂) :
    Summable (quotientConductorTargetTerm χ β κ a D₁ D₂ d) := by
  apply (quotientConductorEquiv D₂ hD).summable_iff.mp
  have hs := quotientConductor_actual_source_summable χ β κ ha hd (D₁:=D₁) (D₂:=D₂)
  exact hs.congr (quotientConductor_source_target_forward χ β κ a D₁ D₂ d hD)

/-- Finite original coefficient support transports through the exact index
bijection; no source or target truncation equality is assumed. -/
theorem quotientConductor_actual_finite_sum_eq {D D₁ D₂ d : ℕ}
    (χ : RealPrimitiveCharacter D) (β : ℂ) (κ : ℕ → ℂ) {Ba : ℝ} {a : ℕ → ℂ}
    (ha : Proposition141AdmissibleSequence D Ba a) (hd : 0 < d) (hD : 0 < D₂) :
    (∑' i : quotientConductorSource D₂, quotientConductorSourceTerm χ β κ a D₁ D₂ d i) =
      ∑ j ∈ quotientConductorTargetBox D D₂ hD,
        quotientConductorTargetTerm χ β κ a D₁ D₂ d j := by
  rw [quotientConductor_source_tsum_eq_sum ha hd _
    (quotientConductor_source_term_zero χ β κ a D₁ D₂ d)]
  simp_rw [quotientConductor_source_target_forward χ β κ a D₁ D₂ d hD]
  exact quotientConductor_finset_sum D₂ hD _ _

/-- Literal k/divisor/primitive and r/h/primitive nesting for full σ. Both
infinite interchanges use convergence proved from the original a* cutoff. -/
theorem quotientConductor_actual_nested_tsum_eq {D D₁ D₂ d : ℕ}
    (χ : RealPrimitiveCharacter D) (β : ℂ) (κ : ℕ → ℂ) {Ba : ℝ} {a : ℕ → ℂ}
    (ha : Proposition141AdmissibleSequence D Ba a) (hd : 0 < d) (hD : 0 < D₂) :
    (∑' k : ℕ+, ∑ i : primitiveConductorFamilyIndex (D₂*(k:ℕ)),
      quotientConductorSourceTerm χ β κ a D₁ D₂ d ⟨k,i⟩) =
    ∑' r : ℕ+, ∑' h : {h : ℕ+ // D₂ ∣ (r:ℕ)*(h:ℕ)},
      ∑ θ : {θ : DirichletCharacter ℂ (r:ℕ) // θ.IsPrimitive},
        quotientConductorTargetTerm χ β κ a D₁ D₂ d ⟨r,h,θ⟩ := by
  have hs := quotientConductor_actual_source_summable χ β κ ha hd (D₁:=D₁) (D₂:=D₂)
  have hst := hs.congr (quotientConductor_source_target_forward χ β κ a D₁ D₂ d hD)
  have he := quotientConductor_nested_tsum D₂ hD
    (quotientConductorTargetTerm χ β κ a D₁ D₂ d) hst
  simp_rw [←quotientConductor_source_target_forward χ β κ a D₁ D₂ d hD] at he
  simpa only [tsum_fintype] using he

/-- A nonzero target term retains the exact original predicates and coefficient. -/
theorem quotientConductor_target_nonzero_data {D D₁ D₂ d : ℕ}
    (χ : RealPrimitiveCharacter D) (β : ℂ) (κ a : ℕ → ℂ)
    (i : quotientConductorTarget D₂)
    (hi : quotientConductorTargetTerm χ β κ a D₁ D₂ d i ≠ 0) :
    ((i.1:ℕ)*(i.2.1.val:ℕ)/D₂).Coprime D₁ ∧ 1 < (i.1:ℕ) ∧
      (∀ hDN : D ∣ (i.1:ℕ)*(i.2.1.val:ℕ),
        i.2.2.val.changeLevel ((i.1:ℕ).dvd_mul_right (i.2.1.val:ℕ)) ≠ χ.chi.changeLevel hDN) ∧
      a (d*((i.1:ℕ)*(i.2.1.val:ℕ)/D₂)) ≠ 0 := by
  have hz : a (d*((i.1:ℕ)*(i.2.1.val:ℕ)/D₂)) ≠ 0 := by
    intro he
    exact hi (by simp [quotientConductorTargetTerm,he])
  unfold quotientConductorTargetTerm at hi
  split_ifs at hi with hp
  · exact ⟨hp.1,hp.2.1,hp.2.2,hz⟩
  · exact False.elim (hi rfl)

/-- An explicit target support theorem; the finite box is derived from a*. -/
theorem quotientConductor_actual_target_finite_support {D D₁ D₂ d : ℕ}
    (χ : RealPrimitiveCharacter D) (β : ℂ) (κ : ℕ → ℂ) {Ba : ℝ} {a : ℕ → ℂ}
    (ha : Proposition141AdmissibleSequence D Ba a) (hd : 0 < d) (hD : 0 < D₂) :
    Function.HasFiniteSupport (quotientConductorTargetTerm χ β κ a D₁ D₂ d) := by
  apply (quotientConductorTargetBox D D₂ hD).finite_toSet.subset
  intro i hi
  apply (quotientConductor_mem_targetBox hD i).mpr
  have han := (quotientConductor_target_nonzero_data χ β κ a i hi).2.2.2
  have hk := (quotientConductor_backward hD i.1.property i.2.1.val.property i.2.1.property).1
  exact (proposition141_nonzero_product_indices ha hd hk han).2

/-- The target's genuine nonzero support lies in the outer box used by the
complete conductor aggregate. No outer-box hypothesis is supplied. -/
theorem quotientConductor_target_outer_support {D D₁ D₂ d : ℕ}
    (χ : RealPrimitiveCharacter D) (β : ℂ) (κ : ℕ → ℂ) {Ba : ℝ} {a : ℕ → ℂ}
    (ha : Proposition141AdmissibleSequence D Ba a)
    (hD : 1 < D) (hmod : 2*(D:ℝ)^2*lemma61PaperP4 D ≤ lemma23PaperP D)
    (hDD : D=D₁*D₂) (hD₁ : 0<D₁) (hd : 0<d)
    (i : quotientConductorTarget D₂)
    (hi : quotientConductorTargetTerm χ β κ a D₁ D₂ d i ≠ 0) :
    d ≤ ⌊lemma23PaperP D⌋₊ ∧ (i.2.1.val:ℕ) ≤ ⌊lemma23PaperP D⌋₊ ∧
      (i.1:ℕ) ≤ ⌊lemma23PaperP D⌋₊ ∧
      (i.2.1.val:ℕ)*(i.1:ℕ) ≤ ⌊lemma23PaperP D⌋₊ := by
  have han := (quotientConductor_target_nonzero_data χ β κ a i hi).2.2.2
  apply proposition141_source_outer_support ha hD hmod hDD hD₁ hd
    i.2.1.val.property i.1.property
  · simpa only [Nat.mul_comm] using i.2.1.property
  · simpa only [Nat.mul_comm] using han

/-- Fully expanded original σ wrapper: the entire positive long series stays
inside each norm, and no localized or finite-long substitute is introduced. -/
theorem quotientConductor_original_full_sigma_reindex {D D₁ D₂ d : ℕ}
    (χ : RealPrimitiveCharacter D) (β : ℂ) (κ : ℕ → ℂ) {Ba : ℝ} {a : ℕ → ℂ}
    (ha : Proposition141AdmissibleSequence D Ba a) (hd : 0 < d) (hD : 0 < D₂) :
    (∑' k : ℕ+, ∑ i : primitiveConductorFamilyIndex (D₂*(k:ℕ)),
      if (k:ℕ).Coprime D₁ ∧ 1 < i.1.val ∧
        (∀ hDN : D ∣ D₂*(k:ℕ),
          i.2.val.changeLevel (Nat.mem_divisors.mp i.1.property).1 ≠ χ.chi.changeLevel hDN) then
        ‖a (d*(k:ℕ))‖ * (Real.sqrt (i.1.val:ℝ)/((d:ℝ)*(k:ℕ)*((D₂*(k:ℕ)).totient:ℝ))) *
          ‖∑' l : ℕ, proposition141SigmaTerm χ i.2.val β κ D₁ d (D₂*(k:ℕ)/i.1.val) l‖
      else 0) =
    ∑' r : ℕ+, ∑' h : {h : ℕ+ // D₂ ∣ (r:ℕ)*(h:ℕ)},
      ∑ θ : {θ : DirichletCharacter ℂ (r:ℕ) // θ.IsPrimitive},
        if ((r:ℕ)*(h.val:ℕ)/D₂).Coprime D₁ ∧ 1 < (r:ℕ) ∧
          (∀ hDN : D ∣ (r:ℕ)*(h.val:ℕ),
            θ.val.changeLevel ((r:ℕ).dvd_mul_right (h.val:ℕ)) ≠ χ.chi.changeLevel hDN) then
          ‖a (d*((r:ℕ)*(h.val:ℕ)/D₂))‖ *
            ((D₂:ℝ)/((d:ℝ)*(h.val:ℕ)*(((r:ℕ)*(h.val:ℕ)).totient:ℝ)*Real.sqrt (r:ℝ))) *
            ‖∑' l : ℕ, proposition141SigmaTerm χ θ.val β κ D₁ d (h.val:ℕ) l‖
        else 0 := by
  exact quotientConductor_actual_nested_tsum_eq χ β κ ha hd hD

/-- All original positive d and divisor-D₁ outer indices and the exterior
normalization are preserved. Pointwise congruence does not exchange d-series. -/
theorem quotientConductor_normalized_outer_reindex {D : ℕ}
    (χ : RealPrimitiveCharacter D) (β : ℂ) (κ : ℕ → ℂ) {Ba : ℝ} {a : ℕ → ℂ}
    (ha : Proposition141AdmissibleSequence D Ba a) (hD : 0 < D) :
    ‖(lemma51PaperT0 D:ℂ)^β‖/Real.sqrt (D:ℝ) *
      (∑ D₁ ∈ D.divisors, ∑' d : ℕ+, ∑' k : ℕ+,
        ∑ i : primitiveConductorFamilyIndex ((D/D₁)*(k:ℕ)),
          quotientConductorSourceTerm χ β κ a D₁ (D/D₁) (d:ℕ) ⟨k,i⟩) =
    ‖(lemma51PaperT0 D:ℂ)^β‖/Real.sqrt (D:ℝ) *
      (∑ D₁ ∈ D.divisors, ∑' d : ℕ+, ∑' r : ℕ+,
        ∑' h : {h : ℕ+ // D/D₁ ∣ (r:ℕ)*(h:ℕ)},
          ∑ θ : {θ : DirichletCharacter ℂ (r:ℕ) // θ.IsPrimitive},
            quotientConductorTargetTerm χ β κ a D₁ (D/D₁) (d:ℕ) ⟨r,h,θ⟩) := by
  congr 1
  apply sum_congr rfl
  intro D₁ hD₁
  apply tsum_congr
  intro d
  have hdiv := (Nat.mem_divisors.mp hD₁).1
  have hp : 0 < D₁ := Nat.pos_of_dvd_of_pos hdiv hD
  have hD₂ : 0 < D/D₁ := Nat.div_pos (Nat.le_of_dvd hD hdiv) hp
  exact quotientConductor_actual_nested_tsum_eq χ β κ ha d.property hD₂

end ZhangLS.Spec
