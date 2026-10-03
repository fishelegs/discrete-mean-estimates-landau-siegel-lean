import ZhangLS.Spec.QuotientSourceFiniteBox

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

/-- A finite cover bounds a nonnegative source without selecting or deleting
any endpoint, and without assuming disjointness. -/
theorem quotientSource_sum_le_cover {ι κ : Type*} (S T : Finset ι)
    (J : Finset κ) (U : κ → Finset ι) (f g l : ι → ℝ)
    (hg : ∀ i, 0≤g i) (hl : ∀ i, 0≤l i)
    (hfg : ∀ i, f i≤g i) (hfl : ∀ i, f i≤l i)
    (hcover : ∀ i∈S, f i≠0 → i∈T ∨ ∃ j∈J, i∈U j) :
    ∑ i∈S, f i ≤ (∑ i∈T, g i)+(∑ j∈J, ∑ i∈U j, l i) := by
  have hpoint (i : ι) (hi : i∈S) :
      f i ≤ (if i∈T then g i else 0)+∑ j∈J, if i∈U j then l i else 0 := by
    by_cases hz : f i=0
    · rw [hz]
      apply add_nonneg
      · split_ifs <;> simp_all
      · exact sum_nonneg (fun j _ => by split_ifs; exact hl i; rfl)
    · rcases hcover i hi hz with ht|⟨j,hj,hij⟩
      · rw [if_pos ht]
        exact (hfg i).trans (le_add_of_nonneg_right (sum_nonneg (fun j _ => by split_ifs; exact hl i; rfl)))
      · have hh : l i ≤ ∑ j∈J, if i∈U j then l i else 0 := by
          have := single_le_sum (f:=fun j => if i∈U j then l i else 0)
            (fun j _ => by dsimp; split_ifs; exact hl i; rfl) hj
          simpa only [if_pos hij] using this
        exact (hfl i).trans (hh.trans (le_add_of_nonneg_left (by split_ifs; exact hg i; rfl)))
  have hind (V : Finset ι) (q : ι→ℝ) (hq : ∀i,0≤q i) :
      (∑i∈S, if i∈V then q i else 0) ≤ ∑i∈V,q i := by
    rw [←sum_filter]
    exact sum_le_sum_of_subset_of_nonneg
      (by intro i hi; exact (mem_filter.mp hi).2) (fun i _ _ => hq i)
  calc
    _ ≤ ∑i∈S, ((if i∈T then g i else 0)+∑j∈J,if i∈U j then l i else 0) :=
      sum_le_sum hpoint
    _ = (∑i∈S,if i∈T then g i else 0)+∑j∈J,∑i∈S,if i∈U j then l i else 0 := by
      rw [sum_add_distrib, sum_comm (s:=S) (t:=J)]
    _ ≤ _ := add_le_add (hind T g hg) (sum_le_sum (fun j _ => hind (U j) l hl))

noncomputable def quotientSourceSmallRowTerm {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (κ a : ℕ→ℂ) (D₁ D₂ d h r : ℕ) : ℝ :=
  ‖a (d*(r*h/D₂))‖*(D₂:ℝ)*((d:ℝ)*(h:ℝ)*((r*h).totient:ℝ)*Real.sqrt (r:ℝ))⁻¹*
    ∑θ∈proposition141SmallPrimitiveFamily χ h r, ‖proposition141Sigma χ θ β κ D₁ d h‖

noncomputable def quotientSourceLargeRowTerm {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (κ a : ℕ→ℂ) (D₁ D₂ d h r : ℕ) : ℝ :=
  ‖a (d*(r*h/D₂))‖*(D₂:ℝ)*((d:ℝ)*(h:ℝ)*((r*h).totient:ℝ)*Real.sqrt (r:ℝ))⁻¹*
    ∑θ∈(univ : Finset (DirichletCharacter ℂ r)).filter (fun θ=>θ.IsPrimitive),
      ‖proposition141Sigma χ θ β κ D₁ d h‖

theorem quotientSource_flat_row_le_small {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (κ a : ℕ→ℂ) (D₁ D₂ d h r : ℕ) :
    (∑θ : DirichletCharacter ℂ r, quotientSourceFlatTerm χ β κ a D₁ D₂ d h r θ) ≤
      quotientSourceSmallRowTerm χ β κ a D₁ D₂ d h r := by
  unfold quotientSourceSmallRowTerm proposition141SmallPrimitiveFamily
  rw [sum_filter, mul_sum]
  apply sum_le_sum
  intro θ hθ
  unfold quotientSourceFlatTerm
  split_ifs with hp hq hq
  · rfl
  · exact False.elim (hq hp.2.2.2)
  · positivity
  · simp

theorem quotientSource_small_row_le_large {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (κ a : ℕ→ℂ) (D₁ D₂ d h r : ℕ) :
    quotientSourceSmallRowTerm χ β κ a D₁ D₂ d h r ≤
      quotientSourceLargeRowTerm χ β κ a D₁ D₂ d h r := by
  unfold quotientSourceSmallRowTerm quotientSourceLargeRowTerm
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact sum_le_sum_of_subset_of_nonneg
    (by intro θ hθ; exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hθ).2.1⟩)
    (fun θ _ _ => norm_nonneg _)

/-- Any nonzero character row witnesses the genuine coefficient and the
exact divisor/coprimality predicates; no support is postulated. -/
theorem quotientSource_flat_row_nonzero_data {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (κ a : ℕ→ℂ) (D₁ D₂ d h r : ℕ)
    (hne : (∑θ : DirichletCharacter ℂ r,
      quotientSourceFlatTerm χ β κ a D₁ D₂ d h r θ)≠0) :
    D₂∣r*h ∧ (r*h/D₂).Coprime D₁ ∧ 1<r ∧ a (d*(r*h/D₂))≠0 := by
  obtain ⟨θ,_,hθ⟩ := exists_ne_zero_of_sum_ne_zero hne
  have ha : a (d*(r*h/D₂))≠0 := by
    intro he
    exact hθ (by simp [quotientSourceFlatTerm,he])
  unfold quotientSourceFlatTerm at hθ
  split_ifs at hθ with hp
  · exact ⟨hp.1,hp.2.1,hp.2.2.1,ha⟩
  · exact False.elim (hθ rfl)

/-- The precise boundary r<D³ / D³≤r is covered by the existing actual
small family and half-open dyadic source families. Both exclusions remain
in the small branch; only a nonnegative upper bound enlarges the large one. -/
theorem quotientSource_actual_conductor_row_le {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (κ a : ℕ→ℂ) (D₁ D₂ d h : ℕ) (hD : 1<D) :
    (∑r∈Icc 1 ⌊lemma23PaperP D⌋₊, ∑θ : DirichletCharacter ℂ r,
      quotientSourceFlatTerm χ β κ a D₁ D₂ d h r θ) ≤
    (∑r∈proposition141SourceSmallModuli D D₁ D₂ d h a,
      quotientSourceSmallRowTerm χ β κ a D₁ D₂ d h r)+
    (∑j∈range (proposition141DyadicBlockCount D),
      proposition141SourceUnlocalizedLargeBlock χ β κ a D₁ D₂ d h (proposition141DyadicScale D j)) := by
  have hb := quotientSource_sum_le_cover (Icc 1 ⌊lemma23PaperP D⌋₊)
    (proposition141SourceSmallModuli D D₁ D₂ d h a)
    (range (proposition141DyadicBlockCount D))
    (fun j => proposition141SourceLargeModuli D₁ D₂ d h (proposition141DyadicScale D j) a)
    (fun r => ∑θ : DirichletCharacter ℂ r, quotientSourceFlatTerm χ β κ a D₁ D₂ d h r θ)
    (quotientSourceSmallRowTerm χ β κ a D₁ D₂ d h)
    (quotientSourceLargeRowTerm χ β κ a D₁ D₂ d h)
    (fun r => by unfold quotientSourceSmallRowTerm; positivity)
    (fun r => by unfold quotientSourceLargeRowTerm; positivity)
    (quotientSource_flat_row_le_small χ β κ a D₁ D₂ d h)
    (fun r => (quotientSource_flat_row_le_small χ β κ a D₁ D₂ d h r).trans
      (quotientSource_small_row_le_large χ β κ a D₁ D₂ d h r)) ?_
  · simpa only [quotientSourceLargeRowTerm,proposition141SourceUnlocalizedLargeBlock,Nat.mul_comm] using hb
  · intro r hr hne
    have hp := quotientSource_flat_row_nonzero_data χ β κ a D₁ D₂ d h r hne
    by_cases hs : r<D^3
    · left
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,hs.le⟩,hp.2.2.1,hs,hp.1,hp.2.1,hp.2.2.2⟩
    · right
      have hlo : (D:ℝ)^(3:ℝ)≤(r:ℝ) := by
        norm_num only [Real.rpow_ofNat]
        exact_mod_cast (show D^3≤r by omega)
      have hup : (r:ℝ)≤lemma23PaperP D :=
        (by exact_mod_cast (mem_Icc.mp hr).2 : (r:ℝ)≤⌊lemma23PaperP D⌋₊).trans
          (Nat.floor_le (Real.exp_pos _).le)
      obtain ⟨j,hj,hjr⟩ := proposition141_dyadic_cover (by omega) hp.2.2.1 hlo hup
      refine ⟨j,hj,mem_filter.mpr ⟨hjr,?_⟩⟩
      simpa only [Nat.mul_comm] using (show D₂∣r*h ∧ (r*h/D₂).Coprime D₁ ∧ a (d*(r*h/D₂))≠0 from ⟨hp.1,hp.2.1,hp.2.2.2⟩)

end ZhangLS.Spec
