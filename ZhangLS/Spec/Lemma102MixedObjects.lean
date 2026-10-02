import ZhangLS.Spec.Lemma102Boundary
import ZhangLS.Spec.Lemma84BoundaryLittleO
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

/-- The source's three polynomial main terms, retaining knot endpoints in
one of the adjacent pieces. Endpoint choices are covered by the boundary budget. -/
noncomputable def lemma102FullMain {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (d r : ℕ) : ℂ :=
  if (d*r:ℝ)≤lemma23PaperP D^(1/2:ℝ) then lemma102MainInitial χ c j d r
  else if (d*r:ℝ)≤lemma23PaperP D^(251/500:ℝ) then lemma102MainLower χ c j d r
  else lemma102MainUpper χ c j d r

/-- Actual Section 10 S_j(a11,a13), in the exact normalized first-factor
notation whose equality to the κ₁+ι₂κ₂ sum is already proved. -/
noncomputable def lemma102MixedRaw {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) : ℂ :=
  ∑ a∈lemma84Section8Pairs D, lemma84Section8Weight χ c j a.1 a.2*
    lemma84Section8FirstCombined χ c j (a.1*a.2)*lemma102Sum χ c j a.1 a.2

noncomputable def lemma102MixedMain {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) : ℂ :=
  ∑ a∈lemma84Section8Pairs D, lemma84Section8Weight χ c j a.1 a.2*
    lemma84Section8FirstCombined χ c j (a.1*a.2)*lemma102FullMain χ c j a.1 a.2

noncomputable def lemma102MixedHybrid {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) : ℂ :=
  ∑ a∈lemma84Section8Pairs D, lemma84Section8Weight χ c j a.1 a.2*
    lemma84Section8FirstCombined χ c j (a.1*a.2)*
      (if Lemma101Transition D (a.1*a.2:ℝ) then lemma102Sum χ c j a.1 a.2
        else lemma102FullMain χ c j a.1 a.2)

/-- Literal κ/ξ/tent expansion of the actual mixed sum. -/
lemma lemma102_mixed_source_exact {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (c : ℝ) (j : Fin 3)
    (hQ6 : 1< lemma84Section8Cutoff D 6) (hQ7 : 1< lemma84Section8Cutoff D 7) :
    lemma102MixedRaw χ c j = ∑ a∈lemma84Section8Pairs D,
      lemma84Section8Weight χ c j a.1 a.2*
        (lemma84Section8FirstSource χ c j 6 (a.1*a.2)+
          lemma84Section8Iota*lemma84Section8FirstSource χ c j 7 (a.1*a.2))*
        (∑' n : ℕ, χ.evalNat n*lemma83Xi (lemma83PaperBeta D c) j n a.1 a.2/(n:ℂ)*
          (lemma111Tent (Real.log ((a.1*a.2:ℝ)*(n:ℝ))/Real.log (lemma23PaperP D)):ℂ)) := by
  unfold lemma102MixedRaw
  apply sum_congr rfl
  intro a ha
  obtain ⟨hd,hr,_⟩ := (lemma84_section8_pairs_exact D a.1 a.2).mp ha
  rw [lemma84Section8FirstCombined,lemma84_section8_first_source_exact χ c j 6 _ (Nat.mul_pos hd hr) hQ6,
    lemma84_section8_first_source_exact χ c j 7 _ (Nat.mul_pos hd hr) hQ7,
    lemma102_sum_eq_tsum χ hD c j a.1 a.2 hd hr]

end ZhangLS.Spec
