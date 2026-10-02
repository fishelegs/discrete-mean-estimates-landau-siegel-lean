import ZhangLS.Spec.Lemma84Section8Cutoffs
import ZhangLS.Spec.Lemma84Repaired

/-! Faithful finite Section 8 sums. The xi factor is changed only in the strict
region where Lemma 8.4 applies. Exact residual boundary terms are retained. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical

/-- Full positive outer support: both mollifiers vanish once dr≥P₁. -/
noncomputable def lemma84Section8Pairs (D : ℕ) : Finset (ℕ×ℕ) :=
  ((Icc 1 ⌊lemma84Section8P1 D⌋₊)×ˢ(Icc 1 ⌊lemma84Section8P1 D⌋₊)).filter
    (fun a => (a.1*a.2:ℕ)<lemma84Section8P1 D)

/-- The actual normalized first inner sum for one mollifier. -/
noncomputable def lemma84Section8First {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (μ n : ℕ) : ℂ :=
  if (n:ℝ)<lemma84Section8Cutoff D μ then
    lemma82ShiftedSum χ c j μ (lemma84Section8Cutoff D μ/n) /
      (Real.log (lemma84Section8Cutoff D μ):ℂ) else 0

/-- The actual normalized ξ inner sum for one mollifier. -/
noncomputable def lemma84Section8Second {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (μ d r : ℕ) : ℂ :=
  if (d*r:ℕ)<lemma84Section8Cutoff D μ then
    lemma84XiSum χ c j μ d r (lemma84Section8Cutoff D μ/(d*r:ℕ)) /
      (Real.log (lemma84Section8Cutoff D μ):ℂ) else 0

/-- The exact Section 8 proposed main term for the ξ factor, with its Π. -/
noncomputable def lemma84Section8SecondMain {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (μ d r : ℕ) : ℂ :=
  if (d*r:ℕ)<lemma84Section8Cutoff D μ then
    LDerivAtOne χ*lemma83Pi χ d r*
      lemma84MainTerm D c j μ (lemma84Section8Cutoff D μ/(d*r:ℕ)) /
      (Real.log (lemma84Section8Cutoff D μ):ℂ) else 0

/-- Replace only on dr<Pμ/T. Boundary values remain exactly the actual sum. -/
noncomputable def lemma84Section8SecondHybrid {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (μ d r : ℕ) : ℂ :=
  if (d*r:ℕ)<lemma84Section8Cutoff D μ/lemma56PaperT D then
    lemma84Section8SecondMain χ c j μ d r else lemma84Section8Second χ c j μ d r

noncomputable def lemma84Section8FirstCombined {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (n : ℕ) : ℂ :=
  lemma84Section8First χ c j 6 n+lemma84Section8Iota*lemma84Section8First χ c j 7 n

/-- Finite Section 8 S_j in its actual normalized-smoothing form. -/
noncomputable def lemma84Section8Raw {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) : ℂ :=
  ∑ a∈lemma84Section8Pairs D, lemma84Section8Weight χ c j a.1 a.2*
    lemma84Section8FirstCombined χ c j (a.1*a.2)*
    (lemma84Section8Second χ c j 6 a.1 a.2+
      star lemma84Section8Iota*lemma84Section8Second χ c j 7 a.1 a.2)

noncomputable def lemma84Section8Hybrid {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) : ℂ :=
  ∑ a∈lemma84Section8Pairs D, lemma84Section8Weight χ c j a.1 a.2*
    lemma84Section8FirstCombined χ c j (a.1*a.2)*
    (lemma84Section8SecondHybrid χ c j 6 a.1 a.2+
      star lemma84Section8Iota*lemma84Section8SecondHybrid χ c j 7 a.1 a.2)

/-- Full ξ replacement, still retaining the actual first inner sum. -/
noncomputable def lemma84Section8FullSecondMain {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) : ℂ :=
  ∑ a∈lemma84Section8Pairs D, lemma84Section8Weight χ c j a.1 a.2*
    lemma84Section8FirstCombined χ c j (a.1*a.2)*
    (lemma84Section8SecondMain χ c j 6 a.1 a.2+
      star lemma84Section8Iota*lemma84Section8SecondMain χ c j 7 a.1 a.2)

/-- Exact outstanding boundary correction. Its two supports are Pμ/T≤dr<Pμ,
including equality at Pμ/T; the strict endpoint at Pμ contributes zero. -/
noncomputable def lemma84Section8Boundary {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) : ℂ :=
  lemma84Section8Hybrid χ c j-lemma84Section8FullSecondMain χ c j

/-- The separation of the repaired interior contribution from the still-needed
boundary estimate is an exact identity, not an asymptotic assumption. -/
theorem lemma84_section8_exact_error_split {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) :
    lemma84Section8Raw χ c j-lemma84Section8FullSecondMain χ c j=
      (lemma84Section8Raw χ c j-lemma84Section8Hybrid χ c j)+
        lemma84Section8Boundary χ c j := by
  unfold lemma84Section8Boundary
  ring

/-- The finite box introduces no extra restriction on positive dr<P₁. -/
theorem lemma84_section8_pairs_exact (D d r : ℕ) :
    (d,r)∈lemma84Section8Pairs D ↔ 0<d ∧ 0<r ∧ ((d*r:ℕ):ℝ)<lemma84Section8P1 D := by
  have hQ : 0≤lemma84Section8P1 D := (Real.rpow_pos_of_pos (Real.exp_pos _) _).le
  constructor
  · intro h
    obtain ⟨hbox,hcut⟩ := mem_filter.mp h
    have hm := mem_product.mp hbox
    exact ⟨(mem_Icc.mp hm.1).1,(mem_Icc.mp hm.2).1,hcut⟩
  · rintro ⟨hd,hr,hcut⟩
    apply mem_filter.mpr
    refine ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨hd,?_⟩,mem_Icc.mpr ⟨hr,?_⟩⟩,hcut⟩
    · apply (Nat.le_floor_iff hQ).mpr
      have hh : d≤d*r := Nat.le_mul_of_pos_right d hr
      exact (by exact_mod_cast hh : (d:ℝ)≤((d*r:ℕ):ℝ)).trans hcut.le
    · apply (Nat.le_floor_iff hQ).mpr
      have hh : r≤d*r := Nat.le_mul_of_pos_left r hd
      exact (by exact_mod_cast hh : (r:ℝ)≤((d*r:ℕ):ℝ)).trans hcut.le

lemma lemma84_section8_first_zero_at_cutoff {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (μ n : ℕ) (h : lemma84Section8Cutoff D μ≤n) :
    lemma84Section8First χ c j μ n=0 := by
  simp only [lemma84Section8First,if_neg (not_lt_of_ge h)]

lemma lemma84_section8_second_zero_at_cutoff {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (μ d r : ℕ) (h : lemma84Section8Cutoff D μ≤(d*r:ℕ)) :
    lemma84Section8Second χ c j μ d r=0 := by
  simp only [lemma84Section8Second,if_neg (not_lt_of_ge h)]

lemma lemma84_section8_hybrid_boundary_endpoint {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (μ d r : ℕ)
    (h : ((d*r:ℕ):ℝ)=lemma84Section8Cutoff D μ/lemma56PaperT D) :
    lemma84Section8SecondHybrid χ c j μ d r=lemma84Section8Second χ c j μ d r := by
  have hh : ¬((d*r:ℕ):ℝ)<lemma84Section8Cutoff D μ/lemma56PaperT D := by rw [h]; exact lt_irrefl _
  simp only [lemma84Section8SecondHybrid,if_neg hh]

end ZhangLS.Spec
