import ZhangLS.Spec.Proposition26GaussianProfiles

/-! Exact source identities attaching original Section 11 series to A-polynomials. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ZhangLS.Spec
open Finset Complex
open scoped BigOperators Classical

lemma proposition26_mem_polynomial_indices (D n : ℕ) :
    n ∈ lemma81PolynomialIndices D ↔ 0 < n ∧ (n:ℝ) < lemma81Cutoff D := by
  simp only [lemma81PolynomialIndices, mem_filter, mem_Icc]
  constructor
  · exact fun h => ⟨h.1.1, h.2⟩
  · rintro ⟨hn,hx⟩
    refine ⟨⟨hn,?_⟩,hx⟩
    exact_mod_cast hx.le.trans (Nat.le_ceil (lemma81Cutoff D))

lemma proposition26_strict_ceil_eq {X : ℝ} (hX : 0 ≤ X) :
    (Icc 1 ⌈X⌉₊).filter (fun n : ℕ => (n:ℝ) < X) = lemma82StrictCutoff X := by
  ext n
  rw [lemma82_mem_strictCutoff hX n]
  simp only [mem_filter, mem_Icc]
  constructor
  · exact fun h => ⟨h.1.1,h.2⟩
  · rintro ⟨hn,hx⟩
    refine ⟨⟨hn,?_⟩,hx⟩
    exact_mod_cast hx.le.trans (Nat.le_ceil X)

lemma proposition26_twisted_polynomial_term {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (v : ℝ) (w : ℕ → ℂ) (s : ℂ) {n : ℕ} (hn : 0 < n) :
    proposition26TwistedCoefficient χ v w n * ψ (n:ZMod p) / (n:ℂ)^s =
      LSeries.term (lemma112Coefficient χ ψ) (s+I*(v:ℂ)) n * w n := by
  have hn0 := hn.ne'
  have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn0
  have hp : (n:ℂ)^(-I*(v:ℂ)) / (n:ℂ)^s = ((n:ℂ)^(s+I*(v:ℂ)))⁻¹ := by
    rw [← Complex.cpow_sub _ _ hnC, ← Complex.cpow_neg]
    congr 1
    ring
  rw [proposition26TwistedCoefficient, if_neg hn0, LSeries.term_of_ne_zero hn0,
    lemma112Coefficient]
  calc
    _ = χ.evalNat n * ψ (n:ZMod p) * w n * ((n:ℂ)^(-I*(v:ℂ)) / (n:ℂ)^s) := by ring
    _ = _ := by rw [hp]; ring

lemma proposition26_twisted_polynomial_strict_sum {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (v : ℝ) (w : ℕ → ℂ) (s : ℂ) {X : ℝ} (hX : 0 ≤ X)
    (hcut : X ≤ lemma81Cutoff D) :
    lemma81Polynomial D
      (proposition26TwistedCoefficient χ v (fun n => if (n:ℝ) < X then w n else 0)) ψ s =
      ∑ n ∈ lemma82StrictCutoff X,
        LSeries.term (lemma112Coefficient χ ψ) (s+I*(v:ℂ)) n * w n := by
  have hsub : lemma82StrictCutoff X ⊆ lemma81PolynomialIndices D := by
    intro n hn
    have hm := (lemma82_mem_strictCutoff hX n).mp hn
    exact (proposition26_mem_polynomial_indices D n).mpr ⟨hm.1,hm.2.trans_le hcut⟩
  have hsum : (∑ n ∈ lemma82StrictCutoff X,
      proposition26TwistedCoefficient χ v (fun n => if (n:ℝ) < X then w n else 0) n *
        ψ (n:ZMod p) / (n:ℂ)^s) =
      lemma81Polynomial D
        (proposition26TwistedCoefficient χ v (fun n => if (n:ℝ) < X then w n else 0)) ψ s := by
    unfold lemma81Polynomial
    apply sum_subset hsub
    intro n hn hnot
    have hm := (proposition26_mem_polynomial_indices D n).mp hn
    have hx : ¬(n:ℝ) < X := fun hx => hnot ((lemma82_mem_strictCutoff hX n).mpr ⟨hm.1,hx⟩)
    simp [proposition26TwistedCoefficient, hx]
  rw [← hsum]
  apply sum_congr rfl
  intro n hn
  have hm := (lemma82_mem_strictCutoff hX n).mp hn
  rw [proposition26_twisted_polynomial_term χ ψ v _ s hm.1, if_pos hm.2]

lemma proposition26_short_polynomial_strict_terms {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ) :
    lemma112ShortPolynomial χ ψ s =
      ∑ n ∈ lemma82StrictCutoff (lemma112PaperP1 D),
        LSeries.term (lemma112Coefficient χ ψ) s n := by
  have hP1 : 0 ≤ lemma112PaperP1 D := Real.rpow_nonneg (Real.exp_nonneg _) _
  rw [lemma112ShortPolynomial, proposition26_strict_ceil_eq hP1]
  apply sum_congr rfl
  intro n hn
  have hm := (lemma82_mem_strictCutoff hP1 n).mp hn
  exact (lemma44_LSeries_term_eq_exp _ _ hm.1.ne').symm

lemma proposition26_short_polynomial_eq_twisted {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hcut : lemma112PaperP1 D ≤ lemma81Cutoff D) (s : ℂ) (v : ℝ) :
    lemma112ShortPolynomial χ ψ (s+I*(v:ℂ)) =
      lemma81Polynomial D (proposition26TwistedCoefficient χ v
        (fun n => if (n:ℝ) < lemma112PaperP1 D then 1 else 0)) ψ s := by
  rw [proposition26_short_polynomial_strict_terms]
  symm
  simpa only [mul_one] using proposition26_twisted_polynomial_strict_sum χ ψ v
    (fun _ => 1) s (Real.rpow_nonneg (Real.exp_nonneg _) _) hcut


lemma proposition26_original_tent_two_coordinate {D : ℕ} (hD : 1 < D)
    {y : ℝ} (hy : 0 < y) :
    lemma111Tent (Real.log y / Real.log (lemma23PaperP D) + 1/250 - proposition26TildeAlpha D) =
      lemma111Tent (Real.log (y / lemma111ShiftScale D) / Real.log (lemma23PaperP D) + 1/250) := by
  have h := lemma111_tent_error_two_original_coordinate hD hy
  unfold lemma111TentErrorTwo at h
  unfold proposition26TildeAlpha lemma51PaperT0
  linarith only [h]

lemma proposition26_J1_eq_gaussian_cutoff {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : 1 < D) (hL : 64 ≤ lemma23PaperL D) (s : ℂ) :
    proposition26J1 χ ψ s =
      ∑ n ∈ lemma82StrictCutoff (proposition26GaussianCutoff D),
        LSeries.term (lemma112Coefficient χ ψ) s n *
          (lemma111Tent (Real.log n / Real.log (lemma23PaperP D)) : ℂ) := by
  unfold proposition26J1
  apply tsum_eq_sum
  intro n hn
  by_cases hn0 : n = 0
  · simp [hn0]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  have hX : 0 ≤ proposition26GaussianCutoff D := Real.rpow_nonneg (Real.exp_nonneg _) _
  have hcut : proposition26GaussianCutoff D ≤ (n:ℝ) :=
    le_of_not_gt (fun h => hn ((lemma82_mem_strictCutoff hX n).mpr ⟨hnpos,h⟩))
  rw [lemma111_tent_one_zero_of_cutoff hD
    ((lemma111_twice_P1_le_transfer_cutoff hL).trans hcut)]
  simp

lemma proposition26_J2_eq_gaussian_cutoff {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : 1 < D) (hL : 64 ≤ lemma23PaperL D) (s : ℂ) :
    proposition26J2 χ ψ s =
      ∑ n ∈ lemma82StrictCutoff (proposition26GaussianCutoff D),
        LSeries.term (lemma112Coefficient χ ψ) s n *
          (lemma111Tent (Real.log n / Real.log (lemma23PaperP D) + 1/250 -
            proposition26TildeAlpha D) : ℂ) := by
  unfold proposition26J2
  apply tsum_eq_sum
  intro n hn
  by_cases hn0 : n = 0
  · simp [hn0]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  have hnR : (0:ℝ) < n := by exact_mod_cast hnpos
  have hX : 0 ≤ proposition26GaussianCutoff D := Real.rpow_nonneg (Real.exp_nonneg _) _
  have hcut : proposition26GaussianCutoff D ≤ (n:ℝ) :=
    le_of_not_gt (fun h => hn ((lemma82_mem_strictCutoff hX n).mpr ⟨hnpos,h⟩))
  rw [proposition26_original_tent_two_coordinate hD hnR,
    lemma111_tent_two_zero_of_cutoff hD hL
      ((lemma111_twice_P1_le_transfer_cutoff hL).trans hcut)]
  simp

lemma proposition26_normalized_gaussian_polynomial {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hL : 64 ≤ lemma23PaperL D) (s : ℂ) (e : ℝ → ℝ) :
    lemma81Polynomial D
      (proposition26TwistedCoefficient χ 0 (proposition26NormalizedGaussianProfile D e)) ψ s =
      (lemma111Scale D : ℂ) *
        ∑ n ∈ lemma82StrictCutoff (proposition26GaussianCutoff D),
          LSeries.term (lemma112Coefficient χ ψ) s n * (e n : ℂ) := by
  have he : proposition26NormalizedGaussianProfile D e = fun n : ℕ =>
      if (n:ℝ) < proposition26GaussianCutoff D then (lemma111Scale D : ℂ) * (e n : ℂ) else 0 := by
    funext n
    by_cases hn : (n:ℝ) < proposition26GaussianCutoff D <;>
      simp [proposition26NormalizedGaussianProfile, hn]
  have hX : 0 ≤ proposition26GaussianCutoff D := Real.rpow_nonneg (Real.exp_nonneg _) _
  have hcut : proposition26GaussianCutoff D ≤ lemma81Cutoff D :=
    proposition26_P505_le_polynomial_cutoff hL
  rw [he, proposition26_twisted_polynomial_strict_sum χ ψ 0
    (fun n : ℕ => (lemma111Scale D : ℂ) * (e n : ℂ)) s hX hcut]
  simp only [Complex.ofReal_zero, mul_zero, add_zero]
  rw [mul_sum]
  apply sum_congr rfl
  intro n hn
  ring

lemma proposition26_error_one_finite_sum {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : 1 < D) (hL : 64 ≤ lemma23PaperL D) (s : ℂ) :
    (∑ n ∈ lemma82StrictCutoff (proposition26GaussianCutoff D),
      LSeries.term (lemma112Coefficient χ ψ) s n * (lemma111TentErrorOne D n : ℂ)) =
      proposition26J1 χ ψ s -
        ∑ n ∈ lemma82StrictCutoff (proposition26GaussianCutoff D),
          LSeries.term (lemma112Coefficient χ ψ) s n * (lemma111SmoothedOne D n : ℂ) := by
  rw [proposition26_J1_eq_gaussian_cutoff χ ψ hD hL s, ← sum_sub_distrib]
  apply sum_congr rfl
  intro n hn
  simp only [lemma111TentErrorOne, Complex.ofReal_sub, mul_sub]

lemma proposition26_error_two_finite_sum {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : 1 < D) (hL : 64 ≤ lemma23PaperL D) (s : ℂ) :
    (∑ n ∈ lemma82StrictCutoff (proposition26GaussianCutoff D),
      LSeries.term (lemma112Coefficient χ ψ) s n * (lemma111TentErrorTwo D n : ℂ)) =
      proposition26J2 χ ψ s -
        ∑ n ∈ lemma82StrictCutoff (proposition26GaussianCutoff D),
          LSeries.term (lemma112Coefficient χ ψ) s n * (lemma111SmoothedTwo D n : ℂ) := by
  rw [proposition26_J2_eq_gaussian_cutoff χ ψ hD hL s, ← sum_sub_distrib]
  apply sum_congr rfl
  intro n hn
  have hX : 0 ≤ proposition26GaussianCutoff D := Real.rpow_nonneg (Real.exp_nonneg _) _
  have hnpos := ((lemma82_mem_strictCutoff hX n).mp hn).1
  have hnR : (0:ℝ) < n := by exact_mod_cast hnpos
  rw [lemma111_tent_error_two_original_coordinate hD hnR]
  simp only [proposition26TildeAlpha, lemma51PaperT0, Complex.ofReal_sub, mul_sub]

noncomputable def proposition26GaussianTailOne {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ) : ℂ :=
  (∑ n ∈ lemma82StrictCutoff (proposition26GaussianCutoff D),
    LSeries.term (lemma112Coefficient χ ψ) s n * (lemma111SmoothedOne D n : ℂ)) -
      lemma112JtildeOne χ ψ s

noncomputable def proposition26GaussianTailTwo {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ) : ℂ :=
  (∑ n ∈ lemma82StrictCutoff (proposition26GaussianCutoff D),
    LSeries.term (lemma112Coefficient χ ψ) s n * (lemma111SmoothedTwo D n : ℂ)) -
      lemma112JtildeTwo χ ψ s

lemma proposition26_inverse_gaussian_scale {D : ℕ} (hD : 1 < D) :
    ((lemma23PaperL D ^ (-24:ℤ) : ℝ) : ℂ) * (lemma111Scale D : ℂ) = 1 := by
  have hA := (lemma111_scale_pos hD).ne'
  have hr : lemma23PaperL D ^ (-24:ℤ) * lemma111Scale D = 1 := by
    rw [lemma111Scale, zpow_neg, zpow_ofNat]
    exact inv_mul_cancel₀ hA
  exact_mod_cast hr

/-- The literal original J₁ defect, with the normalized finite coefficient
sequence and an actual finite-minus-full Gaussian remainder. -/
lemma proposition26_J1_sub_Jtilde_polynomial {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : 1 < D) (hL : 64 ≤ lemma23PaperL D) (s : ℂ) :
    proposition26J1 χ ψ s - lemma112JtildeOne χ ψ s =
      ((lemma23PaperL D ^ (-24:ℤ) : ℝ) : ℂ) *
        lemma81Polynomial D (proposition26TwistedCoefficient χ 0 (proposition26ErrorProfileOne D)) ψ s +
          proposition26GaussianTailOne χ ψ s := by
  rw [proposition26ErrorProfileOne, proposition26_normalized_gaussian_polynomial χ ψ hL,
    proposition26_error_one_finite_sum χ ψ hD hL]
  rw [← mul_assoc, proposition26_inverse_gaussian_scale hD, one_mul]
  unfold proposition26GaussianTailOne
  ring

/-- The second exact defect retains the original shifted J₂ coordinate. -/
lemma proposition26_J2_sub_Jtilde_polynomial {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : 1 < D) (hL : 64 ≤ lemma23PaperL D) (s : ℂ) :
    proposition26J2 χ ψ s - lemma112JtildeTwo χ ψ s =
      ((lemma23PaperL D ^ (-24:ℤ) : ℝ) : ℂ) *
        lemma81Polynomial D (proposition26TwistedCoefficient χ 0 (proposition26ErrorProfileTwo D)) ψ s +
          proposition26GaussianTailTwo χ ψ s := by
  rw [proposition26ErrorProfileTwo, proposition26_normalized_gaussian_polynomial χ ψ hL,
    proposition26_error_two_finite_sum χ ψ hD hL]
  rw [← mul_assoc, proposition26_inverse_gaussian_scale hD, one_mul]
  unfold proposition26GaussianTailTwo
  ring

lemma proposition26_gaussian_tail_one_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : 1 < D) (hL : 64 ≤ lemma23PaperL D) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖proposition26GaussianTailOne χ ψ s‖ ≤
      2 * lemma44InverseSquareMass * Real.exp (-(lemma23PaperL D ^ 10)) := by
  unfold proposition26GaussianTailOne
  rw [norm_sub_rev]
  exact lemma111_smoothed_one_P505_tail χ ψ hD hL hs

lemma proposition26_gaussian_tail_two_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : 1 < D) (hL : 64 ≤ lemma23PaperL D) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖proposition26GaussianTailTwo χ ψ s‖ ≤
      2 * lemma44InverseSquareMass * Real.exp (-(lemma23PaperL D ^ 10)) := by
  unfold proposition26GaussianTailTwo
  rw [norm_sub_rev]
  exact lemma111_smoothed_two_P505_tail χ ψ hD hL hs

end ZhangLS.Spec
