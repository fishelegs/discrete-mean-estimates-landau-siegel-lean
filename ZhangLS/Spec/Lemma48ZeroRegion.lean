import ZhangLS.Spec.Lemma47Reflection

/-! # Actual product zeros in the original region Ω

The inverse-factor estimate in Lemma 4.8 only needs the thin closed slab
`|Re ρ - 1/2| ≤ α²`. This follows from Lemma 4.5 and the genuine reflected
product functional equation, without assuming critical-line location.
-/

namespace ZhangLS.Spec

open Complex ComplexConjugate Metric Set

set_option maxHeartbeats 1000000

/-- The original region (2.7), including its full left half. -/
def Lemma48InOmega (D : ℕ) (s : ℂ) : Prop :=
  |s.re - 1 / 2| < 1 / 2 ∧
    |s.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 2

/-- The actual product appearing in the statement of Lemma 4.8. -/
noncomputable def lemma48ActualProduct {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ) : ℂ :=
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  DirichletCharacter.LFunction ψ s *
    DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) s

theorem lemma48_omega_height_pos {D : ℕ} {s : ℂ}
    (hL : 3 ≤ lemma23PaperL D) (hs : Lemma48InOmega D s) : 0 < s.im := by
  apply (lemma44_extended_gamma_region_height hL ?_).2.2.1
  exact ⟨by linarith [hs.1], by
    linarith [hs.2, pow_nonneg (by linarith : 0 ≤ lemma23PaperL D) 405]⟩

/-- Reflection preserves the original Ω exactly. -/
theorem lemma48_omega_reflection {D : ℕ} {s : ℂ} (hs : Lemma48InOmega D s) :
    Lemma48InOmega D (1 - conj s) := by
  simp only [Lemma48InOmega, sub_re, one_re, conj_re, sub_im, one_im,
    conj_im, zero_sub, neg_neg]
  have he : 1 - s.re - 1 / 2 = -(s.re - 1 / 2) := by ring
  rw [he, abs_neg]
  exact hs

/-- The product's reflected zero follows directly from the actual
functional equation and conjugation; no inverse-character good set is used. -/
theorem lemma48_actual_product_reflected_zero {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hL : 3 ≤ lemma23PaperL D) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (him : 0 < s.im) (hzero : lemma48ActualProduct χ ψ s = 0) :
    lemma48ActualProduct χ ψ (1 - conj s) = 0 := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  have hψne : ψ ≠ 1 := by
    intro he
    have hh := hψ.2.1
    rw [he, DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_one] at hh
    exact hψ.1.ne_one hh.symm
  have htwist := lemma44CharacterTwist_isPrimitive χ ψ hψ.2.1
    (lemma44_family_coprime χ ψ hL hψ)
  have htwne : lemma44CharacterTwist χ ψ ≠ 1 := by
    intro he
    rw [he, DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_one] at htwist
    exact hψ.1.ne_one (Nat.dvd_one.mp (htwist ▸ Nat.dvd_mul_left p D))
  have hfe := lemma44_equation44 χ ψ hL hψ him
  change DirichletCharacter.LFunction ψ s *
    DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) s = 0 at hzero
  rw [hzero] at hfe
  have hbar := (mul_eq_zero.mp hfe.symm).resolve_left
    (lemma44ActualZtilde_ne_zero χ ψ hL hψ him)
  rw [dirichletLFunction_inv_eq_conj_at_conj ψ hψne,
    dirichletLFunction_inv_eq_conj_at_conj (lemma44CharacterTwist χ ψ) htwne,
    ← map_mul, map_sub, map_one] at hbar
  exact (map_eq_zero conj).mp hbar

/-- Both sides of Ω are reduced to the closed thin slab. Endpoints
`1/2 ± α²` are retained, so no strict-boundary case is silently omitted. -/
theorem lemma48_actual_zero_in_thin_slab {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    {s : ℂ} (hs : Lemma48InOmega D s) (hzero : lemma48ActualProduct χ ψ s = 0) :
    |s.re - 1 / 2| ≤ lemma44PaperAlpha D ^ 2 := by
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have hbounds (z : ℂ) (hz : Lemma48InOmega D z)
      (hzzero : lemma48ActualProduct χ ψ z = 0) :
      z.re ≤ 1 / 2 + lemma44PaperAlpha D ^ 2 := by
    by_contra h
    have hr : Lemma45InRegion D z :=
      ⟨lt_of_not_ge h, by linarith [(abs_lt.mp hz.1).2], hz.2⟩
    exact lemma45_actual_product_ne_zero χ ψ hD hψ hr hzzero
  have hu := hbounds s hs hzero
  have hr := lemma48_omega_reflection hs
  have hz := lemma48_actual_product_reflected_zero χ ψ hL hψ.1
    (lemma48_omega_height_pos hL hs) hzero
  have hl := hbounds (1 - conj s) hr hz
  simp only [sub_re, one_re, conj_re] at hl
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Every zero in Ω lies in the domains of Lemmas 4.1, 4.2 and 4.4,
as does its reflected point. -/
theorem lemma48_thin_slab_regions {D : ℕ} {s : ℂ}
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hs : Lemma48InOmega D s)
    (hslab : |s.re - 1 / 2| ≤ lemma44PaperAlpha D ^ 2) :
    Lemma44InOmega3 D s ∧ Lemma23InOmega1 D s ∧
      Lemma44InOmega3 D (1 - conj s) := by
  have ha := lemma46_alpha_parameters hD
  have hp := lemma23_sectionFour_parameters_at_explicit_threshold hD
  have hsre : |s.re - 1 / 2| < lemma44PaperAlpha D := by
    apply hslab.trans_lt
    nlinarith only [ha.1, ha.2.1]
  have hre := abs_lt.mp hsre
  have hs3 : Lemma44InOmega3 D s :=
    ⟨by linarith, by linarith, by linarith [hs.2]⟩
  have hr3 : Lemma44InOmega3 D (1 - conj s) := by
    simp only [Lemma44InOmega3, sub_re, one_re, conj_re, sub_im,
      one_im, conj_im, zero_sub, neg_neg]
    exact ⟨by linarith, by linarith, by linarith [hs.2]⟩
  have hs2 : Lemma23InOmega2 D s :=
    ⟨by linarith [ha.2.2.1], by linarith [ha.2.2.1], by linarith [hs.2]⟩
  have hR : 0 < lemma23LogDerivativeRadius D := by
    unfold lemma23LogDerivativeRadius
    exact div_pos (by linarith only [hp.2]) (by linarith only [hp.1])
  exact ⟨hs3, lemma23_omega2_disk_subset_omega1 hp.1 hp.2 hs2
    (mem_ball_self hR), hr3⟩

/-- An absolute bound for the actual inverse factor at every original
product zero. The threshold remains the explicit Section 4 threshold. -/
theorem lemma48_actual_Z_inv_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    {s : ℂ} (hs : Lemma48InOmega D s) (hzero : lemma48ActualProduct χ ψ s = 0) :
    ‖(lemma44ActualZtilde χ ψ s)⁻¹‖ ≤ Real.exp 3 := by
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have hslab := lemma48_actual_zero_in_thin_slab χ ψ hD hψ hs hzero
  have hr := lemma48_thin_slab_regions hD hs hslab
  have him := lemma48_omega_height_pos hL hs
  have hreflection := lemma47_actual_Z_reflection χ ψ hL hψ.1 him.ne'
  have he : (lemma44ActualZtilde χ ψ s)⁻¹ =
      conj (lemma44ActualZtilde χ ψ (1 - conj s)) := by
    have hn := lemma44ActualZtilde_ne_zero χ ψ hL hψ.1 him
    apply (mul_left_cancel₀ hn)
    simpa only [mul_inv_cancel₀ hn] using hreflection.symm
  rw [he, norm_conj]
  have hb := lemma44ActualZtilde_norm_on_omega3 χ ψ hD hψ.1 hr.2.2
  apply hb.trans
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  simp only [sub_re, one_re, conj_re]
  have ha := lemma46_alpha_parameters hD
  have hM : 0 < Real.log (lemma23PaperP D) := by
    simp only [lemma23PaperP, Real.log_exp]
    positivity
  have haM : lemma44PaperAlpha D * Real.log (lemma23PaperP D) = Real.pi := by
    unfold lemma44PaperAlpha
    exact div_mul_cancel₀ _ hM.ne'
  have hm := mul_le_mul_of_nonneg_right (abs_le.mp hslab).2 hM.le
  have ha2M : lemma44PaperAlpha D ^ 2 * Real.log (lemma23PaperP D) =
      lemma44PaperAlpha D * Real.pi := by rw [← haM]; ring
  rw [ha2M] at hm
  nlinarith only [hm, ha.1, ha.2.1, Real.pi_le_four]

end ZhangLS.Spec
