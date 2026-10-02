import ZhangLS.Spec.Lemma171GaussianMellin
import ZhangLS.Spec.Lemma32NormalizedFiniteShift

/-! # Lemma 17.1: actual cubic principal part and finite rectangle residue -/

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Metric Set Filter
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def lemma171DividedRemainder {D : ℕ} (χ : RealPrimitiveCharacter D) : ℕ → ℂ → ℂ
  | 0 => lemma171RegularNumerator χ
  | n+1 => dslope (lemma171DividedRemainder χ n) 0

lemma lemma171_divided_remainder_differentiableOn {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (n : ℕ) :
    DifferentiableOn ℂ (lemma171DividedRemainder χ n) {w : ℂ | -1/2 < w.re} := by
  induction n with
  | zero => exact (lemma171_regular_numerator_analyticOnNhd χ hD).differentiableOn
  | succ n ih =>
    change DifferentiableOn ℂ (dslope (lemma171DividedRemainder χ n) 0) _
    exact (Complex.differentiableOn_dslope
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num))).mpr ih

lemma lemma171_divided_remainder_analyticOnNhd {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (n : ℕ) :
    AnalyticOnNhd ℂ (lemma171DividedRemainder χ n) {w : ℂ | -1/2 < w.re} :=
  (lemma171_divided_remainder_differentiableOn χ hD n).analyticOnNhd
    (isOpen_lt continuous_const Complex.continuous_re)

lemma lemma171_divided_remainder_recurrence {D : ℕ} (χ : RealPrimitiveCharacter D)
    (n : ℕ) (w : ℂ) :
    lemma171DividedRemainder χ n w = lemma171DividedRemainder χ n 0+
      w*lemma171DividedRemainder χ (n+1) w := by
  have hs := sub_smul_dslope (lemma171DividedRemainder χ n) 0 w
  simp only [sub_zero,smul_eq_mul] at hs
  change lemma171DividedRemainder χ n w = lemma171DividedRemainder χ n 0+
    w*dslope (lemma171DividedRemainder χ n) 0 w
  linear_combination -hs

lemma lemma171_regular_numerator_finite_expansion {D : ℕ} (χ : RealPrimitiveCharacter D)
    (n : ℕ) (w : ℂ) :
    lemma171RegularNumerator χ w =
      (∑ k ∈ Finset.range n, lemma171DividedRemainder χ k 0*w^k)+
        w^n*lemma171DividedRemainder χ n w := by
  induction n with
  | zero => simp [lemma171DividedRemainder]
  | succ n ih =>
    calc
      _ = (∑ k ∈ Finset.range n, lemma171DividedRemainder χ k 0*w^k)+
        w^n*lemma171DividedRemainder χ n w := ih
      _ = (∑ k ∈ Finset.range n, lemma171DividedRemainder χ k 0*w^k)+
        lemma171DividedRemainder χ n 0*w^n+w^(n+1)*lemma171DividedRemainder χ (n+1) w := by
          rw [lemma171_divided_remainder_recurrence χ n w,pow_succ]
          ring
      _ = _ := by rw [Finset.sum_range_succ]

noncomputable def lemma171PrincipalPart {D : ℕ} (χ : RealPrimitiveCharacter D) (w : ℂ) : ℂ :=
  ∑ k ∈ Finset.range 3, lemma171DividedRemainder χ k 0*w^k/w^3

lemma lemma171_actual_integrand_principal_decomposition {D : ℕ} (χ : RealPrimitiveCharacter D)
    (w : ℂ) (hw : -1/2 < w.re) (h0 : w ≠ 0) :
    lemma171MellinIntegrand χ w = lemma171PrincipalPart χ w+lemma171DividedRemainder χ 3 w := by
  have h := lemma171_regular_numerator_finite_expansion χ 3 w
  rw [lemma171_regular_numerator_eq χ w hw h0] at h
  unfold lemma171PrincipalPart
  rw [← Finset.sum_div]
  apply (mul_left_cancel₀ (pow_ne_zero 3 h0))
  field_simp
  linear_combination h

lemma lemma171_actual_regular_remainder_rectangle_zero {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (a b T : ℝ) (ha : -1/2 < a) (hab : a ≤ b) (hT : 0 ≤ T) :
    lemma44GeneralRectangleBoundaryIntegral (lemma171DividedRemainder χ 3) a b T = 0 := by
  apply lemma44_local_rectangle_cauchy _ hab hT
  apply (lemma171_divided_remainder_differentiableOn χ hD 3).mono
  intro w hw
  exact lt_of_lt_of_le ha hw.1.1


lemma lemma171_divided_remainder_power_series {D : ℕ} (χ : RealPrimitiveCharacter D)
    (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (hp : HasFPowerSeriesAt (lemma171RegularNumerator χ) p 0) (n : ℕ) :
    HasFPowerSeriesAt (lemma171DividedRemainder χ n) (FormalMultilinearSeries.fslope^[n] p) 0 := by
  induction n with
  | zero => exact hp
  | succ n ih =>
    simpa only [lemma171DividedRemainder,Function.iterate_succ_apply'] using
      ih.has_fpower_series_dslope_fslope

lemma lemma171_divided_remainder_coefficient {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (n : ℕ) :
    lemma171DividedRemainder χ n 0 =
      iteratedDeriv n (lemma171RegularNumerator χ) 0/(Nat.factorial n : ℂ) := by
  obtain ⟨p,hp⟩ := (lemma171_regular_numerator_analyticOnNhd χ hD) 0 (by norm_num)
  have hs := lemma171_divided_remainder_power_series χ p hp n
  have hc : lemma171DividedRemainder χ n 0 = p.coeff n := by
    rw [← hs.coeff_zero 1]
    change (FormalMultilinearSeries.fslope^[n] p).coeff 0 = p.coeff n
    simp only [FormalMultilinearSeries.coeff_iterate_fslope,zero_add]
  obtain ⟨r,hpr⟩ := hp
  have hf := hpr.factorial_smul (1 : ℂ) n
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,Finset.prod_const_one,one_smul] at hf
  have he : (Nat.factorial n : ℂ)*p.coeff n = iteratedDeriv n (lemma171RegularNumerator χ) 0 := by
    simpa only [FormalMultilinearSeries.coeff,nsmul_eq_mul] using hf
  rw [hc,← he]
  have hn : (Nat.factorial n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  field_simp [hn]

lemma lemma171_actual_residue_eq_divided_remainder {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) : lemma171ActualResidue χ = lemma171DividedRemainder χ 2 0 :=
  (lemma171_divided_remainder_coefficient χ hD 2).symm


lemma lemma171_rectangle_laurent_kernel (a T : ℝ) (ha : -1/2 ≤ a) (han : a < 0)
    (hT : 0 < T) (k : ℕ) (hk : k < 3) :
    lemma44GeneralRectangleBoundaryIntegral (fun w : ℂ => w^(k : ℤ)/w^(3 : ℤ)) a 1 T =
      if k = 2 then (2*Real.pi*I : ℂ) else 0 := by
  have hfun : (fun w : ℂ => w^(k : ℤ)/w^(3 : ℤ)) =
      (fun w : ℂ => w^((k : ℤ)-3)) := by
    funext w
    by_cases hw : w = 0
    · subst w
      have he : (k : ℤ)-3 ≠ 0 := by omega
      norm_num [zero_zpow ((k : ℤ)-3) he]
    · exact (zpow_sub₀ hw (k : ℤ) 3).symm
  rw [hfun]
  by_cases hk2 : k = 2
  · subst k
    norm_num
    exact lemma32_rectangle_inverse_winding a T ha han hT
  · rw [if_neg hk2]
    exact lemma32_rectangle_zpow_zero _ (by omega) a 1 T (ne_of_lt han) (by norm_num) hT


lemma lemma171_laurent_kernel_continuousOn (k : ℕ) :
    ContinuousOn (fun w : ℂ => w^(k : ℤ)/w^(3 : ℤ)) ({0} : Set ℂ)ᶜ := by
  intro w hw
  have h0 : w ≠ 0 := by simpa using hw
  exact ((continuousAt_id.zpow₀ (k : ℤ) (Or.inl h0)).div
    (continuousAt_id.zpow₀ 3 (Or.inl h0)) (zpow_ne_zero 3 h0)).continuousWithinAt

private lemma lemma171_principal_part_eq_laurent_sum {D : ℕ} (χ : RealPrimitiveCharacter D) :
    lemma171PrincipalPart χ = (fun w : ℂ => ∑ k ∈ Finset.range 3,
      lemma171DividedRemainder χ k 0*(w^(k : ℤ)/w^(3 : ℤ))) := by
  funext w
  simp only [lemma171PrincipalPart,zpow_natCast,mul_div_assoc]
  rfl

lemma lemma171_principal_part_boundary_integrable {D : ℕ} (χ : RealPrimitiveCharacter D)
    (a T : ℝ) (han : a < 0) (hT : 0 < T) : lemma32BoundaryIntegrable (lemma171PrincipalPart χ) a 1 T := by
  have hc : ContinuousOn (lemma171PrincipalPart χ) ({0} : Set ℂ)ᶜ := by
    have hs : ContinuousOn (fun w : ℂ => ∑ k ∈ Finset.range 3,
        lemma171DividedRemainder χ k 0*(w^(k : ℤ)/w^(3 : ℤ))) ({0} : Set ℂ)ᶜ :=
      continuousOn_finsetSum _ (fun k hk =>
        (lemma171_laurent_kernel_continuousOn k).const_mul _)
    rw [lemma171_principal_part_eq_laurent_sum χ]
    exact hs
  exact lemma32_boundary_integrable_punctured _ hc a 1 T (ne_of_lt han) (by norm_num) hT

lemma lemma171_actual_principal_boundary_residue {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (a T : ℝ) (ha : -1/2 ≤ a) (han : a < 0) (hT : 0 < T) :
    lemma44GeneralRectangleBoundaryIntegral (lemma171PrincipalPart χ) a 1 T =
      2*Real.pi*I*lemma171ActualResidue χ := by
  have hfun := lemma171_principal_part_eq_laurent_sum χ
  have hi (k : ℕ) : lemma32BoundaryIntegrable
      (fun w : ℂ => lemma171DividedRemainder χ k 0*(w^(k : ℤ)/w^(3 : ℤ))) a 1 T :=
    lemma32_boundary_integrable_punctured _
      ((lemma171_laurent_kernel_continuousOn k).const_mul _) a 1 T (ne_of_lt han) (by norm_num) hT
  rw [hfun,lemma32_boundary_integral_sum _ _ _ _ _ (fun k hk => hi k)]
  simp_rw [lemma32_boundary_integral_const_mul]
  calc
    _ = ∑ k ∈ Finset.range 3, lemma171DividedRemainder χ k 0*
        (if k = 2 then (2*Real.pi*I : ℂ) else 0) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [lemma171_rectangle_laurent_kernel a T ha han hT k (Finset.mem_range.mp hk)]
    _ = 2*Real.pi*I*lemma171DividedRemainder χ 2 0 := by
      simp [mul_ite,mul_comm]
    _ = _ := by rw [lemma171_actual_residue_eq_divided_remainder χ hD]


lemma lemma171_actual_finite_rectangle_residue {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (a T : ℝ) (ha : -1/2 < a) (han : a < 0) (hT : 0 < T) :
    lemma44GeneralRectangleBoundaryIntegral (lemma171MellinIntegrand χ) a 1 T =
      2*Real.pi*I*lemma171ActualResidue χ := by
  let P := lemma171PrincipalPart χ
  let R := lemma171DividedRemainder χ 3
  have hab : a ≤ 1 := by linarith
  have he (w : ℂ) (hw : -1/2 < w.re) (h0 : w ≠ 0) :
      lemma171MellinIntegrand χ w = P w+R w :=
    lemma171_actual_integrand_principal_decomposition χ w hw h0
  have hb : (∫ x : ℝ in a..1, lemma171MellinIntegrand χ ((x : ℂ)-(T : ℂ)*I)) =
      ∫ x : ℝ in a..1, P ((x : ℂ)-(T : ℂ)*I)+R ((x : ℂ)-(T : ℂ)*I) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hab] at hx
    apply he _ (by simpa using lt_of_lt_of_le ha hx.1)
    intro h;have hi := congrArg Complex.im h;simp at hi;linarith
  have ht : (∫ x : ℝ in a..1, lemma171MellinIntegrand χ ((x : ℂ)+(T : ℂ)*I)) =
      ∫ x : ℝ in a..1, P ((x : ℂ)+(T : ℂ)*I)+R ((x : ℂ)+(T : ℂ)*I) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hab] at hx
    apply he _ (by simpa using lt_of_lt_of_le ha hx.1)
    intro h;have hi := congrArg Complex.im h;simp at hi;linarith
  have hr : (∫ y : ℝ in -T..T, lemma171MellinIntegrand χ ((1 : ℂ)+(y : ℂ)*I)) =
      ∫ y : ℝ in -T..T, P ((1 : ℂ)+(y : ℂ)*I)+R ((1 : ℂ)+(y : ℂ)*I) := by
    apply intervalIntegral.integral_congr
    intro y hy
    apply he _ (by norm_num)
    intro h;have hx := congrArg Complex.re h;norm_num at hx
  have hl : (∫ y : ℝ in -T..T, lemma171MellinIntegrand χ ((a : ℂ)+(y : ℂ)*I)) =
      ∫ y : ℝ in -T..T, P ((a : ℂ)+(y : ℂ)*I)+R ((a : ℂ)+(y : ℂ)*I) := by
    apply intervalIntegral.integral_congr
    intro y hy
    apply he _ (by simpa using ha)
    intro h;have hx := congrArg Complex.re h;simp at hx;linarith
  have hP := lemma171_principal_part_boundary_integrable χ a T han hT
  have hR := lemma32_boundary_integrable_halfplane R
    (lemma171_divided_remainder_differentiableOn χ hD 3).continuousOn a 1 T ha hab
  calc
    _ = lemma44GeneralRectangleBoundaryIntegral (fun w => P w+R w) a 1 T := by
      unfold lemma44GeneralRectangleBoundaryIntegral
      simp only [Complex.ofReal_one]
      rw [hb,ht,hr,hl]
    _ = lemma44GeneralRectangleBoundaryIntegral P a 1 T+
        lemma44GeneralRectangleBoundaryIntegral R a 1 T :=
      lemma32_boundary_integral_add P R a 1 T hP hR
    _ = _ := by
      rw [lemma171_actual_principal_boundary_residue χ hD a T ha.le han hT,
        lemma171_actual_regular_remainder_rectangle_zero χ hD a 1 T ha hab hT.le,add_zero]


lemma lemma171_actual_normalized_finite_shift {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (a T : ℝ) (ha : -1/2 < a) (han : a < 0) (hT : 0 < T) :
    ((1/(2*Real.pi) : ℝ) : ℂ)*
      ((∫ t : ℝ in -T..T, lemma171MellinIntegrand χ (1+(t : ℂ)*I))-
        ∫ t : ℝ in -T..T, lemma171MellinIntegrand χ ((a : ℂ)+(t : ℂ)*I))+
    (2*Real.pi*I : ℂ)⁻¹*
      ((∫ x : ℝ in a..1, lemma171MellinIntegrand χ ((x : ℂ)-(T : ℂ)*I))-
        ∫ x : ℝ in a..1, lemma171MellinIntegrand χ ((x : ℂ)+(T : ℂ)*I)) =
      lemma171ActualResidue χ := by
  have hf := lemma171_actual_finite_rectangle_residue χ hD a T ha han hT
  have hn : (2*Real.pi*I : ℂ)⁻¹*
      lemma44GeneralRectangleBoundaryIntegral (lemma171MellinIntegrand χ) a 1 T =
        lemma171ActualResidue χ := by
    rw [hf,← mul_assoc,inv_mul_cancel₀ Complex.two_pi_I_ne_zero,one_mul]
  unfold lemma44GeneralRectangleBoundaryIntegral at hn
  simp only [Complex.ofReal_one] at hn
  calc
    _ = (2*Real.pi*I : ℂ)⁻¹*
      ((∫ x : ℝ in a..1, lemma171MellinIntegrand χ ((x : ℂ)-(T : ℂ)*I))-
        (∫ x : ℝ in a..1, lemma171MellinIntegrand χ ((x : ℂ)+(T : ℂ)*I))+
        I*(∫ t : ℝ in -T..T, lemma171MellinIntegrand χ (1+(t : ℂ)*I))-
        I*(∫ t : ℝ in -T..T, lemma171MellinIntegrand χ ((a : ℂ)+(t : ℂ)*I))) := by
      rw [← lemma32_mellin_normalizing_factor]
      ring
    _ = _ := hn


end ZhangLS.Spec
