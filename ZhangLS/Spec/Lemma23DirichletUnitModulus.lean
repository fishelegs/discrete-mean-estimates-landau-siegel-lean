import ZhangLS.Spec.Lemma23PrimitiveGaussSum

/-!
# Gamma-factor symmetry and unit modulus in Lemma 2.3

This module proves the remaining pointwise facts for Zhang's functional-
equation factor on the critical line, using the primitive Gauss-sum estimate
and conjugation of the archimedean gamma factor.
-/

namespace ZhangLS.Spec

open ComplexConjugate

/-- Conjugation symmetry of Deligne's real gamma factor. -/
theorem lemma23_GammaR_conj (s : ℂ) :
    Complex.Gammaℝ (conj s) = conj (Complex.Gammaℝ s) := by
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def]
  have harg : (Real.pi : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]
    exact Real.pi_ne_zero.symm
  have hpow : (Real.pi : ℂ) ^ (-conj s / 2) =
      conj ((Real.pi : ℂ) ^ (-s / 2)) := by
    have h := Complex.cpow_conj (Real.pi : ℂ) (-s / 2) harg
    have hpi : star (Real.pi : ℂ) = (Real.pi : ℂ) := by
      rw [Complex.star_def, Complex.conj_ofReal]
    calc
      (Real.pi : ℂ) ^ (-conj s / 2) =
          star (star (Real.pi : ℂ) ^ (-s / 2)) := by
        simpa only [map_div₀, map_neg, map_ofNat, starRingEnd_apply] using h
      _ = star ((Real.pi : ℂ) ^ (-s / 2)) := by rw [hpi]
      _ = conj ((Real.pi : ℂ) ^ (-s / 2)) := by rw [Complex.star_def]
  have hhalf : conj s / 2 = conj (s / 2) := by
    calc
      conj s / 2 = conj s / conj (2 : ℂ) := by rw [Complex.conj_ofNat]
      _ = conj (s / 2) := (map_div₀ conj s (2 : ℂ)).symm
  have hGamma : Complex.Gamma (conj s / 2) = conj (Complex.Gamma (s / 2)) := by
    rw [hhalf, Complex.Gamma_conj]
  calc
    (Real.pi : ℂ) ^ (-conj s / 2) * Complex.Gamma (conj s / 2) =
        conj ((Real.pi : ℂ) ^ (-s / 2)) * conj (Complex.Gamma (s / 2)) := by
      rw [hpow, hGamma]
    _ = conj ((Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2)) := by
      rw [map_mul]
    _ = conj (Complex.Gammaℝ s) := by rw [Complex.Gammaℝ_def]

/-- Inverting a character preserves its parity, so its gamma factor at the
conjugate point is the conjugate of the original gamma factor. -/
theorem lemma23_gammaFactor_inv_conj
    {N : ℕ} (χ : DirichletCharacter ℂ N) (s : ℂ) :
    DirichletCharacter.gammaFactor χ⁻¹ (conj s) =
      conj (DirichletCharacter.gammaFactor χ s) := by
  rcases χ.even_or_odd with heven | hodd
  · have hevenInv : χ⁻¹.Even := by
      change χ⁻¹ (-1) = 1
      change χ (-1) = 1 at heven
      rw [MulChar.inv_apply_eq_inv', heven]
      simp
    rw [hevenInv.gammaFactor_def, heven.gammaFactor_def, lemma23_GammaR_conj]
  · have hoddInv : χ⁻¹.Odd := by
      change χ⁻¹ (-1) = -1
      change χ (-1) = -1 at hodd
      rw [MulChar.inv_apply_eq_inv', hodd]
      simp
    rw [hoddInv.gammaFactor_def, hodd.gammaFactor_def]
    rw [show conj s + 1 = conj (s + 1) by simp, lemma23_GammaR_conj]

/-- The archimedean gamma factor has no zeros away from the real axis. -/
theorem lemma23_gammaFactor_ne_zero_of_im_ne_zero
    {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : s.im ≠ 0) :
    DirichletCharacter.gammaFactor χ s ≠ 0 := by
  rcases χ.even_or_odd with heven | hodd
  · rw [heven.gammaFactor_def]
    intro hzero
    obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp hzero
    apply hs
    rw [hn]
    simp
  · rw [hodd.gammaFactor_def]
    intro hzero
    obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp hzero
    apply hs
    have him : (s + 1).im = 0 := by rw [hn]; simp
    simpa using him

/-- The factor `Z(s,χ)` is nonzero in the upper half-plane for a primitive
character of nontrivial level. -/
theorem lemma23DirichletZ_ne_zero_of_im_pos
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : DirichletCharacter.IsPrimitive χ) (hN : N ≠ 1)
    {s : ℂ} (hs : 0 < s.im) : lemma23DirichletZ χ s ≠ 0 := by
  apply mul_ne_zero
  · apply mul_ne_zero
    · have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
      exact norm_pos_iff.mp (Complex.norm_natCast_cpow_pos_of_pos hNpos _)
    · have hroot := lemma23_rootNumber_norm_eq_one χ hχ hN
      exact norm_pos_iff.mp (by rw [hroot]; norm_num)
  · apply div_ne_zero
    · apply lemma23_gammaFactor_ne_zero_of_im_ne_zero
      simpa [Complex.sub_im] using neg_ne_zero.mpr hs.ne'
    · exact lemma23_gammaFactor_ne_zero_of_im_ne_zero χ hs.ne'

/-- The paper's factor `Z(s,χ)` has modulus one on the critical line.  This
uses the primitive root-number norm proved from the discrete Fourier identity. -/
theorem lemma23DirichletZ_norm_eq_one_on_critical_line
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : DirichletCharacter.IsPrimitive χ) (hN : N ≠ 1)
    {s : ℂ} (hs : s.re = 1 / 2) : ‖lemma23DirichletZ χ s‖ = 1 := by
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hreflection : conj s = 1 - s := by
    apply Complex.ext <;>
      simp [Complex.sub_re, Complex.sub_im, hs] <;> ring
  have hgamma : DirichletCharacter.gammaFactor χ s ≠ 0 :=
    lemma23_gammaFactor_ne_zero_of_re_pos χ (by rw [hs]; norm_num)
  have hgammaInv : DirichletCharacter.gammaFactor χ⁻¹ (1 - s) =
      conj (DirichletCharacter.gammaFactor χ s) := by
    rw [← hreflection]
    exact lemma23_gammaFactor_inv_conj χ s
  have hbaseNorm : ‖(N : ℂ) ^ ((1 / 2 : ℂ) - s)‖ = 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hNpos]
    have hexp : (((1 / 2 : ℂ) - s).re) = 0 := by simp [Complex.sub_re, hs]
    rw [hexp, Real.rpow_zero]
  have hratioNorm :
      ‖DirichletCharacter.gammaFactor χ⁻¹ (1 - s) /
        DirichletCharacter.gammaFactor χ s‖ = 1 := by
    rw [hgammaInv, norm_div, Complex.norm_conj]
    exact div_self (norm_ne_zero_iff.mpr hgamma)
  have hrootNorm := lemma23_rootNumber_norm_eq_one χ hχ hN
  rw [lemma23DirichletZ, norm_mul, norm_mul, hbaseNorm, hrootNorm, hratioNorm]
  norm_num

/-- Lemma 2.3's sign conclusion specialized to an actual primitive Dirichlet
L-function: the functional equation, conjugation identity, and unit modulus
of `Z` are all discharged here.  Only the local simple-zero data and the
zero-free offset intervals (supplied by Proposition 2.2) remain inputs. -/
theorem lemma23_verticalLine_coefficient_nonneg_of_actual_dirichlet_LFunction
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : DirichletCharacter.IsPrimitive χ) (hN : N ≠ 1)
    (ρ : ℂ) (hρ : ρ.re = 1 / 2) {mDeriv : ℂ} {b₁ b₂ b₃ : ℝ}
    (horder : 0 < b₁ ∧ b₁ ≤ b₂ ∧ b₂ ≤ b₃)
    (M Y : ℂ → ℂ)
    (hMcont : ContinuousOn M
      (criticalLinePoint ρ '' Set.Icc 0 b₃))
    (hMderiv : HasDerivAt M mDeriv ρ) (hMderivNe : mDeriv ≠ 0)
    (hMzero : M ρ = 0)
    (hfactor : ∀ t : ℝ,
      M (ρ + Complex.I * (t : ℂ)) =
        Y (ρ + Complex.I * (t : ℂ)) *
          DirichletCharacter.LFunction χ (ρ + Complex.I * (t : ℂ)))
    (hYsquare : ∀ t : ℝ,
      (Y (ρ + Complex.I * (t : ℂ))) ^ 2 =
        (lemma23DirichletZ χ (ρ + Complex.I * (t : ℂ)))⁻¹)
    (hnozero₁ : ∀ ⦃t : ℝ⦄, 0 < t → t ≤ b₁ →
      M (criticalLinePoint ρ t) ≠ 0)
    (hnozero₂ : ∀ x ∈ Set.Icc b₂ b₃,
      M (criticalLinePoint ρ x) ≠ 0) :
    ((lemma23ComplexCoefficient
      (M (ρ + Complex.I * (b₁ : ℂ)))
      (M (ρ + Complex.I * (b₂ : ℂ)))
      (M (ρ + Complex.I * (b₃ : ℂ))) mDeriv).im = 0) ∧
    0 ≤ (lemma23ComplexCoefficient
      (M (ρ + Complex.I * (b₁ : ℂ)))
      (M (ρ + Complex.I * (b₂ : ℂ)))
      (M (ρ + Complex.I * (b₃ : ℂ))) mDeriv).re := by
  have hχne : χ ≠ 1 := by
    intro h
    have hprimitive := (DirichletCharacter.isPrimitive_def χ).mp hχ
    rw [h, DirichletCharacter.conductor_one] at hprimitive
    exact hN hprimitive.symm
  have hFE : ∀ t : ℝ,
      DirichletCharacter.LFunction χ (ρ + Complex.I * (t : ℂ)) =
        lemma23DirichletZ χ (ρ + Complex.I * (t : ℂ)) *
          DirichletCharacter.LFunction χ⁻¹
            (1 - (ρ + Complex.I * (t : ℂ))) := by
    intro t
    have hsRe : (ρ + Complex.I * (t : ℂ)).re = 1 / 2 := by
      simp [Complex.add_re, Complex.mul_re, hρ]
    have hmirrorRe : (1 - (ρ + Complex.I * (t : ℂ))).re = 1 / 2 := by
      rw [Complex.sub_re, Complex.one_re, hsRe]
      norm_num
    exact lemma23_dirichletLFunction_functional_equation χ hχ hN
      (lemma23_gammaFactor_ne_zero_of_re_pos χ (by rw [hsRe]; norm_num))
      (lemma23_gammaFactor_ne_zero_of_re_pos χ⁻¹ (by rw [hmirrorRe]; norm_num))
  have hZnorm : ∀ t : ℝ,
      ‖lemma23DirichletZ χ (ρ + Complex.I * (t : ℂ))‖ = 1 := by
    intro t
    exact lemma23DirichletZ_norm_eq_one_on_critical_line χ hχ hN (by
      simp [Complex.add_re, Complex.mul_re, hρ])
  have hconj : ∀ t : ℝ,
      DirichletCharacter.LFunction χ⁻¹
          (1 - (ρ + Complex.I * (t : ℂ))) =
        conj (DirichletCharacter.LFunction χ (ρ + Complex.I * (t : ℂ))) := by
    intro t
    exact dirichletLFunction_inv_eq_conj_reflection_critical χ
      hχne ρ hρ t
  exact lemma23_verticalLine_coefficient_nonneg_of_square_root
    M Y (DirichletCharacter.LFunction χ) (DirichletCharacter.LFunction χ⁻¹)
    (lemma23DirichletZ χ) horder hMcont hMderiv hMderivNe hMzero
    hfactor hFE hYsquare hZnorm hconj hnozero₁ hnozero₂

end ZhangLS.Spec
