import ZhangLS.Spec.Lemma44GammaLogDerivative
import ZhangLS.Spec.Lemma23DirichletBranch

/-!
# Effective bounds for the actual Dirichlet functional-equation factor

The logarithmic derivative of the conductor power is separated exactly from
the two archimedean factors. The Gamma estimates are proved from Euler's
integral and reflection, rather than assumed as a complex Stirling formula.
-/

namespace ZhangLS.Spec

open Complex

set_option maxHeartbeats 1000000

/-- Logarithmic differentiation of a nonzero constant raised to an affine power. -/
theorem lemma44_logDeriv_const_cpow_affine {b : ℂ} (hb : b ≠ 0) (a d s : ℂ) :
    logDeriv (fun z : ℂ => b ^ (a + d * z)) s = Complex.log b * d := by
  have harg : HasDerivAt (fun z : ℂ => a + d * z) d s := by
    simpa using ((hasDerivAt_id s).const_mul d).const_add a
  rw [logDeriv_apply, (harg.const_cpow (Or.inl hb)).deriv]
  have hp : b ^ (a + d * s) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hb)
  field_simp

/-- The exact logarithmic derivative of Deligne's real Gamma factor. -/
theorem lemma44_GammaR_logDeriv {s : ℂ} (him : s.im ≠ 0) :
    logDeriv Complex.Gammaℝ s =
      -Complex.log (Real.pi : ℂ) / 2 + logDeriv Complex.Gamma (s / 2) / 2 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hΓ : Complex.Gamma (s / 2) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m h
    apply him
    have h' := congrArg Complex.im h
    simp at h'
    linarith
  have hdiff : DifferentiableAt ℂ Complex.Gamma (s / 2) := by
    apply Complex.differentiableAt_Gamma
    intro m h
    apply him
    have h' := congrArg Complex.im h
    simp at h'
    linarith
  have hpDiff : DifferentiableAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s :=
    (show DifferentiableAt ℂ (fun z : ℂ => -z / 2) s by fun_prop).const_cpow (Or.inl hpi)
  have hfun : Complex.Gammaℝ =
      fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2) := rfl
  rw [hfun, logDeriv_mul (f := fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2))
    (g := fun z : ℂ => Complex.Gamma (z / 2)) s
    (Complex.cpow_ne_zero_iff.mpr (Or.inl hpi)) hΓ hpDiff
    (hdiff.comp s (differentiableAt_id.div_const 2))]
  have hp : logDeriv (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s =
      -Complex.log (Real.pi : ℂ) / 2 := by
    have heq : (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) =
        (fun z : ℂ => (Real.pi : ℂ) ^ (0 + (-1 / 2 : ℂ) * z)) := by
      funext z; congr 1; ring
    rw [heq, lemma44_logDeriv_const_cpow_affine hpi]
    ring
  have hg : logDeriv (fun z : ℂ => Complex.Gamma (z / 2)) s =
      logDeriv Complex.Gamma (s / 2) / 2 := by
    have h := logDeriv_comp (g := fun z : ℂ => z / 2) (x := s)
      hdiff (differentiableAt_id.div_const (2 : ℂ))
    simpa [Function.comp_def, div_eq_mul_inv] using h
  rw [hp, hg]

/-- The same Gamma logarithmic-derivative estimate works for both character parities. -/
theorem lemma44_gammaFactor_logDeriv_bound {N : ℕ}
    (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hheight : 24 ≤ |s.im|) (hre : |s.re| + 1 ≤ |s.im| / 4) :
    ‖logDeriv (DirichletCharacter.gammaFactor χ) s‖ ≤
      24 * Real.log (3 * |s.im|) + 8 * Real.pi + 4 +
        ‖Complex.log (Real.pi : ℂ)‖ / 2 := by
  have hGammaR {z : ℂ} (hzIm : z.im = s.im) (hzRe : |z.re| ≤ |s.im| / 4) :
      ‖logDeriv Complex.Gammaℝ z‖ ≤
        24 * Real.log (3 * |s.im|) + 8 * Real.pi + 4 +
          ‖Complex.log (Real.pi : ℂ)‖ / 2 := by
    have hzne : z.im ≠ 0 := by rw [hzIm]; intro h; rw [h, abs_zero] at hheight; linarith
    have hg : ‖logDeriv Complex.Gamma (z / 2)‖ ≤
        48 * Real.log (3 * |s.im|) + 16 * Real.pi + 8 := by
      have hh : 12 ≤ |(z / 2).im| := by simp [hzIm, abs_div]; linarith
      have hr : |(z / 2).re| ≤ |(z / 2).im| / 4 := by
        simp [hzIm, abs_div]; linarith
      have h := lemma44_norm_logDeriv_Gamma_le_log_height hh hr
      have hl : Real.log (3 * |(z / 2).im|) ≤ Real.log (3 * |s.im|) := by
        apply Real.log_le_log (by linarith : 0 < 3 * |(z / 2).im|)
        simp [hzIm, abs_div]
      exact h.trans (by linarith)
    rw [lemma44_GammaR_logDeriv hzne]
    have htriangle := norm_add_le (-Complex.log (Real.pi : ℂ) / 2)
      (logDeriv Complex.Gamma (z / 2) / 2)
    norm_num [norm_div, norm_neg] at htriangle
    linarith
  rcases χ.even_or_odd with heven | hodd
  · have heq : DirichletCharacter.gammaFactor χ = Complex.Gammaℝ := by
      funext z; exact heven.gammaFactor_def z
    rw [heq]
    exact hGammaR rfl (by linarith)
  · have heq : DirichletCharacter.gammaFactor χ = fun z : ℂ => Complex.Gammaℝ (z + 1) := by
      funext z; exact hodd.gammaFactor_def z
    rw [heq]
    have hz : (s + 1).im ≠ 0 := by
      simp only [Complex.add_im, Complex.one_im, add_zero]
      intro h; rw [h, abs_zero] at hheight; linarith
    have hcomp := logDeriv_comp (g := fun z : ℂ => z + 1) (x := s)
      (lemma23_GammaR_differentiableAt_of_im_ne_zero hz)
      (differentiableAt_id.add_const (1 : ℂ))
    have hlog : logDeriv (fun z : ℂ => Complex.Gammaℝ (z + 1)) s =
        logDeriv Complex.Gammaℝ (s + 1) := by simpa [Function.comp_def] using hcomp
    rw [hlog]
    apply hGammaR (by simp)
    have h := abs_add_le s.re 1
    simp at h
    simpa using h.trans hre

/-- The conductor contribution to the actual `Z` logarithmic derivative is exact. -/
theorem lemma44_DirichletZ_logDeriv {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (hN : N ≠ 1)
    {s : ℂ} (him : s.im ≠ 0) :
    logDeriv (lemma23DirichletZ χ) s = -Complex.log (N : ℂ) -
      logDeriv (DirichletCharacter.gammaFactor χ⁻¹) (1 - s) -
      logDeriv (DirichletCharacter.gammaFactor χ) s := by
  have hNr : (N : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  have hr : DirichletCharacter.rootNumber χ ≠ 0 := by
    exact norm_ne_zero_iff.mp (by rw [lemma23_rootNumber_norm_eq_one χ hχ hN]; norm_num)
  have hmirror : (1 - s).im ≠ 0 := by simpa using neg_ne_zero.mpr him
  have hp : DifferentiableAt ℂ (fun z : ℂ => (N : ℂ) ^ ((1 / 2 : ℂ) - z)) s :=
    (show DifferentiableAt ℂ (fun z : ℂ => (1 / 2 : ℂ) - z) s by fun_prop).const_cpow (Or.inl hNr)
  have hnum := (lemma23_gammaFactor_differentiableAt_of_im_ne_zero χ⁻¹ hmirror).comp s
    (differentiableAt_id.const_sub 1)
  have hden := lemma23_gammaFactor_differentiableAt_of_im_ne_zero χ him
  have hnne := lemma23_gammaFactor_ne_zero_of_im_ne_zero χ⁻¹ hmirror
  have hdne := lemma23_gammaFactor_ne_zero_of_im_ne_zero χ him
  have heq : lemma23DirichletZ χ = fun z : ℂ =>
      ((N : ℂ) ^ ((1 / 2 : ℂ) - z) * DirichletCharacter.rootNumber χ) *
        (DirichletCharacter.gammaFactor χ⁻¹ (1 - z) / DirichletCharacter.gammaFactor χ z) := rfl
  rw [heq, logDeriv_mul
    (f := fun z : ℂ => (N : ℂ) ^ ((1 / 2 : ℂ) - z) * DirichletCharacter.rootNumber χ)
    (g := fun z : ℂ => DirichletCharacter.gammaFactor χ⁻¹ (1 - z) /
      DirichletCharacter.gammaFactor χ z)
    s (mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hNr)) hr)
    (div_ne_zero hnne hdne) (hp.mul_const _) (hnum.div hden hdne),
    logDeriv_mul_const s _ hr,
    logDeriv_div (f := fun z : ℂ => DirichletCharacter.gammaFactor χ⁻¹ (1 - z))
      (g := DirichletCharacter.gammaFactor χ) s hnne hdne hnum hden]
  have hpower : logDeriv (fun z : ℂ => (N : ℂ) ^ ((1 / 2 : ℂ) - z)) s =
      -Complex.log (N : ℂ) := by
    have he : (fun z : ℂ => (N : ℂ) ^ ((1 / 2 : ℂ) - z)) =
        (fun z : ℂ => (N : ℂ) ^ ((1 / 2 : ℂ) + (-1 : ℂ) * z)) := by
      funext z; congr 1; ring
    rw [he, lemma44_logDeriv_const_cpow_affine hNr]
    ring
  have hreflect : logDeriv (fun z : ℂ => DirichletCharacter.gammaFactor χ⁻¹ (1 - z)) s =
      -logDeriv (DirichletCharacter.gammaFactor χ⁻¹) (1 - s) := by
    have h := logDeriv_comp (g := fun z : ℂ => 1 - z) (x := s)
      (lemma23_gammaFactor_differentiableAt_of_im_ne_zero χ⁻¹ hmirror)
      (differentiableAt_id.const_sub (1 : ℂ))
    simpa [Function.comp_def] using h
  rw [hpower, hreflect]
  ring

/-- Uniform effective control of the archimedean error in the actual factor. -/
theorem lemma44_DirichletZ_logDeriv_bound {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (hN : N ≠ 1)
    {s : ℂ} (hheight : 24 ≤ |s.im|) (hre : |s.re| + 2 ≤ |s.im| / 4) :
    ‖logDeriv (lemma23DirichletZ χ) s + Complex.log (N : ℂ)‖ ≤
      48 * Real.log (3 * |s.im|) + 16 * Real.pi + 8 +
        ‖Complex.log (Real.pi : ℂ)‖ := by
  have him : s.im ≠ 0 := by intro h; rw [h, abs_zero] at hheight; linarith
  have hg := lemma44_gammaFactor_logDeriv_bound χ hheight (by linarith)
  have hrefl : |(1 - s).re| + 1 ≤ |(1 - s).im| / 4 := by
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
      zero_sub, abs_neg]
    have h := abs_add_le 1 (-s.re)
    simp only [abs_one, abs_neg, ← sub_eq_add_neg] at h
    linarith
  have hg' := lemma44_gammaFactor_logDeriv_bound χ⁻¹ (s := 1 - s)
    (by simpa using hheight) hrefl
  simp only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] at hg'
  rw [lemma44_DirichletZ_logDeriv χ hχ hN him]
  have he : -Complex.log (N : ℂ) - logDeriv (DirichletCharacter.gammaFactor χ⁻¹) (1 - s) -
      logDeriv (DirichletCharacter.gammaFactor χ) s + Complex.log (N : ℂ) =
      -(logDeriv (DirichletCharacter.gammaFactor χ⁻¹) (1 - s) +
        logDeriv (DirichletCharacter.gammaFactor χ) s) := by ring
  rw [he, norm_neg]
  exact (norm_add_le _ _).trans (by linarith)

/-- The product factor, for any two actual primitive Dirichlet characters. -/
noncomputable def lemma44ProductZ {N M : ℕ} [NeZero N] [NeZero M]
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) (s : ℂ) : ℂ :=
  lemma23DirichletZ χ s * lemma23DirichletZ ψ s

/-- The two conductor contributions add, with an explicit logarithmic height error. -/
theorem lemma44_productZ_logDeriv_bound {N M : ℕ} [NeZero N] [NeZero M]
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive) (hN : N ≠ 1) (hM : M ≠ 1)
    {s : ℂ} (hheight : 24 ≤ |s.im|) (hre : |s.re| + 2 ≤ |s.im| / 4) :
    ‖logDeriv (lemma44ProductZ χ ψ) s + Complex.log (N : ℂ) + Complex.log (M : ℂ)‖ ≤
      96 * Real.log (3 * |s.im|) + 32 * Real.pi + 16 +
        2 * ‖Complex.log (Real.pi : ℂ)‖ := by
  have him : s.im ≠ 0 := by intro h; rw [h, abs_zero] at hheight; linarith
  have hne {K : ℕ} [NeZero K] (θ : DirichletCharacter ℂ K)
      (hθ : θ.IsPrimitive) (hK : K ≠ 1) : lemma23DirichletZ θ s ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast NeZero.ne K)))
      apply norm_ne_zero_iff.mp
      rw [lemma23_rootNumber_norm_eq_one θ hθ hK]
      norm_num
    · exact div_ne_zero
        (lemma23_gammaFactor_ne_zero_of_im_ne_zero θ⁻¹ (by simpa using neg_ne_zero.mpr him))
        (lemma23_gammaFactor_ne_zero_of_im_ne_zero θ him)
  have hlog : logDeriv (lemma44ProductZ χ ψ) s =
      logDeriv (lemma23DirichletZ χ) s + logDeriv (lemma23DirichletZ ψ) s :=
    logDeriv_mul s (hne χ hχ hN) (hne ψ hψ hM)
      (lemma23DirichletZ_differentiableAt_of_im_ne_zero χ him)
      (lemma23DirichletZ_differentiableAt_of_im_ne_zero ψ him)
  rw [hlog]
  have heq : logDeriv (lemma23DirichletZ χ) s + logDeriv (lemma23DirichletZ ψ) s +
      Complex.log (N : ℂ) + Complex.log (M : ℂ) =
      (logDeriv (lemma23DirichletZ χ) s + Complex.log (N : ℂ)) +
        (logDeriv (lemma23DirichletZ ψ) s + Complex.log (M : ℂ)) := by ring
  rw [heq]
  have h₁ := lemma44_DirichletZ_logDeriv_bound χ hχ hN hheight hre
  have h₂ := lemma44_DirichletZ_logDeriv_bound ψ hψ hM hheight hre
  exact (norm_add_le _ _).trans (by linarith)

end ZhangLS.Spec
