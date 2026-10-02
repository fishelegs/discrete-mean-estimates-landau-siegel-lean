import ZhangLS.Spec.Lemma44GaussianLongSum

/-!
# Exact Gaussian Mellin representation of the long sum

The existing scalar Gaussian inversion theorem is applied coefficient by
coefficient. Absolute integrability justifies the finite sum/integral
exchange, then the complex powers are recombined into the actual long
Dirichlet polynomial at the shifted argument.
-/

namespace ZhangLS.Spec

open Complex MeasureTheory

set_option maxHeartbeats 1000000

theorem lemma44_finite_gaussian_mellin_identity {D : ℕ}
    (hD : 1 < D) (S : Finset ℕ) (c : ℕ → ℂ)
    (hS : ∀ n ∈ S, 0 < n) {B σ : ℝ} (hB : 0 < B) (hσ : 0 < σ) :
    (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        (∫ t : ℝ, (∑ n ∈ S, c n * lemma57GaussianKernelIntegrand D σ (B / n) t) *
          Complex.I) =
      ∑ n ∈ S, c n * (zhangGaussianWeight D (B / n) : ℂ) := by
  have hint (n : ℕ) (hn : n ∈ S) :
      Integrable (fun t : ℝ => c n * lemma57GaussianKernelIntegrand D σ (B / n) t) :=
    (lemma57GaussianKernel_integrable hD hσ.ne'
      (div_pos hB (by exact_mod_cast hS n hn))).const_mul _
  rw [integral_mul_const, integral_finsetSum S hint]
  simp_rw [integral_const_mul]
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hk := lemma57GaussianKernelVerticalIntegral_eq_weight (x := B / n) hD hσ
    (div_pos hB (by exact_mod_cast hS n hn))
  rw [lemma57GaussianKernelVerticalIntegral, integral_mul_const] at hk
  calc
    _ = c n * ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      ((∫ t : ℝ, lemma57GaussianKernelIntegrand D σ (B / n) t) * Complex.I)) := by ring
    _ = _ := by rw [hk]

/-- The vertical integrand with the actual long polynomial at `s+w`. -/
noncomputable def lemma44GaussianLongMellinIntegrand {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N)
    (s : ℂ) (B σ t : ℝ) : ℂ :=
  let w := (σ : ℂ) + (t : ℂ) * Complex.I
  lemma44LongDirichletSum χ ψ (s + w) * Complex.exp (w * (Real.log B : ℂ)) *
    lemma57OmegaOne D w / w

private theorem lemma44_gaussian_mellin_term {D n : ℕ} {B σ t : ℝ}
    (hB : 0 < B) (hn : 0 < n) (s c : ℂ) :
    (c * Complex.exp (-s * (Real.log (n : ℝ) : ℂ))) *
        lemma57GaussianKernelIntegrand D σ (B / n) t =
      (c * Complex.exp (-(s + ((σ : ℂ) + (t : ℂ) * Complex.I)) *
        (Real.log (n : ℝ) : ℂ))) *
          Complex.exp (((σ : ℂ) + (t : ℂ) * Complex.I) * (Real.log B : ℂ)) *
            lemma57OmegaOne D ((σ : ℂ) + (t : ℂ) * Complex.I) /
              ((σ : ℂ) + (t : ℂ) * Complex.I) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hx : (0 : ℝ) < B / n := div_pos hB hnpos
  have hxC : ((B / n : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hlog : Complex.log ((B / n : ℝ) : ℂ) =
      (Real.log B : ℂ) - (Real.log (n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_log hx.le, Real.log_div hB.ne' hnpos.ne', Complex.ofReal_sub]
  rw [lemma57GaussianKernelIntegrand, Complex.cpow_def_of_ne_zero hxC, hlog]
  have he : Complex.exp (-s * (Real.log (n : ℝ) : ℂ)) *
      Complex.exp (((Real.log B : ℂ) - (Real.log (n : ℝ) : ℂ)) *
        ((σ : ℂ) + (t : ℂ) * Complex.I)) =
      Complex.exp (-(s + ((σ : ℂ) + (t : ℂ) * Complex.I)) *
        (Real.log (n : ℝ) : ℂ)) *
          Complex.exp (((σ : ℂ) + (t : ℂ) * Complex.I) * (Real.log B : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  calc
    _ = c * (Complex.exp (-s * (Real.log (n : ℝ) : ℂ)) *
      Complex.exp (((Real.log B : ℂ) - (Real.log (n : ℝ) : ℂ)) *
        ((σ : ℂ) + (t : ℂ) * Complex.I))) *
          lemma57OmegaOne D ((σ : ℂ) + (t : ℂ) * Complex.I) /
            ((σ : ℂ) + (t : ℂ) * Complex.I) := by ring
    _ = _ := by rw [he]; ring

theorem lemma44_gaussian_long_mellin_integrand_eq_sum {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N) (s : ℂ)
    {B : ℝ} (hB : 0 < B) (σ t : ℝ) :
    lemma44GaussianLongMellinIntegrand χ ψ s B σ t =
      ∑ n ∈ Finset.Ioc (D ^ 4) ⌊lemma23PaperP D ^ 2⌋₊,
        (lemma23NuArithmeticFunction χ n * ψ (n : ZMod N) *
          Complex.exp (-s * (Real.log (n : ℝ) : ℂ))) *
            lemma57GaussianKernelIntegrand D σ (B / n) t := by
  dsimp only [lemma44GaussianLongMellinIntegrand, lemma44LongDirichletSum]
  rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  exact (lemma44_gaussian_mellin_term hB
    (lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hn).1) s
      (lemma23NuArithmeticFunction χ n * ψ (n : ZMod N))).symm

theorem lemma44_gaussian_long_mellin_integrable {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N) (s : ℂ)
    (hD : 1 < D) {B σ : ℝ} (hB : 0 < B) (hσ : σ ≠ 0) :
    Integrable (lemma44GaussianLongMellinIntegrand χ ψ s B σ) := by
  change Integrable (fun t : ℝ => lemma44GaussianLongMellinIntegrand χ ψ s B σ t)
  simp_rw [lemma44_gaussian_long_mellin_integrand_eq_sum χ ψ s hB σ]
  apply integrable_finsetSum
  intro n hn
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hn).1)
  exact (lemma57GaussianKernel_integrable hD hσ (div_pos hB hnpos)).const_mul _

/-- The actual long sum with its Gaussian weight is exactly the absolutely
convergent Mellin integral of the shifted actual long polynomial. -/
theorem lemma44_gaussian_long_mellin_identity {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N) (s : ℂ)
    (hD : 1 < D) {B σ : ℝ} (hB : 0 < B) (hσ : 0 < σ) :
    (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        (∫ t : ℝ, lemma44GaussianLongMellinIntegrand χ ψ s B σ t * Complex.I) =
      lemma44GaussianLongDirichletSum χ ψ s B := by
  simp_rw [lemma44_gaussian_long_mellin_integrand_eq_sum χ ψ s hB σ]
  exact lemma44_finite_gaussian_mellin_identity hD _ _
    (fun n hn => lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hn).1) hB hσ

end ZhangLS.Spec
