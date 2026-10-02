import ZhangLS.Spec.Lemma32NormalizedFiniteShift
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Metric Set Filter
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma32_gamma_shift_product (z : ℂ) (hz : z.im ≠ 0) (n : ℕ) :
    Complex.Gamma (z+(n : ℂ)) = Complex.Gamma z*(∏ j ∈ Finset.range n, (z+(j : ℂ))) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hne : z+(n : ℂ) ≠ 0 := by
      intro h;have hi := congrArg Complex.im h;simp at hi;exact hz hi
    rw [show z+((n+1 : ℕ) : ℂ) = (z+(n : ℂ))+1 by push_cast;ring,
      Complex.Gamma_add_one _ hne,ih,Finset.prod_range_succ]
    ring

lemma lemma32_gamma_shift_norm_lower (z : ℂ) (hz : z.im ≠ 0) (n : ℕ) :
    |z.im|^n*‖Complex.Gamma z‖ ≤ ‖Complex.Gamma (z+(n : ℂ))‖ := by
  have hp : |z.im|^n ≤ ∏ j ∈ Finset.range n, ‖z+(j : ℂ)‖ := by
    calc
      _ = ∏ j ∈ Finset.range n, |z.im| := by simp
      _ ≤ _ := Finset.prod_le_prod (fun j hj => abs_nonneg _) (fun j hj => by
        simpa using Complex.abs_im_le_norm (z+(j : ℂ)))
  rw [lemma32_gamma_shift_product z hz n,norm_mul,norm_prod]
  calc
    _ ≤ (∏ j ∈ Finset.range n, ‖z+(j : ℂ)‖)*‖Complex.Gamma z‖ :=
      mul_le_mul_of_nonneg_right hp (norm_nonneg _)
    _ = _ := by ring

lemma lemma32_gamma_strip_polynomial_decay (z : ℂ) (hlo : -1/4 ≤ z.re) (hhi : z.re ≤ 1)
    (hz : z.im ≠ 0) (n : ℕ) (hn : 2 ≤ n) :
    ‖Complex.Gamma z‖ ≤ (1+(n.factorial : ℝ))/|z.im|^n := by
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hg : ‖Complex.Gamma (z+(n : ℂ))‖ ≤ 1+(n.factorial : ℝ) :=
    lemma44_norm_Gamma_le_factorial
      (by simp only [Complex.add_re,Complex.natCast_re];linarith)
      (by simp only [Complex.add_re,Complex.natCast_re];linarith)
  apply (le_div_iff₀ (pow_pos (abs_pos.mpr hz) n)).mpr
  calc
    _ = |z.im|^n*‖Complex.Gamma z‖ := by ring
    _ ≤ ‖Complex.Gamma (z+(n : ℂ))‖ := lemma32_gamma_shift_norm_lower z hz n
    _ ≤ _ := hg

end ZhangLS.Spec
