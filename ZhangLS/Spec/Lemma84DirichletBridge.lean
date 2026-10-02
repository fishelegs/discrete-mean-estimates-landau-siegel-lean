import ZhangLS.Spec.Lemma84Definitions
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex

lemma lemma84_actual_L_ne_zero_right {D : ℕ} (χ : RealPrimitiveCharacter D)
    {s : ℂ} (hs : 1 < s.re) : dirichletLFunction χ s ≠ 0 := by
  rw [dirichletLFunction_eq_series χ hs]
  exact χ.chi.LSeries_ne_zero_of_one_lt_re hs

/-- The true 8.3 Dirichlet-series identity in its convergence half-plane.
The reciprocal is justified by a theorem about the actual L-function. -/
lemma lemma84_actual_dirichlet_bridge {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (d r : ℕ) (hd : 0 < d) (hr : 0 < r)
    (s : ℂ) (hs : 0 < s.re) :
    LSeriesSummable (fun n => χ.evalNat n*lemma83Xi (lemma83PaperBeta D c) j n d r) (1+s) ∧
      lemma83XiDirichletSeries χ (lemma83PaperBeta D c) j d r (1+s) =
        dirichletLFunction χ (1+s+lemma83PaperBeta D c (j+1)) *
          dirichletLFunction χ (1+s+lemma83PaperBeta D c (j+2)) /
            dirichletLFunction χ (1+s) *
              lemma83EulerCorrection χ (lemma83PaperBeta D c) j d r (1+s) := by
  have hs1 : 1 < (1+s).re := by simp only [Complex.add_re,Complex.one_re]; linarith
  have hdata := (lemma83_euler_is_continuation χ (lemma83PaperBeta D c)
    (lemma83_beta_re D c) j d r (mul_ne_zero hd.ne' hr.ne')).2 (1+s) hs1
  refine ⟨hdata.1,?_⟩
  have hne := lemma84_actual_L_ne_zero_right χ hs1
  apply (mul_left_cancel₀ hne)
  calc
    _ = lemma83EulerCorrection χ (lemma83PaperBeta D c) j d r (1+s) *
        dirichletLFunction χ (1+s+lemma83PaperBeta D c (j+1)) *
          dirichletLFunction χ (1+s+lemma83PaperBeta D c (j+2)) := hdata.2.symm
    _ = _ := by field_simp

end ZhangLS.Spec
