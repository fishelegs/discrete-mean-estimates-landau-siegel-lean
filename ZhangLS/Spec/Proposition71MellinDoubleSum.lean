import ZhangLS.Spec.Proposition71MellinFiniteSum

/-! # Exact two-finite-sum Mellin factorization for Sections 7 and 14

Every interchange uses actual integrability. The full (hr)^s factor is
retained, and the two finite Dirichlet polynomials remain genuine sums.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Finset
open scoped Classical Topology
set_option maxHeartbeats 2000000

lemma proposition71_positive_ratio_cpow {u v : ℝ} (hu : 0<u) (hv : 0<v) (s : ℂ) :
    ((u/v : ℝ) : ℂ)^s=(u : ℂ)^s*(v : ℂ)^(-s) := by
  have hvarg : (v : ℂ).arg≠Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hv.le]
    exact Real.pi_ne_zero.symm
  calc
    _=((u : ℂ)*((v⁻¹ : ℝ) : ℂ))^s := by congr 1; push_cast; ring
    _=(u : ℂ)^s*((v⁻¹ : ℝ) : ℂ)^s :=
      Complex.mul_cpow_ofReal_nonneg hu.le (inv_nonneg.mpr hv.le) s
    _=_ := by rw [Complex.ofReal_inv,Complex.inv_cpow _ _ hvarg,Complex.cpow_neg]

/-- Absolute integrability of the actual one-finite-sum inverse transform. -/
theorem proposition71_finite_mellin_integrand_integrable {D : ℕ}
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) {σ h r l : ℝ}
    (hσ : 1/2≤σ) (hh : 0<h) (hr : 0<r) (hl : 0<l)
    (S : Finset ℕ) (hS : ∀ p∈S, 0<p) (a : ℕ → ℂ) :
    Integrable (fun t : ℝ =>
      lemma54PaperDeltaMellin D ((σ : ℂ)+(t : ℂ)*I)*
        ((h*r/l : ℝ) : ℂ)^((σ : ℂ)+(t : ℂ)*I)*
          ∑ p∈S, a p*(p : ℂ)^((σ : ℂ)+(t : ℂ)*I)) := by
  let F : ℕ → ℝ → ℂ := fun p t =>
    a p*((l/((p : ℝ)*h*r) : ℝ) : ℂ)^(-((σ : ℂ)+(t : ℂ)*I))*
      lemma54PaperDeltaMellin D ((σ : ℂ)+(t : ℂ)*I)
  have hF (p : ℕ) (hp : p∈S) : Integrable (F p) := by
    have hp' : 0<(p : ℝ) := by exact_mod_cast hS p hp
    have hi := proposition71_inverse_mellin_integrand_integrable hD hL hσ
      (by positivity : 0<l/((p : ℝ)*h*r))
    simpa only [F,mul_assoc] using hi.const_mul (a p)
  apply (integrable_finsetSum S hF).congr
  apply ae_of_all
  intro t
  dsimp only
  rw [mul_sum]
  apply sum_congr rfl
  intro p hp
  dsimp [F]
  rw [proposition71_scaled_mellin_power (by exact_mod_cast hS p hp) hh hr hl]
  simp only [Complex.ofReal_natCast]
  ring

noncomputable def proposition71DoubleMellinIntegrand (D : ℕ) (σ h r : ℝ)
    (L P : Finset ℕ) (b a : ℕ → ℂ) (t : ℝ) : ℂ :=
  lemma54PaperDeltaMellin D ((σ : ℂ)+(t : ℂ)*I)*
    ((h*r : ℝ) : ℂ)^((σ : ℂ)+(t : ℂ)*I)*
      (∑ l∈L, b l*(l : ℂ)^(-((σ : ℂ)+(t : ℂ)*I)))*
      (∑ p∈P, a p*(p : ℂ)^((σ : ℂ)+(t : ℂ)*I))

lemma proposition71_double_mellin_integrand_expansion (D : ℕ) (σ : ℝ)
    {h r : ℝ} (hh : 0<h) (hr : 0<r)
    (L P : Finset ℕ) (hL : ∀l∈L, 0<l) (b a : ℕ → ℂ) (t : ℝ) :
    proposition71DoubleMellinIntegrand D σ h r L P b a t=
      ∑ l∈L, b l*(lemma54PaperDeltaMellin D ((σ : ℂ)+(t : ℂ)*I)*
        ((h*r/(l : ℝ) : ℝ) : ℂ)^((σ : ℂ)+(t : ℂ)*I)*
          ∑ p∈P, a p*(p : ℂ)^((σ : ℂ)+(t : ℂ)*I)) := by
  unfold proposition71DoubleMellinIntegrand
  conv_lhs => arg 1; rw [mul_sum]
  rw [sum_mul]
  apply sum_congr rfl
  intro l hl
  rw [proposition71_positive_ratio_cpow (mul_pos hh hr) (by exact_mod_cast hL l hl)]
  simp only [Complex.ofReal_natCast]
  ring

/-- Absolute integrability of the complete factored two-polynomial kernel. -/
theorem proposition71_double_mellin_integrand_integrable {D : ℕ}
    (hD : 1<D) (hlog : 2000≤lemma23PaperL D) {σ h r : ℝ}
    (hσ : 1/2≤σ) (hh : 0<h) (hr : 0<r)
    (L P : Finset ℕ) (hL : ∀l∈L, 0<l) (hP : ∀p∈P, 0<p) (b a : ℕ → ℂ) :
    Integrable (proposition71DoubleMellinIntegrand D σ h r L P b a) := by
  have hs : Integrable (fun t : ℝ =>
      ∑ l∈L, b l*(lemma54PaperDeltaMellin D ((σ : ℂ)+(t : ℂ)*I)*
        ((h*r/(l : ℝ) : ℝ) : ℂ)^((σ : ℂ)+(t : ℂ)*I)*
          ∑ p∈P, a p*(p : ℂ)^((σ : ℂ)+(t : ℂ)*I))) := by
    apply integrable_finsetSum
    intro l hl
    exact (proposition71_finite_mellin_integrand_integrable hD hlog hσ hh hr
      (by exact_mod_cast hL l hl) P hP a).const_mul (b l)
  apply hs.congr
  exact ae_of_all _ (fun t => (proposition71_double_mellin_integrand_expansion D σ hh hr L P hL b a t).symm)

/-- Exact two-finite-sum Mellin factorization. This is the common Section7/14
large-conductor bridge; all scaling and both finite polynomials are explicit. -/
theorem proposition71_actual_double_mellin_sum {D : ℕ}
    (hD : 1<D) (hlog : 2000≤lemma23PaperL D) {σ h r : ℝ}
    (hσ : 1/2≤σ) (hh : 0<h) (hr : 0<r)
    (L P : Finset ℕ) (hL : ∀l∈L, 0<l) (hP : ∀p∈P, 0<p) (b a : ℕ → ℂ) :
    (∑ l∈L, b l*∑ p∈P, a p*lemma53PaperDelta D ((l : ℝ)/((p : ℝ)*h*r)))=
      ((1/(2*Real.pi) : ℝ) : ℂ)*∫ t : ℝ,
        proposition71DoubleMellinIntegrand D σ h r L P b a t := by
  let F : ℕ → ℝ → ℂ := fun l t =>
    lemma54PaperDeltaMellin D ((σ : ℂ)+(t : ℂ)*I)*
      ((h*r/(l : ℝ) : ℝ) : ℂ)^((σ : ℂ)+(t : ℂ)*I)*
        ∑ p∈P, a p*(p : ℂ)^((σ : ℂ)+(t : ℂ)*I)
  have hF (l : ℕ) (hl : l∈L) : Integrable (F l) :=
    proposition71_finite_mellin_integrand_integrable hD hlog hσ hh hr
      (by exact_mod_cast hL l hl) P hP a
  calc
    _=∑ l∈L, ((1/(2*Real.pi) : ℝ) : ℂ)*∫t : ℝ, b l*F l t := by
      apply sum_congr rfl
      intro l hl
      rw [proposition71_actual_finite_mellin_sum hD hlog hσ hh hr
        (by exact_mod_cast hL l hl) P hP a,integral_const_mul]
      dsimp [F]
      ring
    _=((1/(2*Real.pi) : ℝ) : ℂ)*∫t : ℝ, ∑ l∈L, b l*F l t := by
      rw [←mul_sum,integral_finsetSum L (fun l hl => (hF l hl).const_mul (b l))]
    _=_ := by
      congr 1
      apply integral_congr_ae
      exact ae_of_all _ (fun t => (proposition71_double_mellin_integrand_expansion D σ hh hr L P hL b a t).symm)

end ZhangLS.Spec
