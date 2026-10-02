import ZhangLS.Spec.Lemma81ContourReflection

/-! # Analyticity of the actual Lemma 8.1 numerator and integrands

The numerator is assembled from the actual shifted normalized L-functions,
finite Dirichlet polynomials and original Gaussian. This is the common
analytic input for contour integrability and the actual simple-zero residues.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex ComplexConjugate Set MeasureTheory Filter
open scoped Real Topology
set_option maxHeartbeats 2000000

lemma lemma81_polynomial_differentiable {p : ℕ} (D : ℕ) (a : ℕ → ℂ)
    (ψ : DirichletCharacter ℂ p) : Differentiable ℂ (lemma81Polynomial D a ψ) := by
  unfold lemma81Polynomial
  apply Differentiable.fun_sum
  intro n hn
  have hnpos : 0 < n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hnpos)
  have hd : Differentiable ℂ (fun s : ℂ => (n : ℂ)^s) := by
    intro s
    exact differentiableAt_id.const_cpow (Or.inl hn0)
  exact (differentiable_const _).div hd (fun _ => Complex.cpow_ne_zero_iff.mpr (Or.inl hn0))

lemma lemma81_omega_differentiable (D : ℕ) : Differentiable ℂ (lemma81Omega D) := by
  unfold lemma81Omega
  fun_prop

noncomputable def lemma81TildeNumerator {p : ℕ} [NeZero p]
    (D : ℕ) (c : ℝ) (ψ : DirichletCharacter ℂ p) (Y : ℂ → ℂ)
    (a₁ a₂ : ℕ → ℂ) (s : ℂ) : ℂ :=
  (-I * (lemma23DirichletNormalizedM ψ Y (s + lemma52PaperBetaOne D c) *
    lemma23DirichletNormalizedM ψ Y (s + lemma52PaperBetaTwo D c) *
    lemma23DirichletNormalizedM ψ Y (s + lemma52PaperBetaThree D c))) *
    lemma81Polynomial D a₁ ψ s * lemma81Polynomial D a₂ ψ⁻¹ (1-s) * lemma81Omega D s

lemma lemma81_tilde_integrand_eq_numerator_div {p : ℕ} [NeZero p]
    (D : ℕ) (c : ℝ) (ψ : DirichletCharacter ℂ p) (Y : ℂ → ℂ)
    (a₁ a₂ : ℕ → ℂ) (s : ℂ) :
    lemma81TildeIntegrand D c ψ Y a₁ a₂ s =
      lemma81TildeNumerator D c ψ Y a₁ a₂ s / lemma23DirichletNormalizedM ψ Y s := by
  unfold lemma81TildeIntegrand lemma81TildeNumerator lemma81ActualCtilde
  ring

lemma lemma81_actual_tilde_numerator_analyticAt {D p : ℕ} [NeZero p]
    (c : ℝ) (ψ : DirichletCharacter ℂ p) (hψ : ψ.IsPrimitive) (hp : p ≠ 1)
    (Y : ℂ → ℂ) (hY : Lemma23ActualBranch ψ Y) (a₁ a₂ : ℕ → ℂ) {s : ℂ}
    (h₁ : 0 < s.im + lemma23PaperOffsetOne D c)
    (h₂ : 0 < s.im + lemma23PaperOffsetTwo D c)
    (h₃ : 0 < s.im + lemma23PaperOffsetThree D c) :
    AnalyticAt ℂ (lemma81TildeNumerator D c ψ Y a₁ a₂) s := by
  have hM := lemma81_actual_M_analytic ψ hψ hp Y hY
  have hM₁ : AnalyticAt ℂ (fun z => lemma23DirichletNormalizedM ψ Y (z+lemma52PaperBetaOne D c)) s :=
    (hM _ (by simpa [lemma52PaperBetaOne] using h₁)).comp (by fun_prop)
  have hM₂ : AnalyticAt ℂ (fun z => lemma23DirichletNormalizedM ψ Y (z+lemma52PaperBetaTwo D c)) s :=
    (hM _ (by simpa [lemma52PaperBetaTwo] using h₂)).comp (by fun_prop)
  have hM₃ : AnalyticAt ℂ (fun z => lemma23DirichletNormalizedM ψ Y (z+lemma52PaperBetaThree D c)) s :=
    (hM _ (by simpa [lemma52PaperBetaThree] using h₃)).comp (by fun_prop)
  have hA₁ := (lemma81_polynomial_differentiable D a₁ ψ).analyticAt s
  have hA₂ := ((lemma81_polynomial_differentiable D a₂ ψ⁻¹).analyticAt (1-s)).comp
    (show AnalyticAt ℂ (fun z : ℂ => 1-z) s by fun_prop)
  have hω := (lemma81_omega_differentiable D).analyticAt s
  exact (((analyticAt_const.mul ((hM₁.mul hM₂).mul hM₃)).mul hA₁).mul hA₂).mul hω

lemma lemma81_actual_tilde_integrand_analyticAt {D p : ℕ} [NeZero p]
    (c : ℝ) (ψ : DirichletCharacter ℂ p) (hψ : ψ.IsPrimitive) (hp : p ≠ 1)
    (Y : ℂ → ℂ) (hY : Lemma23ActualBranch ψ Y) (a₁ a₂ : ℕ → ℂ) {s : ℂ}
    (hs : 0 < s.im) (hMne : lemma23DirichletNormalizedM ψ Y s ≠ 0)
    (h₁ : 0 < s.im + lemma23PaperOffsetOne D c)
    (h₂ : 0 < s.im + lemma23PaperOffsetTwo D c)
    (h₃ : 0 < s.im + lemma23PaperOffsetThree D c) :
    AnalyticAt ℂ (lemma81TildeIntegrand D c ψ Y a₁ a₂) s := by
  have he : lemma81TildeIntegrand D c ψ Y a₁ a₂ = fun z =>
      lemma81TildeNumerator D c ψ Y a₁ a₂ z / lemma23DirichletNormalizedM ψ Y z := by
    funext z
    exact lemma81_tilde_integrand_eq_numerator_div D c ψ Y a₁ a₂ z
  rw [he]
  exact (lemma81_actual_tilde_numerator_analyticAt c ψ hψ hp Y hY a₁ a₂ h₁ h₂ h₃).div
    (lemma81_actual_M_analytic ψ hψ hp Y hY s hs) hMne

/-- Analyticity of the unnormalized actual C-kernel wherever the original
L-denominator is nonzero and all four points are in its upper-half-plane domain. -/
lemma lemma81_actual_C_analyticAt {D p : ℕ} [NeZero p]
    (c : ℝ) (ψ : DirichletCharacter ℂ p) (hψ : ψ.IsPrimitive) (hp : p ≠ 1)
    {s : ℂ} (hs : 0 < s.im) (hLne : ψ.LFunction s ≠ 0)
    (h₁ : 0 < s.im + lemma23PaperOffsetOne D c)
    (h₂ : 0 < s.im + lemma23PaperOffsetTwo D c)
    (h₃ : 0 < s.im + lemma23PaperOffsetThree D c) :
    AnalyticAt ℂ (lemma81ActualC D c ψ) s := by
  have hL (z : ℂ) (hz : 0 < z.im) : AnalyticAt ℂ ψ.LFunction z :=
    lemma46_LFunction_analyticAt ψ (by intro he; rw [he] at hz; simp at hz)
  have hL₁ : AnalyticAt ℂ (fun z => ψ.LFunction (z+lemma52PaperBetaOne D c)) s :=
    (hL _ (by simpa [lemma52PaperBetaOne] using h₁)).comp (by fun_prop)
  have hL₂ : AnalyticAt ℂ (fun z => ψ.LFunction (z+lemma52PaperBetaTwo D c)) s :=
    (hL _ (by simpa [lemma52PaperBetaTwo] using h₂)).comp (by fun_prop)
  have hL₃ : AnalyticAt ℂ (fun z => ψ.LFunction (z+lemma52PaperBetaThree D c)) s :=
    (hL _ (by simpa [lemma52PaperBetaThree] using h₃)).comp (by fun_prop)
  have hZ : AnalyticAt ℂ (lemma23DirichletZ ψ) s := by
    have hd : DifferentiableOn ℂ (lemma23DirichletZ ψ) {z : ℂ | 0 < z.im} := by
      intro z hz
      exact (lemma23DirichletZ_differentiableAt_of_im_ne_zero ψ hz.ne').differentiableWithinAt
    exact (hd.analyticOnNhd UpperHalfPlane.isOpen_upperHalfPlaneSet) s hs
  exact (analyticAt_const.mul
    (hZ.inv (lemma23DirichletZ_ne_zero_of_im_pos ψ hψ hp hs))).mul
    (((hL₁.mul hL₂).mul hL₃).div (hL s hs) hLne)

end ZhangLS.Spec
