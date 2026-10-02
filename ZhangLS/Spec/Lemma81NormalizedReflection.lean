import ZhangLS.Spec.Lemma52
import Mathlib.Analysis.Complex.Convex

/-! # Exact reflection of the actual normalized function in Lemma 8.1

No reflection identity is assumed for the Dirichlet L-function or its branch.
The functional equation gives real values on the critical line and analytic
continuation proves reflection throughout the upper half-plane.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex ComplexConjugate Metric Set UpperHalfPlane
open scoped Topology
set_option maxHeartbeats 2000000

lemma lemma81_analytic_critical_reflection (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f upperHalfPlaneSet)
    (hreal : ∀ s : ℂ, 0 < s.im → s.re = 1 / 2 → conj (f s) = f s)
    {s : ℂ} (hs : 0 < s.im) : f (1 - conj s) = conj (f s) := by
  let g : ℂ → ℂ := fun z => conj (f (1 - conj z))
  have hg : AnalyticOnNhd ℂ g upperHalfPlaneSet := by
    apply DifferentiableOn.analyticOnNhd _ isOpen_upperHalfPlaneSet
    intro z hz
    have hh : DifferentiableAt ℂ (fun w : ℂ => f (1 - w)) (conj z) := by
      exact (hf (1 - conj z) (by simpa using hz)).differentiableAt.comp (conj z)
        (differentiableAt_id.const_sub (1 : ℂ))
    have hg' := hh.conj_conj
    simpa only [Function.comp_def,conj_conj] using hg'.differentiableWithinAt
  have hline : ∀ z : ℂ, 0 < z.im → z.re = 1 / 2 → f z = g z := by
    intro z hz hre
    have hr : 1 - conj z = z := by
      apply Complex.ext <;> simp [hre]
      ring
    dsimp [g]
    rw [hr,hreal z hz hre]
  let z₀ : ℂ := ⟨1/2,1⟩
  have hmem : z₀ ∈ upperHalfPlaneSet := by change (0 : ℝ) < 1; norm_num
  have hclosure : z₀ ∈ closure ({z : ℂ | f z = g z} \ {z₀}) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    let z : ℂ := ⟨1/2,1+ε/2⟩
    refine ⟨z,⟨hline z (by dsimp [z]; linarith) rfl,?_⟩,?_⟩
    · intro he
      have hi := congrArg Complex.im (Set.mem_singleton_iff.mp he)
      dsimp [z,z₀] at hi
      linarith
    · rw [dist_eq_norm]
      have hd : z₀ - z = -Complex.I * ((ε/2 : ℝ) : ℂ) := by
        apply Complex.ext <;> simp [z₀,z]
      rw [hd,norm_mul,norm_neg,norm_I,one_mul,Complex.norm_real,
        Real.norm_of_nonneg (by positivity : 0 ≤ ε/2)]
      linarith
  have heq := hf.eqOn_of_preconnected_of_mem_closure hg
    (convex_halfSpace_im_gt (0 : ℝ)).isPreconnected hmem hclosure hs
  dsimp [g] at heq
  have hc := congrArg conj heq
  simpa only [conj_conj] using hc.symm

lemma lemma81_actual_M_analytic {p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : ψ.IsPrimitive) (hp : p ≠ 1)
    (Y : ℂ → ℂ) (hY : Lemma23ActualBranch ψ Y) :
    AnalyticOnNhd ℂ (lemma23DirichletNormalizedM ψ Y) upperHalfPlaneSet := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_upperHalfPlaneSet
  intro s hs
  have hYd := (lemma52_actual_branch_hasDerivAt ψ hψ hp Y hY hs).differentiableAt
  have hne : s ≠ 1 := by intro he; rw [he] at hs; simp at hs
  have hLd := (lemma46_LFunction_analyticAt ψ hne).differentiableAt
  exact (hYd.mul hLd).differentiableWithinAt

lemma lemma81_actual_M_critical_real {p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : ψ.IsPrimitive) (hp : p ≠ 1)
    (Y : ℂ → ℂ) (hY : Lemma23ActualBranch ψ Y) {s : ℂ}
    (hs : 0 < s.im) (hre : s.re = 1 / 2) :
    conj (lemma23DirichletNormalizedM ψ Y s) = lemma23DirichletNormalizedM ψ Y s := by
  have hψne : ψ ≠ 1 := by
    intro he
    have hc : ψ.conductor = p := hψ
    rw [he,DirichletCharacter.conductor_one] at hc
    exact hp hc.symm
  have hZne := lemma23DirichletZ_ne_zero_of_im_pos ψ hψ hp hs
  have hfe := lemma23_dirichletLFunction_functional_equation ψ hψ hp
    (lemma23_gammaFactor_ne_zero_of_re_pos ψ (by rw [hre]; norm_num))
    (lemma23_gammaFactor_ne_zero_of_re_pos ψ⁻¹ (by simp only [sub_re,one_re,hre]; norm_num))
  have hnorm := lemma23DirichletZ_norm_eq_one_on_critical_line ψ hψ hp hre
  have hYnorm := lemma23_Y_norm_eq_one_of_sq_eq_inv (hY.2 s hs) hnorm
  have hfactor : lemma23DirichletNormalizedM ψ Y s = Y s * ψ.LFunction s := rfl
  have hnormalized := lemma23_normalized_functional_equation hfactor hfe (hY.2 s hs) hZne
  have hr : conj (1-s) = s := by
    apply Complex.ext <;> simp [hre]
    ring
  have hconj : ψ⁻¹.LFunction (1-s) = conj (ψ.LFunction s) := by
    rw [dirichletLFunction_inv_eq_conj_at_conj ψ hψne,hr]
  exact Complex.conj_eq_iff_im.mpr
    (lemma23_M_value_real_of_functional_equation hfactor hnormalized hconj hYnorm)

/-- Reflection for every actual upper-half-plane square-root branch. -/
theorem lemma81_actual_M_reflection {p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : ψ.IsPrimitive) (hp : p ≠ 1)
    (Y : ℂ → ℂ) (hY : Lemma23ActualBranch ψ Y) {s : ℂ} (hs : 0 < s.im) :
    lemma23DirichletNormalizedM ψ Y (1 - conj s) =
      conj (lemma23DirichletNormalizedM ψ Y s) :=
  lemma81_analytic_critical_reflection (lemma23DirichletNormalizedM ψ Y)
    (lemma81_actual_M_analytic ψ hψ hp Y hY)
    (fun _z hz hre => lemma81_actual_M_critical_real ψ hψ hp Y hY hz hre) hs

/-- The actual normalized three-shift quotient is anti-real under critical
reflection. The only point restrictions are its original upper-half-plane
domain at the four evaluation points. -/
theorem lemma81_actual_normalized_quotient_reflection {p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : ψ.IsPrimitive) (hp : p ≠ 1)
    (Y : ℂ → ℂ) (hY : Lemma23ActualBranch ψ Y) {s : ℂ} (hs : 0 < s.im)
    (b₁ b₂ b₃ : ℝ) (h₁ : 0 < s.im + b₁) (h₂ : 0 < s.im + b₂)
    (h₃ : 0 < s.im + b₃) :
    (-Complex.I *
      (lemma23DirichletNormalizedM ψ Y (1 - conj s + Complex.I * (b₁ : ℂ)) *
        lemma23DirichletNormalizedM ψ Y (1 - conj s + Complex.I * (b₂ : ℂ)) *
        lemma23DirichletNormalizedM ψ Y (1 - conj s + Complex.I * (b₃ : ℂ))) /
      lemma23DirichletNormalizedM ψ Y (1 - conj s)) =
    -conj (-Complex.I *
      (lemma23DirichletNormalizedM ψ Y (s + Complex.I * (b₁ : ℂ)) *
        lemma23DirichletNormalizedM ψ Y (s + Complex.I * (b₂ : ℂ)) *
        lemma23DirichletNormalizedM ψ Y (s + Complex.I * (b₃ : ℂ))) /
      lemma23DirichletNormalizedM ψ Y s) := by
  have hshift (b : ℝ) (hb : 0 < s.im + b) :
      lemma23DirichletNormalizedM ψ Y (1 - conj s + Complex.I * (b : ℂ)) =
        conj (lemma23DirichletNormalizedM ψ Y (s + Complex.I * (b : ℂ))) := by
    have he : 1 - conj (s + Complex.I * (b : ℂ)) = 1 - conj s + Complex.I * (b : ℂ) := by
      simp
      ring
    simpa only [he] using lemma81_actual_M_reflection ψ hψ hp Y hY
      (s := s + Complex.I * (b : ℂ)) (by simpa using hb)
  rw [hshift b₁ h₁,hshift b₂ h₂,hshift b₃ h₃,
    lemma81_actual_M_reflection ψ hψ hp Y hY hs]
  simp only [map_div₀,map_mul,map_neg,Complex.conj_I]
  ring

end ZhangLS.Spec
