import ZhangLS.Spec.Proposition71FrontUniformRate
import ZhangLS.Spec.Lemma81FiniteZerosReflection

/-! # Exact original-contour interpretation of the common front transform -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex
set_option maxHeartbeats 1500000

noncomputable def proposition71FrontActualKernel {N : ℕ} [NeZero N] (D : ℕ)
    (θ : DirichletCharacter ℂ N) (c : ℕ → ℂ) (S : Finset ℕ) (a : ℕ → ℂ) (s : ℂ) : ℂ :=
  (lemma23DirichletZ θ s)⁻¹*LSeries c s*
    (∑n∈S, a n*(n : ℂ)^(s-1))*lemma81Omega D s

lemma proposition71_front_omega_exact (D : ℕ) (s : ℂ) :
    lemma81Omega D s=lemma53PaperOmega D s := by
  unfold lemma81Omega lemma53PaperOmega lemma53PaperScale
  push_cast
  rfl

lemma proposition71_front_segment_point_exact (D : ℕ) (u : ℝ) :
    lemma81SegmentPoint D 1 u=(3/2 : ℂ)+((u+(lemma23PaperCenter D).im : ℝ) : ℂ)*I := by
  have hcenter : lemma23PaperCenter D=(1/2 : ℂ)+((lemma23PaperCenter D).im : ℂ)*I := by
    conv_lhs => rw [←Complex.re_add_im (lemma23PaperCenter D)]
    congr 1
    norm_num [lemma23PaperCenter]
  unfold lemma81SegmentPoint
  conv_lhs => rw [hcenter]
  push_cast
  ring

/-- The shared front integral is exactly the original upward J(1), with its
original Gaussian and 1/(2πi) normalization. -/
theorem proposition71_front_original_contour_exact {N : ℕ} [NeZero N] (D : ℕ)
    (θ : DirichletCharacter ℂ N) (c : ℕ → ℂ) (S : Finset ℕ) (a : ℕ → ℂ) :
    lemma81NormalizedSegmentIntegral D 1 (proposition71FrontActualKernel D θ c S a)=
      proposition71FrontSegmentIntegral D θ c S a := by
  unfold lemma81NormalizedSegmentIntegral proposition71FrontSegmentIntegral
  have hnorm : ((2*Real.pi : ℝ) : ℂ)⁻¹=(((1/(2*Real.pi) : ℝ) : ℂ)) := by push_cast; ring
  rw [hnorm]
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  dsimp only
  rw [proposition71_front_segment_point_exact]
  simp only [proposition71FrontActualKernel,proposition71FrontActualIntegrand,
    proposition71_front_omega_exact]

end ZhangLS.Spec
