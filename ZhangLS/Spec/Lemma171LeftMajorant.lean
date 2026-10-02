import ZhangLS.Spec.Lemma171CorrectionBounds

set_option autoImplicit false
namespace ZhangLS.Spec

noncomputable def lemma171LeftMajorant (D : ℕ) : ℝ :=
  ((2*Real.pi)⁻¹)*(4*64^2*lemma32RegularProductBound (3/4)*(D:ℝ)^4)*
    Real.exp (-(lemma23PaperL D^(11/10:ℝ))/4+1/(64*lemma23PaperL D^30))*
    (1+16*lemma23PaperL D^30)^2*Real.sqrt (8*Real.pi*lemma23PaperL D^30)

end ZhangLS.Spec
