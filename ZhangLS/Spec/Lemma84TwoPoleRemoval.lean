import ZhangLS.Spec.Lemma84LogPerronSeries
import ZhangLS.Spec.ChiExceptionalRemoval
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Set
open scoped Topology
set_option maxHeartbeats 1500000

noncomputable def lemma84TwoPoleRemainder (N : ℂ → ℂ) (a b : ℂ) : ℂ → ℂ :=
  dslope (dslope (dslope N b) b) a

noncomputable def lemma84TwoPoleCoefficientA (N : ℂ → ℂ) (a b : ℂ) : ℂ :=
  N b/(a-b)^2+dslope N b b/(a-b)+dslope (dslope N b) b a
noncomputable def lemma84TwoPoleCoefficientB (N : ℂ → ℂ) (a b : ℂ) : ℂ :=
  -(N b/(a-b)^2)-dslope N b b/(a-b)
noncomputable def lemma84TwoPoleCoefficientC (N : ℂ → ℂ) (a b : ℂ) : ℂ :=
  -(N b/(a-b))

/-- Algebraic removal of two distinct poles, one simple and one double.
The remainder is an actual iterated divided difference of the numerator. -/
lemma lemma84_two_pole_decomposition (N : ℂ → ℂ) (a b s : ℂ)
    (hab : a ≠ b) (hsa : s ≠ a) (hsb : s ≠ b) :
    N s/((s-a)*(s-b)^2) =
      lemma84TwoPoleCoefficientA N a b/(s-a) +
        lemma84TwoPoleCoefficientB N a b/(s-b) +
          lemma84TwoPoleCoefficientC N a b/(s-b)^2 + lemma84TwoPoleRemainder N a b s := by
  have h1 := sub_smul_dslope N b s
  have h2 := sub_smul_dslope (dslope N b) b s
  have h3 := sub_smul_dslope (dslope (dslope N b) b) a s
  simp only [smul_eq_mul] at h1 h2 h3
  have hn : N s = N b+(s-b)*dslope N b b +
      (s-b)^2*(dslope (dslope N b) b a+(s-a)*lemma84TwoPoleRemainder N a b s) := by
    unfold lemma84TwoPoleRemainder
    linear_combination -h1-(s-b)*h2-(s-b)^2*h3
  rw [hn]
  unfold lemma84TwoPoleCoefficientA lemma84TwoPoleCoefficientB lemma84TwoPoleCoefficientC
  field_simp [sub_ne_zero.mpr hab,sub_ne_zero.mpr hsa,sub_ne_zero.mpr hsb]
  ring

lemma lemma84_two_pole_remainder_differentiableOn (N : ℂ → ℂ) {S : Set ℂ}
    (hN : DifferentiableOn ℂ N S) (a b : ℂ) (ha : S ∈ nhds a) (hb : S ∈ nhds b) :
    DifferentiableOn ℂ (lemma84TwoPoleRemainder N a b) S := by
  exact (Complex.differentiableOn_dslope ha).mpr
    ((Complex.differentiableOn_dslope hb).mpr ((Complex.differentiableOn_dslope hb).mpr hN))

/-- Genuine numerator after removing the actual exceptional zero. -/
noncomputable def lemma84ActualTwoPoleNumerator {D : ℕ} (χ : RealPrimitiveCharacter D)
    (ρ : ℝ) (a b : ℂ) (U : ℂ → ℂ) (x : ℝ) (s : ℂ) : ℂ :=
  dirichletLFunction χ (1+s+a)*dirichletLFunction χ (1+s+b)*U (1+s)*(x:ℂ)^s*
    (s-((ρ:ℂ)-1)+1)/chiExceptionalRemoved χ ρ (1+s)

lemma lemma84_actual_reciprocal_factorization {D : ℕ} (χ : RealPrimitiveCharacter D)
    {ρ : ℝ} (hzero : dirichletLFunction χ (ρ:ℂ)=0) (s : ℂ)
    (hL : dirichletLFunction χ (1+s) ≠ 0)
    (hG : chiExceptionalRemoved χ ρ (1+s) ≠ 0) (hs : s ≠ (ρ:ℂ)-1) :
    (dirichletLFunction χ (1+s))⁻¹ =
      (s-((ρ:ℂ)-1)+1)/((s-((ρ:ℂ)-1))*chiExceptionalRemoved χ ρ (1+s)) := by
  have hh := chi_exceptional_removed_factorization χ hzero (1+s)
  have he : 1+s-(ρ:ℂ) = s-((ρ:ℂ)-1) := by ring
  rw [he] at hh
  apply (eq_div_iff (mul_ne_zero (sub_ne_zero.mpr hs) hG)).mpr
  rw [hh]
  field_simp

lemma lemma84_actual_integrand_two_pole_factorization {D : ℕ} (χ : RealPrimitiveCharacter D)
    {ρ : ℝ} (hzero : dirichletLFunction χ (ρ:ℂ)=0) (a b m : ℂ) (U : ℂ → ℂ) (x : ℝ)
    (s : ℂ) (hL : dirichletLFunction χ (1+s) ≠ 0)
    (hG : chiExceptionalRemoved χ ρ (1+s) ≠ 0) (hs : s ≠ (ρ:ℂ)-1) :
    lemma84AnalyticCircleIntegrand χ a b m U x s =
      lemma84ActualTwoPoleNumerator χ ρ a b U x s/((s-((ρ:ℂ)-1))*(s-(-m))^2) := by
  unfold lemma84AnalyticCircleIntegrand lemma84ActualTwoPoleNumerator
  simp only [div_eq_mul_inv]
  rw [lemma84_actual_reciprocal_factorization χ hzero s hL hG hs]
  simp only [sub_neg_eq_add,div_eq_mul_inv,mul_inv]
  ring

lemma lemma84_actual_two_pole_numerator_differentiableOn {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) {ρ : ℝ} (hρ : ρ ≤ 1)
    (hzero : dirichletLFunction χ (ρ:ℂ)=0) (hsimple : deriv (dirichletLFunction χ) (ρ:ℂ) ≠ 0)
    (hunique : ∀ z : ℂ, Lemma55InZeroRegion D z → dirichletLFunction χ z=0 → z=(ρ:ℂ))
    (a b : ℂ) (U : ℂ → ℂ) (hU : AnalyticOnNhd ℂ U {z : ℂ | 9/10 < z.re})
    {x : ℝ} (hx : 0 < x) {S : Set ℂ}
    (hS : ∀ s ∈ S, 9/10 < (1+s).re ∧ Lemma55InZeroRegion D (1+s)) :
    DifferentiableOn ℂ (lemma84ActualTwoPoleNumerator χ ρ a b U x) S := by
  have hLd := differentiable_dirichletLFunction_of_one_lt_modulus χ hD
  have hGd := chi_exceptional_removed_differentiable χ hD ρ
  intro s hs
  apply DifferentiableAt.differentiableWithinAt
  unfold lemma84ActualTwoPoleNumerator
  apply DifferentiableAt.div
  · apply DifferentiableAt.mul
    · apply DifferentiableAt.mul
      · exact (((hLd _).comp s (by fun_prop)).mul ((hLd _).comp s (by fun_prop))).mul
          ((hU _ (hS s hs).1).differentiableAt.comp s (by fun_prop))
      · exact (Complex.hasStrictDerivAt_const_cpow (y := s)
          (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))).hasDerivAt.differentiableAt
    · fun_prop
  · exact (hGd _).comp s (by fun_prop)
  · exact chi_exceptional_removed_ne_zero χ hρ hzero hsimple hunique (hS s hs).2
      (by linarith only [(hS s hs).1])

end ZhangLS.Spec
