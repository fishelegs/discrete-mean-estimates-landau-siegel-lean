import ZhangLS.Spec.Lemma23ZeroData
import ZhangLS.Spec.Lemma23DirichletBranch

/-! # Lemma 2.3 for actual Dirichlet L-functions

The paper coefficient uses the derivative of the actual normalized
function M=YL. Branch existence is proved, and the conclusion holds for
every continuous square-root branch of the actual inverse gamma factor.
The only zero hypothesis is an L-function zero in the original smaller
window; simplicity, ordering and interval nonvanishing are conclusions.
-/

namespace ZhangLS.Spec

open Complex Set UpperHalfPlane

set_option maxHeartbeats 1000000

def Lemma23ActualBranch {p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (Y : ℂ → ℂ) : Prop :=
  ContinuousOn Y upperHalfPlaneSet ∧
    ∀ s ∈ upperHalfPlaneSet, Y s ^ 2 = (lemma23DirichletZ ψ s)⁻¹

/-- Exactly -i M(ρ+β₁)M(ρ+β₂)M(ρ+β₃)/M'(ρ). -/
noncomputable def lemma23ActualCoefficient {p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (Y : ℂ → ℂ) (D : ℕ) (c : ℝ) (ρ : ℂ) : ℂ :=
  lemma23ComplexCoefficient
    (lemma23DirichletNormalizedM ψ Y (criticalLinePoint ρ (lemma23PaperOffsetOne D c)))
    (lemma23DirichletNormalizedM ψ Y (criticalLinePoint ρ (lemma23PaperOffsetTwo D c)))
    (lemma23DirichletNormalizedM ψ Y (criticalLinePoint ρ (lemma23PaperOffsetThree D c)))
    (deriv (lemma23DirichletNormalizedM ψ Y) ρ)

theorem lemma23_actual_M_hasDerivAt_zero {p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : ψ.IsPrimitive) (hp : p ≠ 1)
    (Y : ℂ → ℂ) (hY : Lemma23ActualBranch ψ Y)
    {ρ : ℂ} (him : 0 < ρ.im) (hz : DirichletCharacter.LFunction ψ ρ = 0) :
    HasDerivAt (lemma23DirichletNormalizedM ψ Y)
      (Y ρ * deriv (DirichletCharacter.LFunction ψ) ρ) ρ := by
  have hZne := lemma23DirichletZ_ne_zero_of_im_pos ψ hψ hp him
  have hZd := (lemma23DirichletZ_differentiableAt_of_im_ne_zero ψ him.ne').hasDerivAt
  have hYd := lemma23_hasDerivAt_square_root_on_open isOpen_upperHalfPlaneSet
    him hY.1 hY.2 (hZd.inv hZne) (inv_ne_zero hZne)
  have hρne : ρ ≠ 1 := by
    intro he
    rw [he] at him
    norm_num at him
  have hLd := (lemma46_LFunction_analyticAt ψ hρne).differentiableAt.hasDerivAt
  exact hasDerivAt_lemma23NormalizedM_of_zero Y (DirichletCharacter.LFunction ψ)
    hYd hLd hz

theorem lemma23_actual_coefficient_nonneg_of_zero_data {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : ψ.IsPrimitive) (hp : p ≠ 1)
    (Y : ℂ → ℂ) (hY : Lemma23ActualBranch ψ Y) {c : ℝ} {ρ : ℂ}
    (hz : DirichletCharacter.LFunction ψ ρ = 0) (hdata : Lemma23ZeroDataAt ψ D c ρ) :
    deriv (lemma23DirichletNormalizedM ψ Y) ρ ≠ 0 ∧
      (lemma23ActualCoefficient ψ Y D c ρ).im = 0 ∧
      0 ≤ (lemma23ActualCoefficient ψ Y D c ρ).re := by
  have hd := lemma23_actual_M_hasDerivAt_zero ψ hψ hp Y hY hdata.positive_height hz
  have hYne := lemma23_square_root_ne_zero (hY.2 ρ hdata.positive_height)
    (lemma23DirichletZ_ne_zero_of_im_pos ψ hψ hp hdata.positive_height)
  have hc := lemma23_actual_dirichlet_coefficient_nonneg_of_branch ψ hψ hp ρ
    hdata.critical hdata.positive_height hdata.offset_order Y hY.1 hY.2
    hz hdata.simple hdata.first_interval hdata.third_interval
  refine ⟨by rw [hd.deriv]; exact mul_ne_zero hYne hdata.simple, ?_⟩
  simpa only [lemma23ActualCoefficient, hd.deriv] using hc

/-- The strict gap constant also defines the three original shifts.
The branch exists, and every valid branch gives the actual nonnegative
coefficient at every original smaller-window L-function zero. -/
def Lemma23Target : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ D₀ : ℕ, ∀ {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p),
    D₀ ≤ D → Lemma23InPsi1 χ ψ →
    (∀ ρ ρ' : ℂ, Proposition22ConsecutiveZeros χ ψ ρ ρ' →
      |ρ'.im - ρ.im - lemma44PaperAlpha D| <
        c * lemma44PaperAlpha D ^ 2 * lemma23PaperL D) ∧
    (∃ Y : ℂ → ℂ, Lemma23ActualBranch ψ Y) ∧
    (∀ Y : ℂ → ℂ, Lemma23ActualBranch ψ Y → ∀ ρ : ℂ,
      Lemma23InZeroWindow D ρ → DirichletCharacter.LFunction ψ ρ = 0 →
      deriv (lemma23DirichletNormalizedM ψ Y) ρ ≠ 0 ∧
        (lemma23ActualCoefficient ψ Y D c ρ).im = 0 ∧
        0 ≤ (lemma23ActualCoefficient ψ Y D c ρ).re)

theorem lemma23_proved : Lemma23Target := by
  obtain ⟨c, hc, D₀, hzero⟩ := lemma23_exists_uniform_actual_zero_data
  refine ⟨c, hc, D₀, ?_⟩
  intro D p hp χ ψ hD hψ
  have hd := hzero χ ψ hD hψ
  refine ⟨hd.1, lemma23_exists_continuous_actual_square_root ψ hψ.1.2.1 hψ.1.1.ne_one, ?_⟩
  intro Y hY ρ hρ hz
  exact lemma23_actual_coefficient_nonneg_of_zero_data ψ hψ.1.2.1 hψ.1.1.ne_one
    Y hY hz (hd.2 ρ hρ hz)

end ZhangLS.Spec
