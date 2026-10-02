import ZhangLS.Spec.Lemma162Definitions
import ZhangLS.Spec.Lemma171Residue
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-! Conditional diagnostic, not a proved Euler continuation for actual varpi.
Given the genuine shifted Dirichlet identity on Re(s)>1, *any* continuous
extension of the printed quotient must vanish at 1. We approach 1 through
ordinary convergent points. No totalized zeta value or nonsummable tsum at
its pole is evaluated. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Filter
open scoped Topology
set_option maxHeartbeats 1000000

noncomputable def lemma162RegularOldExtension {D : ℕ} (χ : RealPrimitiveCharacter D)
    (γ : ℂ) (V : ℂ → ℂ) (s : ℂ) : ℂ :=
  (s-1)*V s*riemannZeta (s-γ)*dirichletLFunction χ (s-γ)^2 /
    (zetaPoleRemoved s*dirichletLFunction χ s^2)

lemma lemma162_regular_old_extension_at_one {D : ℕ} (χ : RealPrimitiveCharacter D)
    (γ : ℂ) (V : ℂ → ℂ) : lemma162RegularOldExtension χ γ V 1 = 0 := by
  simp [lemma162RegularOldExtension]

lemma lemma162_regular_old_extension_continuous {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (γ : ℂ) (hγ : γ ≠ 0) (V : ℂ → ℂ) (hV : ContinuousAt V 1) :
    ContinuousAt (lemma162RegularOldExtension χ γ V) 1 := by
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  have hL := (differentiable_dirichletLFunction_of_one_lt_modulus χ hD).continuous
  have hL1 : dirichletLFunction χ 1 ≠ 0 := by
    exact DirichletCharacter.LFunction_apply_one_ne_zero
      (χ.nontrivial_of_one_lt_modulus hD)
  have hshift : ContinuousAt (fun s : ℂ => s-γ) 1 := by fun_prop
  have hζ : ContinuousAt (fun s : ℂ => riemannZeta (s-γ)) 1 :=
    (differentiableAt_riemannZeta (by intro h; apply hγ; linear_combination -h)).continuousAt.comp hshift
  have hLp : ContinuousAt (fun s : ℂ => dirichletLFunction χ (s-γ)) 1 :=
    hL.continuousAt.comp hshift
  have hz := (lemma32_zeta_pole_removed_differentiableAt (by norm_num : 0<(1:ℂ).re)).continuousAt
  unfold lemma162RegularOldExtension
  exact ((((continuousAt_id.sub continuousAt_const).mul hV).mul hζ).mul (hLp.pow 2)).div
    (hz.mul (hL.continuousAt.pow 2))
    (by simpa [lemma55_actual_zeta_pole_removed_at_one] using pow_ne_zero 2 hL1)

/-- Algebra only on the genuine absolute-convergence half-plane. -/
lemma lemma162_regular_old_extension_eq_quotient {D : ℕ} (χ : RealPrimitiveCharacter D)
    (γ : ℂ) (V : ℂ → ℂ) (s : ℂ) (hs : 1<s.re) :
    lemma162RegularOldExtension χ γ V s =
      (V s*riemannZeta s^2*riemannZeta (s-γ)*dirichletLFunction χ s*
        dirichletLFunction χ (s-γ)^2)/(riemannZeta s^3*dirichletLFunction χ s^3) := by
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hl : dirichletLFunction χ s ≠ 0 := by
    unfold dirichletLFunction
    rw [DirichletCharacter.LFunction_eq_LSeries χ.chi hs]
    exact DirichletCharacter.LSeries_ne_zero_of_one_lt_re χ.chi hs
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; norm_num at hs
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have hsm : s-1 ≠ 0 := sub_ne_zero.mpr hs1
  unfold lemma162RegularOldExtension
  rw [zetaPoleRemoved_eq_mul_riemannZeta hs0 hs1]
  field_simp [hz,hl,hsm]

/-- A real sequence stays inside Re(s)>1 and approaches 1; this fixes which
side of the actual convergent Dirichlet series the witness uses. -/
noncomputable def lemma162Approach (n : ℕ) : ℂ := 1 + (1/((n:ℝ)+1):ℝ)

lemma lemma162_approach_re (n : ℕ) : 1 < (lemma162Approach n).re := by
  simp only [lemma162Approach,Complex.add_re,Complex.one_re,Complex.ofReal_re]
  have h : (0:ℝ)<1/((n:ℝ)+1) := by positivity
  linarith

lemma lemma162_approach_tendsto : Tendsto lemma162Approach atTop (𝓝 (1:ℂ)) := by
  have h : Tendsto (fun n : ℕ => (1/((n:ℝ)+1):ℝ)) atTop (𝓝 (0:ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp h
  simpa only [lemma162Approach,Complex.ofReal_zero,add_zero] using
    tendsto_const_nhds.add hc

/-- Honest limit witness. `hidentity` is exactly the still-required actual
shifted Dirichlet/Euler bridge, isolated as a condition rather than asserted.
Every continuous extension U of the literal quotient then has U(1)=0. -/
theorem lemma162_original_value_forced_zero {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (γ : ℂ) (hγ : γ ≠ 0) (U V F : ℂ → ℂ)
    (hU : ContinuousAt U 1) (hV : ContinuousAt V 1)
    (hidentity : ∀ s : ℂ, 1<s.re →
      F s = V s*riemannZeta s^2*riemannZeta (s-γ)*dirichletLFunction χ s*
        dirichletLFunction χ (s-γ)^2)
    (hquotient : ∀ s : ℂ, 1<s.re → U s = F s/(riemannZeta s^3*dirichletLFunction χ s^3)) :
    U 1 = 0 := by
  have hlimU : Tendsto (fun n => U (lemma162Approach n)) atTop (𝓝 (U 1)) :=
    hU.tendsto.comp lemma162_approach_tendsto
  have hlimR : Tendsto (fun n => lemma162RegularOldExtension χ γ V (lemma162Approach n))
      atTop (𝓝 (0:ℂ)) := by
    simpa only [lemma162_regular_old_extension_at_one] using
      (lemma162_regular_old_extension_continuous χ hD γ hγ V hV).tendsto.comp
        lemma162_approach_tendsto
  have he : (fun n => U (lemma162Approach n)) =
      (fun n => lemma162RegularOldExtension χ γ V (lemma162Approach n)) := by
    funext n
    rw [hquotient _ (lemma162_approach_re n),hidentity _ (lemma162_approach_re n),
      lemma162_regular_old_extension_eq_quotient χ γ V _ (lemma162_approach_re n)]
  rw [he] at hlimU
  exact tendsto_nhds_unique hlimU hlimR

end ZhangLS.Spec
