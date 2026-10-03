import ZhangLS.Spec.AppendixBTailGaussianSplit
import ZhangLS.Spec.AppendixBTailFloorGeometry
import ZhangLS.Spec.AppendixBTailOriginalRange

/-! Genuine pointwise-in-z unsmoothing of the full Gaussian source into the
actual finite sharp source, uniformly for positive l1<T. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace ZhangLS.Spec
open Complex MeasureTheory Finset Filter Set
open scoped Classical

noncomputable def appendixBSingleUnsmoothingBudget (D : ℕ) : ℝ :=
  appendixBCutoffUnsmoothingBudget D (lemma23PaperL D) (lemma56PaperT D)+
    lemma44InverseSquareMass*Real.exp (-(lemma23PaperL D^10))

lemma appendixB_finite_gaussian_sharp_error {D : ℕ} (hD : 1<D)
    (hL : 0<lemma23PaperL D) {β γ : ℂ}
    (hβre : β.re=0) (hβ : ‖β‖≤3*lemma44PaperAlpha D) (hγ : γ.re=0)
    {l₁ : ℕ} (hl : 0<l₁) (z : ℝ) :
    ‖appendixBFiniteGaussianSourceSlice D β γ l₁ ⌊lemma23PaperP D⌋₊ z-
      appendixBSharpSourceSlice D β γ l₁ ⌊lemma23PaperP D⌋₊ z‖≤
      appendixBCutoffUnsmoothingBudget D (lemma23PaperL D)
        (Real.exp (z*lemma23PaperL D^9)/(l₁ : ℝ))+
      appendixBCutoffUnsmoothingBudget D (lemma23PaperL D)
        (Real.exp (0.5*lemma23PaperL D^9)/(l₁ : ℝ)) := by
  let S := Finset.Icc 1 ⌊lemma23PaperP D⌋₊
  let X := lemma151P1 D/(l₁ : ℝ)
  let x := Real.exp (0.5*lemma23PaperL D^9)/(l₁ : ℝ)
  let y := Real.exp (z*lemma23PaperL D^9)/(l₁ : ℝ)
  let a := appendixBRhoMonomialCoefficient X β γ
  let E₁ := ∑ n∈S, a n*((zhangGaussianWeight D (y/n)-(if (n : ℝ)<y then 1 else 0) : ℝ) : ℂ)
  let E₂ := ∑ n∈S, a n*((zhangGaussianWeight D (x/n)-(if (n : ℝ)<x then 1 else 0) : ℝ) : ℂ)
  have hlr : 0<(l₁ : ℝ) := Nat.cast_pos.mpr hl
  have hP1 : 0<lemma151P1 D := by unfold lemma151P1; exact Real.rpow_pos_of_pos (Real.exp_pos _) _
  have hX : 0<X := div_pos hP1 hlr
  have hx : 0<x := div_pos (Real.exp_pos _) hlr
  have hy : 0<y := div_pos (Real.exp_pos _) hlr
  have he : appendixBFiniteGaussianSourceSlice D β γ l₁ ⌊lemma23PaperP D⌋₊ z-
      appendixBSharpSourceSlice D β γ l₁ ⌊lemma23PaperP D⌋₊ z=E₁-E₂ := by
    unfold appendixBFiniteGaussianSourceSlice appendixBSharpSourceSlice appendixBSharpSourceTerm
    dsimp [E₁,E₂,S,a,X,x,y]
    simp_rw [Complex.ofReal_sub,mul_sub,Finset.sum_sub_distrib]
    ring
  have h₁ := appendixB_actual_rho_finite_error hD hL hX hy hL hβre hβ hγ
  have h₂ := appendixB_actual_rho_finite_error hD hL hX hx hL hβre hβ hγ
  rw [he]
  exact (norm_sub_le E₁ E₂).trans (add_le_add h₁ h₂)

/-- This is the full actual Gaussian source, with the finite source and both
infinite tails joined. Its error is explicit and uniform in the original l1,z range. -/
theorem appendixB_source_unsmoothing_uniform :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      100≤lemma23PaperL D ∧ ∀ β γ : ℂ,
      β.re=0 → ‖β‖≤3*lemma44PaperAlpha D → γ.re=0 →
      ∀ l₁ : ℕ, 0<l₁ → (l₁ : ℝ)<lemma56PaperT D →
      ∀ z : ℝ, z∈Icc (0.5 : ℝ) 0.504 →
      ‖appendixBSourceGaussianSlice D (lemma23PaperL D^9) z β γ l₁-
        appendixBSharpSourceSlice D β γ l₁ ⌊lemma23PaperP D⌋₊ z‖≤
        2*appendixBSingleUnsmoothingBudget D := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp appendixB_source_scales_uniform
  have hlog : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨M,hM⟩ := eventually_atTop.mp (hlog.eventually_ge_atTop 100)
  refine ⟨max 2 (max N M),le_max_left _ _,?_⟩
  intro D hD
  have hD2 : 1<D := by have := (le_max_left 2 (max N M)).trans hD; omega
  have hNM : max N M≤D := (le_max_right _ _).trans hD
  have hL := hM D ((le_max_right _ _).trans hNM)
  have hLp : 0<lemma23PaperL D := by linarith
  have hrange := (hN D ((le_max_left _ _).trans hNM)).2
  have hα := lemma83_alpha_small hL
  refine ⟨hL,?_⟩
  intro β γ hβre hβ hγ l₁ hl hlT z hz
  have hβ1 : ‖β‖≤1 := by linarith [hα.2]
  have hfloor := appendixB_source_floor_geometry (by linarith : 3≤lemma23PaperL D) hl hz.2
  have hfar := appendixB_source_gaussian_finite_error hD2 (by linarith : 3≤lemma23PaperL D)
    hz.1 hβre hβ1 hγ hl ⌊lemma23PaperP D⌋₊ hfloor.1 hfloor.2
  have hfinite := appendixB_finite_gaussian_sharp_error hD2 hLp hβre hβ hγ hl z
  have hT := lemma56_paper_T_pos D
  have huy := (hrange l₁ hl hlT z hz).1
  have hux := (hrange l₁ hl hlT (0.5 : ℝ) (by norm_num)).1
  have hBy := appendixB_cutoff_budget_antitone (D := D) (lemma23PaperL D) hT huy.le
  have hBx := appendixB_cutoff_budget_antitone (D := D) (lemma23PaperL D) hT hux.le
  have ht := norm_add_le
    (appendixBSourceGaussianSlice D (lemma23PaperL D^9) z β γ l₁-
      appendixBFiniteGaussianSourceSlice D β γ l₁ ⌊lemma23PaperP D⌋₊ z)
    (appendixBFiniteGaussianSourceSlice D β γ l₁ ⌊lemma23PaperP D⌋₊ z-
      appendixBSharpSourceSlice D β γ l₁ ⌊lemma23PaperP D⌋₊ z)
  rw [sub_add_sub_cancel] at ht
  apply ht.trans ((add_le_add hfar hfinite).trans ?_)
  have hh := add_le_add hBy hBx
  unfold appendixBSingleUnsmoothingBudget
  linarith

end ZhangLS.Spec
