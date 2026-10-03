import ZhangLS.Spec.AppendixBTailRhoBounds
import Mathlib.NumberTheory.Harmonic.Bounds

/-! Closed finite Gaussian-to-sharp error on n<=floor(P), with the checked
constant rho bound on the boundary and only the ordinary far-band harmonic mass. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace ZhangLS.Spec
open Complex MeasureTheory Finset
open scoped Classical

noncomputable def appendixBCutoffUnsmoothingBudget (D : ℕ) (K x : ℝ) : ℝ :=
  Real.exp (3*Real.pi)*(Real.exp (2*(K/lemma23PaperL D^15))-1+
    2*Real.exp (K/lemma23PaperL D^15)/x)+
  ((Real.sqrt Real.pi)⁻¹*Real.exp (-(K^2))/K)*Real.exp (3*Real.pi)*(1+lemma23PaperL D^9)

lemma appendixB_harmonic_paper_floor {D : ℕ} (hL : 0<lemma23PaperL D) :
    (∑ n∈Finset.Icc 1 ⌊lemma23PaperP D⌋₊, (1 : ℝ)/n)≤1+lemma23PaperL D^9 := by
  have hP : 1≤lemma23PaperP D := Real.one_le_exp (pow_nonneg hL.le 9)
  have hh := harmonic_floor_le_one_add_log (lemma23PaperP D) hP
  simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,
    one_div,lemma23PaperP,Real.log_exp] using hh

/-- An actual closed error bound, with no rho-norm hypothesis left to discharge. -/
theorem appendixB_actual_rho_finite_error {D : ℕ} (hD : 1<D)
    (hL : 0<lemma23PaperL D) {X x K : ℝ} (hX : 0<X) (hx : 0<x) (hK : 0<K)
    {β γ : ℂ} (hβre : β.re=0) (hβ : ‖β‖≤3*lemma44PaperAlpha D) (hγ : γ.re=0) :
    ‖∑ n∈Finset.Icc 1 ⌊lemma23PaperP D⌋₊,
      appendixBRhoMonomialCoefficient X β γ n*
        ((zhangGaussianWeight D (x/n)-(if (n : ℝ)<x then 1 else 0) : ℝ) : ℂ)‖≤
      appendixBCutoffUnsmoothingBudget D K x := by
  let S := Finset.Icc 1 ⌊lemma23PaperP D⌋₊
  let u := fun n : ℕ => Real.log (x/(n : ℝ))
  let B := appendixBGaussianBoundaryBand D K u S
  let δ := K/lemma23PaperL D^15
  let E := (Real.sqrt Real.pi)⁻¹*Real.exp (-(K^2))/K
  have hP : 0<lemma23PaperP D := Real.exp_pos _
  have hS (n : ℕ) (hn : n∈S) : 0<n ∧ (n : ℝ)≤lemma23PaperP D :=
    ⟨(Finset.mem_Icc.mp hn).1,(Nat.le_floor_iff hP.le).mp (Finset.mem_Icc.mp hn).2⟩
  have hBsub : B⊆S := Finset.filter_subset _ _
  have hA : 0<lemma23PaperL D^15 := by positivity
  have hδ : 0≤δ := by dsimp [δ]; positivity
  have hband (n : ℕ) (hn : n∈B) : |Real.log (x/(n : ℝ))|≤δ := by
    have hh := (Finset.mem_filter.mp hn).2
    change lemma23PaperL D^15*|Real.log (x/(n : ℝ))|<K at hh
    dsimp [δ]
    apply (le_div_iff₀ hA).mpr
    simpa only [mul_comm] using hh.le
  have hmass := appendixB_logarithmic_boundary_mass B hx hδ
    (fun n hn => (hS n (hBsub hn)).1) hband
  have hfar : (∑ n∈S\B, (1 : ℝ)/n)≤1+lemma23PaperL D^9 := by
    calc
      _ ≤ ∑ n∈S, (1 : ℝ)/n :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (by intro n hn hnb; positivity)
      _ ≤ _ := appendixB_harmonic_paper_floor hL
  have hh := appendixB_actual_rho_finite_unsmoothing hD hL hX hx hK hβre hβ hγ S hS
  apply hh.trans
  have hb := mul_le_mul_of_nonneg_left hmass (Real.exp_pos (3*Real.pi)).le
  have hf := mul_le_mul_of_nonneg_left hfar (show 0≤E*Real.exp (3*Real.pi) by dsimp [E]; positivity)
  exact (add_le_add hb hf).trans_eq (by dsimp [appendixBCutoffUnsmoothingBudget,δ,E])

lemma appendixB_cutoff_budget_antitone {D : ℕ} (K : ℝ) {x y : ℝ}
    (hx : 0<x) (hxy : x≤y) :
    appendixBCutoffUnsmoothingBudget D K y≤appendixBCutoffUnsmoothingBudget D K x := by
  unfold appendixBCutoffUnsmoothingBudget
  gcongr

end ZhangLS.Spec
