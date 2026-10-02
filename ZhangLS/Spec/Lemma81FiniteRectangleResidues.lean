import ZhangLS.Spec.Lemma81FinitePoleRemoval
import ZhangLS.Spec.Lemma81RectangleWinding

/-! # Finite simple-pole residue theorem for the verified rectangle

Residues are computed as N(ρ)/M′(ρ), the finite pole-removed function is proved
analytic, and each individual winding integral is proved +2πi. There are no
residue, contour-integrability, or remainder assumptions in the capstone.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Set MeasureTheory Filter
open scoped Topology Classical
set_option maxHeartbeats 2000000

lemma lemma81_finite_pole_edge_integral (N M : ℂ → ℂ) (S : Finset ℂ)
    (U : Set ℂ) (hR : ContinuousOn (lemma81FinitePoleRemainder N M S) U)
    (γ : ℝ → ℂ) (hγ : Continuous γ) (a b : ℝ) (hm : MapsTo γ (uIcc a b) U)
    (hne : ∀ t ∈ uIcc a b, ∀ ρ ∈ S, γ t ≠ ρ) :
    (∫ t in a..b, N (γ t)/M (γ t)) =
      (∑ ρ ∈ S, (N ρ/deriv M ρ) * (∫ t in a..b, (γ t-ρ)⁻¹)) +
        ∫ t in a..b, lemma81FinitePoleRemainder N M S (γ t) := by
  have hq (ρ : ℂ) (hρ : ρ ∈ S) : IntervalIntegrable
      (fun t => (N ρ/deriv M ρ) * (γ t-ρ)⁻¹) volume a b := by
    apply ContinuousOn.intervalIntegrable
    exact ((hγ.continuousOn.sub continuousOn_const).inv₀
      (fun t ht => sub_ne_zero.mpr (hne t ht ρ hρ))).const_mul _
  have hr : IntervalIntegrable (fun t => lemma81FinitePoleRemainder N M S (γ t)) volume a b :=
    (hR.comp hγ.continuousOn hm).intervalIntegrable
  have hsum : IntervalIntegrable
      (fun t => ∑ ρ ∈ S, (N ρ/deriv M ρ) * (γ t-ρ)⁻¹) volume a b := by
    have he : (∑ ρ ∈ S, fun t => (N ρ/deriv M ρ) * (γ t-ρ)⁻¹) =
        (fun t => ∑ ρ ∈ S, (N ρ/deriv M ρ) * (γ t-ρ)⁻¹) := by
      funext t
      simp only [Finset.sum_apply]
    rw [← he]
    exact IntervalIntegrable.sum S hq
  calc
    _ = ∫ t in a..b, (∑ ρ ∈ S, (N ρ/deriv M ρ) * (γ t-ρ)⁻¹) +
        lemma81FinitePoleRemainder N M S (γ t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have hnot : γ t ∉ S := fun hh => hne t ht (γ t) hh rfl
      dsimp only
      rw [lemma81_finite_pole_remainder_off_set N M S hnot]
      simp only [div_eq_mul_inv]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add hsum hr,
        intervalIntegral.integral_finsetSum hq]
      simp only [intervalIntegral.integral_const_mul]

/-- Genuine finite rectangle residue theorem with all analytic details
and the winding factor discharged from the actual numerator/denominator. -/
theorem lemma81_finite_rectangle_residue_theorem (N M : ℂ → ℂ) (S : Finset ℂ)
    {a b lo hi : ℝ} (hab : a < b) (hlh : lo < hi)
    (hN : AnalyticOnNhd ℂ N (Icc a b ×ℂ Icc lo hi))
    (hM : AnalyticOnNhd ℂ M (Icc a b ×ℂ Icc lo hi))
    (hzeros : ∀ s ∈ Icc a b ×ℂ Icc lo hi, M s = 0 ↔ s ∈ S)
    (hinside : ∀ ρ ∈ S, ρ ∈ Ioo a b ×ℂ Ioo lo hi)
    (hsimple : ∀ ρ ∈ S, deriv M ρ ≠ 0) :
    lemma81RectangleIntegral (fun s => N s/M s) a b lo hi =
      2*(Real.pi : ℂ)*I * ∑ ρ ∈ S, N ρ/deriv M ρ := by
  let R := lemma81FinitePoleRemainder N M S
  have hRa := lemma81_finite_pole_remainder_analyticOnNhd N M S _ hN hM hzeros hsimple
  have hRc : ContinuousOn R (Icc a b ×ℂ Icc lo hi) := hRa.continuousOn
  have hRzero := lemma81_rectangle_cauchy R hab.le hlh.le hRa.differentiableOn
  have hbottom := lemma81_finite_pole_edge_integral N M S _ hRc
    (fun x : ℝ => (x : ℂ)+(lo : ℂ)*I) (by fun_prop) a b
    (by
      intro x hx
      rw [uIcc_of_le hab.le] at hx
      exact ⟨by simpa using hx,by simpa using (show lo ≤ lo ∧ lo ≤ hi from ⟨le_rfl,hlh.le⟩)⟩)
    (by
      intro x hx ρ hρ he
      have hh := congrArg Complex.im he
      simp only [add_im,ofReal_im,mul_im,I_im,I_re,ofReal_re,mul_one,mul_zero,add_zero,zero_add] at hh
      have hp := (hinside ρ hρ).2.1
      linarith only [hh,hp])
  have htop := lemma81_finite_pole_edge_integral N M S _ hRc
    (fun x : ℝ => (x : ℂ)+(hi : ℂ)*I) (by fun_prop) a b
    (by
      intro x hx
      rw [uIcc_of_le hab.le] at hx
      exact ⟨by simpa using hx,by simpa using (show lo ≤ hi ∧ hi ≤ hi from ⟨hlh.le,le_rfl⟩)⟩)
    (by
      intro x hx ρ hρ he
      have hh := congrArg Complex.im he
      simp only [add_im,ofReal_im,mul_im,I_im,I_re,ofReal_re,mul_one,mul_zero,add_zero,zero_add] at hh
      have hp := (hinside ρ hρ).2.2
      linarith only [hh,hp])
  have hright := lemma81_finite_pole_edge_integral N M S _ hRc
    (fun y : ℝ => (b : ℂ)+(y : ℂ)*I) (by fun_prop) lo hi
    (by
      intro y hy
      rw [uIcc_of_le hlh.le] at hy
      exact ⟨by simpa using (show a ≤ b ∧ b ≤ b from ⟨hab.le,le_rfl⟩),by simpa using hy⟩)
    (by
      intro y hy ρ hρ he
      have hh := congrArg Complex.re he
      simp only [add_re,ofReal_re,mul_re,I_re,I_im,ofReal_im,mul_zero,mul_one,sub_zero,add_zero] at hh
      have hp := (hinside ρ hρ).1.2
      linarith only [hh,hp])
  have hleft := lemma81_finite_pole_edge_integral N M S _ hRc
    (fun y : ℝ => (a : ℂ)+(y : ℂ)*I) (by fun_prop) lo hi
    (by
      intro y hy
      rw [uIcc_of_le hlh.le] at hy
      exact ⟨by simpa using (show a ≤ a ∧ a ≤ b from ⟨le_rfl,hab.le⟩),by simpa using hy⟩)
    (by
      intro y hy ρ hρ he
      have hh := congrArg Complex.re he
      simp only [add_re,ofReal_re,mul_re,I_re,I_im,ofReal_im,mul_zero,mul_one,sub_zero,add_zero] at hh
      have hp := (hinside ρ hρ).1.1
      linarith only [hh,hp])
  have hsum : (∑ ρ ∈ S, (N ρ/deriv M ρ) *
      lemma81RectangleIntegral (fun z => (z-ρ)⁻¹) a b lo hi) =
      (∑ ρ ∈ S, (N ρ/deriv M ρ) * (∫ x in a..b, ((x : ℂ)+(lo : ℂ)*I-ρ)⁻¹)) -
      (∑ ρ ∈ S, (N ρ/deriv M ρ) * (∫ x in a..b, ((x : ℂ)+(hi : ℂ)*I-ρ)⁻¹)) +
      I * (∑ ρ ∈ S, (N ρ/deriv M ρ) * (∫ y in lo..hi, ((b : ℂ)+(y : ℂ)*I-ρ)⁻¹)) -
      I * (∑ ρ ∈ S, (N ρ/deriv M ρ) * (∫ y in lo..hi, ((a : ℂ)+(y : ℂ)*I-ρ)⁻¹)) := by
    unfold lemma81RectangleIntegral
    calc
      _ = ∑ ρ ∈ S,
          ((N ρ/deriv M ρ) * (∫ x in a..b, ((x : ℂ)+(lo : ℂ)*I-ρ)⁻¹) -
           (N ρ/deriv M ρ) * (∫ x in a..b, ((x : ℂ)+(hi : ℂ)*I-ρ)⁻¹) +
           I * ((N ρ/deriv M ρ) * (∫ y in lo..hi, ((b : ℂ)+(y : ℂ)*I-ρ)⁻¹)) -
           I * ((N ρ/deriv M ρ) * (∫ y in lo..hi, ((a : ℂ)+(y : ℂ)*I-ρ)⁻¹))) := by
        apply Finset.sum_congr rfl
        intro ρ hρ
        ring
      _ = _ := by simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum]
  calc
    _ = (∑ ρ ∈ S, (N ρ/deriv M ρ) *
        lemma81RectangleIntegral (fun z => (z-ρ)⁻¹) a b lo hi) +
          lemma81RectangleIntegral R a b lo hi := by
      rw [hsum]
      unfold lemma81RectangleIntegral
      rw [hbottom,htop,hright,hleft]
      dsimp only [R]
      ring
    _ = ∑ ρ ∈ S, (N ρ/deriv M ρ) * (2*(Real.pi : ℂ)*I) := by
      rw [hRzero,add_zero]
      apply Finset.sum_congr rfl
      intro ρ hρ
      rw [lemma81_rectangle_simple_pole_winding (hinside ρ hρ)]
    _ = _ := by rw [← Finset.sum_mul]; ring

end ZhangLS.Spec
