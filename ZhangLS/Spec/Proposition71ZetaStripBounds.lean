import ZhangLS.Spec.Proposition71ZetaAuxiliaryStrip
import ZhangLS.Spec.Proposition71ZetaRightAnchor

/-! # Actual direct and inverse zeta bounds on the repaired Section7 strip

The right anchor is an actual Möbius/constant Dirichlet series. Pole-removed
transport remains regular at height zero, and the explicit distance-to-pole
factors are retained until the contour geometry supplies them.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Set
set_option maxHeartbeats 3500000

lemma proposition71_norm_quotient_displacement (z w : ℂ) {d e : ℝ}
    (hd : 0≤d) (he : 0<e) (hdist : ‖z-w‖≤d) (hden : e≤‖w‖) :
    ‖z/w‖≤1+d/e := by
  have hw : 0<‖w‖ := he.trans_le hden
  rw [norm_div]
  calc
    _≤(d+‖w‖)/‖w‖ := div_le_div_of_nonneg_right
      ((norm_le_norm_sub_add z w).trans (add_le_add hdist le_rfl)) hw.le
    _=1+d/‖w‖ := by rw [add_div,div_self hw.ne']; ring
    _≤_ := add_le_add le_rfl (div_le_div_of_nonneg_left hd he hden)

/-- Uniform actual zeta bounds; the final direct bound requests only the
literal distance from the pole, as supplied by each contour side. -/
theorem proposition71_zeta_repaired_strip_bounds :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      3≤Real.log (D : ℝ) ∧ ∀ α : ℝ, 0<α → α≤1/Real.log (D : ℝ) →
      ∀ z : ℂ, z≠1 → 1-1/Real.log (D : ℝ)≤z.re → z.re≤1+α →
        |z.im|≤proposition71ZetaAuxHeight D →
        riemannZeta z≠0 ∧
        ‖(riemannZeta z)⁻¹‖≤Real.exp 1*(2+1/α)*(1+(2/Real.log (D : ℝ))/α) ∧
        (1/Real.log (D : ℝ)≤‖z-1‖ → ‖riemannZeta z‖≤3*Real.exp 1*(2+1/α)) := by
  obtain ⟨D₁,hD₁,hstrip⟩ := proposition71_zeta_auxiliary_strip
  obtain ⟨D₂,hD₂,hratios⟩ := proposition71_zeta_auxiliary_horizontal_ratios
  refine ⟨max D₁ D₂,hD₁.trans (le_max_left _ _),?_⟩
  intro D hD
  obtain ⟨hL,hcost,hbound⟩ := hstrip D ((le_max_left _ _).trans hD)
  have hrat := (hratios D ((le_max_right _ _).trans hD)).2
  refine ⟨hL,?_⟩
  intro α hα hαL z hz1 hzlo hzhi hzt
  have hLp : 0<Real.log (D : ℝ) := by linarith
  have hsmall : 1/Real.log (D : ℝ)≤1/2 := by
    apply (div_le_div_iff₀ hLp (by norm_num : (0 : ℝ)<2)).mpr
    linarith
  have hzpos : 0<z.re := by linarith
  have hzne : z≠0 := by intro hh; rw [hh] at hzpos; simpa using hzpos
  have hz2 : z.re≤2 := by linarith
  have hRz := (hbound z hzlo hz2 hzt).1
  have hζz : riemannZeta z≠0 := by
    intro hzero
    exact hRz ((lemma55_actual_zeta_pole_removed_zero_iff hzpos).mpr hzero)
  let w : ℂ := ((1+α : ℝ) : ℂ)+I*(z.im : ℂ)
  have hwre : w.re=1+α := by simp [w]
  have hwpos : 1<w.re := by rw [hwre]; linarith
  have hwne0 : w≠0 := by intro hh; rw [hh] at hwpos; norm_num at hwpos
  have hwne1 : w≠1 := by intro hh; rw [hh] at hwpos; norm_num at hwpos
  have hζw : riemannZeta w≠0 := riemannZeta_ne_zero_of_one_lt_re hwpos
  have hwlow : 1-1/Real.log (D : ℝ)≤w.re := by rw [hwre]; have := one_div_pos.mpr hLp; linarith
  have hw2 : w.re≤2 := by rw [hwre]; linarith
  have hwt : |w.im|≤proposition71ZetaAuxHeight D := by simpa [w] using hzt
  have hRw := (hbound w hwlow hw2 hwt).1
  have hwidth : (1+α)-z.re≤2/Real.log (D : ℝ) := by
    rw [show 2/Real.log (D : ℝ)=2*(1/Real.log (D : ℝ)) by ring]
    linarith
  have hzcoord : (z.re : ℂ)+I*(z.im : ℂ)=z := by apply Complex.ext <;> simp
  have hr := hrat z.re (1+α) z.im hzlo hzhi (by linarith) hwidth hzt
  rw [hzcoord] at hr
  have hanchor : ‖riemannZeta w‖≤2+1/α ∧ ‖(riemannZeta w)⁻¹‖≤2+1/α := by
    simpa only [hwre,add_sub_cancel_left] using proposition71_zeta_right_half_bounds hwpos
  have hdiff : z-w=((z.re-(1+α) : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [w]
  have hdist : ‖z-w‖≤2/Real.log (D : ℝ) := by
    rw [hdiff,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr hzhi)]
    linarith only [hwidth]
  have hαnorm : α≤‖w-1‖ := by
    have hh := Complex.re_le_norm (w-1)
    simpa only [Complex.sub_re,hwre,Complex.one_re,add_sub_cancel_left] using hh
  have hratio := proposition71_norm_quotient_displacement (z-1) (w-1)
    (show 0≤2/Real.log (D : ℝ) by positivity) hα
    (by simpa only [sub_sub_sub_cancel_right] using hdist) hαnorm
  have hident : (riemannZeta z)⁻¹=((z-1)/(w-1))*(riemannZeta w)⁻¹*
      (zetaPoleRemoved w/zetaPoleRemoved z) := by
    rw [zetaPoleRemoved_eq_mul_riemannZeta hzne hz1,
      zetaPoleRemoved_eq_mul_riemannZeta hwne0 hwne1]
    field_simp [sub_ne_zero.mpr hz1,sub_ne_zero.mpr hwne1]
  refine ⟨hζz,?_,?_⟩
  · rw [hident,norm_mul,norm_mul]
    have hB : 0≤2+1/α := by positivity
    have hQ : 0≤1+(2/Real.log (D : ℝ))/α := by positivity
    exact (mul_le_mul (mul_le_mul hratio hanchor.2 (norm_nonneg _) hQ) hr.2
      (norm_nonneg _) (mul_nonneg hQ hB)).trans_eq (by ring)
  · intro hdistpole
    have hdreverse : ‖(w-1)-(z-1)‖≤2/Real.log (D : ℝ) := by
      simpa only [sub_sub_sub_cancel_right,norm_sub_rev] using hdist
    have hqr := proposition71_norm_quotient_displacement (w-1) (z-1)
      (show 0≤2/Real.log (D : ℝ) by positivity) (one_div_pos.mpr hLp) hdreverse hdistpole
    have hq3 : ‖(w-1)/(z-1)‖≤3 := by
      convert hqr using 1 <;> field_simp
      ring
    have he : riemannZeta z=((w-1)/(z-1))*riemannZeta w*
        (zetaPoleRemoved z/zetaPoleRemoved w) := by
      rw [zetaPoleRemoved_eq_mul_riemannZeta hzne hz1,
        zetaPoleRemoved_eq_mul_riemannZeta hwne0 hwne1]
      field_simp [sub_ne_zero.mpr hz1,sub_ne_zero.mpr hwne1]
    rw [he,norm_mul,norm_mul]
    exact (mul_le_mul (mul_le_mul hq3 hanchor.1 (norm_nonneg _) (by norm_num)) hr.1
      (norm_nonneg _) (by positivity)).trans_eq (by ring)

end ZhangLS.Spec
