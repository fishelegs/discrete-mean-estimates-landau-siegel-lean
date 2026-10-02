import ZhangLS.Spec.Proposition71ZetaStripBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-! # Polynomial zeta bounds with the original α=π/log P

The three-shift main-term contour needs only this unconditional shorter-height
rectangle. The original α and all distances from the actual pole are explicit.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

lemma proposition71_zeta_paper_alpha_budget {D : ℕ} (hL : 3≤lemma23PaperL D) :
    0<lemma44PaperAlpha D ∧ lemma44PaperAlpha D≤1/lemma23PaperL D ∧
      2+1/lemma44PaperAlpha D≤3*lemma23PaperL D^9 ∧
      1+(2/lemma23PaperL D)/lemma44PaperAlpha D≤3*lemma23PaperL D^8 := by
  let L := lemma23PaperL D
  have hLp : 0<L := by dsimp [L]; linarith
  have hL1 : 1≤L := by dsimp [L]; linarith
  have ha : lemma44PaperAlpha D=Real.pi/L^9 := by simp [lemma44PaperAlpha,lemma23PaperP,L]
  have hL8 : 4≤L^8 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ)≤3) hL 8
    norm_num at hh
    exact (by norm_num : (4 : ℝ)≤6561).trans hh
  have hp8 : Real.pi≤L^8 := Real.pi_lt_four.le.trans hL8
  have hap : 0<lemma44PaperAlpha D := by rw [ha]; positivity
  have haL : lemma44PaperAlpha D≤1/L := by
    rw [ha]
    apply (div_le_div_iff₀ (pow_pos hLp 9) hLp).mpr
    calc
      _≤L^8*L := mul_le_mul_of_nonneg_right hp8 hLp.le
      _=_ := by ring
  have hi : 1/lemma44PaperAlpha D≤L^9 := by
    rw [ha,one_div_div]
    apply (div_le_iff₀ Real.pi_pos).mpr
    nlinarith only [Real.pi_gt_three,pow_nonneg hLp.le 9]
  have hi2 : (2/L)/lemma44PaperAlpha D≤2*L^8 := by
    have he : (2/L)/lemma44PaperAlpha D=2*L^8/Real.pi := by
      rw [ha]
      field_simp
    rw [he]
    apply (div_le_iff₀ Real.pi_pos).mpr
    nlinarith only [Real.pi_gt_three,pow_nonneg hLp.le 8]
  refine ⟨hap,haL,?_,?_⟩
  · have hh : 1≤L^9 := one_le_pow₀ hL1
    change 2+1/lemma44PaperAlpha D≤3*L^9
    linarith
  · change 1+(2/L)/lemma44PaperAlpha D≤3*L^8
    linarith

/-- The actual ζ denominator is bounded by O(L^17), while each numerator is
O(L^9) on a side at distance at least 1/L from its pole. -/
theorem proposition71_zeta_paper_strip_bounds :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      3≤lemma23PaperL D ∧ ∀ z : ℂ, z≠1 → 1-1/lemma23PaperL D≤z.re →
        z.re≤1+lemma44PaperAlpha D → |z.im|≤proposition71ZetaAuxHeight D →
        riemannZeta z≠0 ∧ ‖(riemannZeta z)⁻¹‖≤9*Real.exp 1*lemma23PaperL D^17 ∧
        (1/lemma23PaperL D≤‖z-1‖ → ‖riemannZeta z‖≤9*Real.exp 1*lemma23PaperL D^9) := by
  obtain ⟨D₀,hD₀,hstrip⟩ := proposition71_zeta_repaired_strip_bounds
  refine ⟨D₀,hD₀,?_⟩
  intro D hD
  obtain ⟨hL,hbound⟩ := hstrip D hD
  have hp := proposition71_zeta_paper_alpha_budget hL
  refine ⟨hL,?_⟩
  intro z hz1 hzlo hzhi hzt
  obtain ⟨hne,hinv,hdir⟩ := hbound (lemma44PaperAlpha D) hp.1 hp.2.1 z hz1 hzlo hzhi hzt
  have hαpos := hp.1
  have hLpos : 0<lemma23PaperL D := by change 0<Real.log (D : ℝ); linarith
  refine ⟨hne,hinv.trans ?_,?_⟩
  · change Real.exp 1*(2+1/lemma44PaperAlpha D)*(1+(2/lemma23PaperL D)/lemma44PaperAlpha D)≤_
    calc
      _≤Real.exp 1*(3*lemma23PaperL D^9)*(3*lemma23PaperL D^8) := by
        gcongr
        · exact hp.2.2.1
        · exact hp.2.2.2
      _=_ := by ring
  · intro hd
    exact (hdir hd).trans ((mul_le_mul_of_nonneg_left hp.2.2.1 (by positivity : 0≤3*Real.exp 1)).trans_eq (by ring))

end ZhangLS.Spec
