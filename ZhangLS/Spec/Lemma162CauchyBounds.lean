import ZhangLS.Spec.Lemma162SectorBound
import Mathlib.Analysis.Complex.Liouville

/-! Every fixed derivative order is controlled on the actual center;
all powers of log D and the factorial are explicit. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Metric
set_option maxHeartbeats 1500000

theorem lemma162_paper_cauchy_bounds (c : ℝ) (hc : 0<c) :
    ∃ D₀ : ℕ, 3≤D₀ ∧ lemma23SectionFourModulusThreshold≤D₀ ∧
      ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D, ∀ j : Fin 2, ∀ n : ℕ,
        ‖iteratedDeriv n (lemma162CorrectedEulerProduct χ (lemma52PaperBetaOne D c)
          (lemma162PaperShift D c j)) 1‖≤
            n.factorial*lemma162SectorConstant*(10*lemma23PaperL D)^n := by
  obtain ⟨D₀,hD₀,hsection,hdisk⟩ := lemma162_paper_disk_bound c hc
  refine ⟨D₀,hD₀,hsection,?_⟩
  intro D hD χ j n
  obtain ⟨ha,hb⟩ := hdisk D hD χ j
  have hL := (lemma44_parameters_at_explicit_threshold (hsection.trans hD)).1
  have hR : 0<(10*lemma23PaperL D)⁻¹ := inv_pos.mpr (by linarith)
  have hd : DiffContOnCl ℂ
      (lemma162CorrectedEulerProduct χ (lemma52PaperBetaOne D c) (lemma162PaperShift D c j))
      (ball 1 ((10*lemma23PaperL D)⁻¹)) :=
    ha.differentiableOn.diffContOnCl_ball subset_rfl
  have hh := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR hd
    (fun s hs => hb s (le_of_eq (by simpa [mem_sphere,dist_eq_norm] using hs)))
  simpa only [inv_pow,div_inv_eq_mul] using hh

end ZhangLS.Spec
