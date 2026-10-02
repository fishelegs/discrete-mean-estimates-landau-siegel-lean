import ZhangLS.Spec.Lemma81ActualRectangleBoundary
import ZhangLS.Spec.Lemma81FiniteRectangleResidues

/-! # Exact actual finite rectangle residue identity in Lemma 8.1

This is the first equality in (8.1), on a proved uniformly separated
rectangle containing exactly the original strict L-zero set. The actual
residues, actual branch, analytic numerator, and all boundary integrals are
handled internally. No residue/contour/zero assertions are assumptions.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Set MeasureTheory Filter
open scoped Real Topology Classical
set_option maxHeartbeats 2000000

lemma lemma81_closed_rectangle_iff {D : ℕ} {lo hi : ℝ} {s : ℂ} :
    s ∈ Icc (1/2-lemma44PaperAlpha D) (1/2+lemma44PaperAlpha D) ×ℂ Icc lo hi ↔
      Lemma81ClosedRectangle D lo hi s := by
  constructor
  · intro hs
    exact ⟨abs_le.mpr ⟨by linarith only [hs.1.1],by linarith only [hs.1.2]⟩,hs.2⟩
  · intro hs
    exact ⟨⟨by linarith only [(abs_le.mp hs.1).1],by linarith only [(abs_le.mp hs.1).2]⟩,hs.2⟩

lemma lemma81_open_rectangle_iff {D : ℕ} {lo hi : ℝ} {s : ℂ} :
    s ∈ Ioo (1/2-lemma44PaperAlpha D) (1/2+lemma44PaperAlpha D) ×ℂ Ioo lo hi ↔
      Lemma81OpenRectangle D lo hi s := by
  constructor
  · intro hs
    exact ⟨abs_lt.mpr ⟨by linarith only [hs.1.1],by linarith only [hs.1.2]⟩,hs.2⟩
  · intro hs
    exact ⟨⟨by linarith only [(abs_lt.mp hs.1).1],by linarith only [(abs_lt.mp hs.1).2]⟩,hs.2⟩

lemma lemma81_closed_not_open_is_boundary {D : ℕ} {lo hi : ℝ} {s : ℂ}
    (hs : Lemma81ClosedRectangle D lo hi s) (hn : ¬Lemma81OpenRectangle D lo hi s) :
    Lemma81RectangleBoundary D lo hi s := by
  refine ⟨hs,?_⟩
  rcases lt_or_eq_of_le hs.1 with hr | hr
  · by_cases hl : lo < s.im
    · have hu : s.im = hi := le_antisymm hs.2.2 (not_lt.mp (fun h => hn ⟨hr,hl,h⟩))
      exact Or.inr (Or.inr hu)
    · exact Or.inr (Or.inl (le_antisymm (not_lt.mp hl) hs.2.1))
  · exact Or.inl hr

/-- The exact actual zero-sum-to-rectangle identity for every compatible
shift constant, with the complete rectangle construction included. -/
theorem lemma81_actual_rectangle_residue_identity {c : ℝ} (hc : 0 < c)
    (hcompatible : Lemma52CompatibleConstant c) :
    ∃ N : ℕ, ∀ {D p : ℕ} [NeZero p] (χ : RealPrimitiveCharacter D)
      (ψ : DirichletCharacter ℂ p), N ≤ D → Lemma23InPsi1 χ ψ →
      ∀ Y : ℂ → ℂ, Lemma23ActualBranch ψ Y → ∀ a₁ a₂ : ℕ → ℂ,
      ∃ lo hi : ℝ,
      |lo-((lemma23PaperCenter D).im-lemma23PaperL D ^ 405)| ≤ lemma44PaperAlpha D/4 ∧
      |hi-((lemma23PaperCenter D).im+lemma23PaperL D ^ 405)| ≤ lemma44PaperAlpha D/4 ∧
      lo < hi ∧
      (∀ s : ℂ, Lemma81RectangleBoundary D lo hi s → Lemma59ZeroSeparated (D := D) ψ s (1/4)) ∧
      (2*(Real.pi : ℂ)*I)⁻¹ * lemma81RectangleIntegral
        (lemma81TildeIntegrand D c ψ Y a₁ a₂)
        (1/2-lemma44PaperAlpha D) (1/2+lemma44PaperAlpha D) lo hi =
        ∑ ρ ∈ lemma81ZeroFinset D ψ, lemma81ActualResidueWeight D c ψ Y a₁ a₂ ρ := by
  obtain ⟨Nb,hbound⟩ := lemma81_uniform_actual_rectangle_boundaries
  obtain ⟨Nc,hcomp⟩ := hcompatible
  obtain ⟨Ns,hsection,hsmall⟩ := lemma52_exists_shift_threshold hc
  refine ⟨max Nb (max Nc Ns),?_⟩
  intro D p _ χ ψ hD hψ Y hY a₁ a₂
  have hDb := (le_max_left Nb (max Nc Ns)).trans hD
  have hDc := (le_max_left Nc Ns).trans ((le_max_right Nb (max Nc Ns)).trans hD)
  have hDs := (le_max_right Nc Ns).trans ((le_max_right Nb (max Nc Ns)).trans hD)
  have hL := (lemma44_parameters_at_explicit_threshold (hsection.trans hDs)).1
  have hLp : 0 < lemma23PaperL D := by linarith only [hL]
  have ha := (lemma44_alpha_pos_le_one hL).1
  have haq := lemma51_alpha_le_quarter hL
  obtain ⟨lo,hi,hlo,hhi,horder,hzeros,hsep⟩ := hbound χ ψ hDb hψ
  refine ⟨lo,hi,hlo,hhi,horder,hsep,?_⟩
  let K := Icc (1/2-lemma44PaperAlpha D) (1/2+lemma44PaperAlpha D) ×ℂ Icc lo hi
  let Num := lemma81TildeNumerator D c ψ Y a₁ a₂
  let M := lemma23DirichletNormalizedM ψ Y
  let S := lemma81ZeroFinset D ψ
  have hdom {s : ℂ} (hs : s ∈ K) : 0 < s.im ∧
      0 < s.im+lemma23PaperOffsetOne D c ∧
      0 < s.im+lemma23PaperOffsetTwo D c ∧
      0 < s.im+lemma23PaperOffsetThree D c := by
    have hclosed := lemma81_closed_rectangle_iff.mp hs
    have hh := lemma81_closed_rectangle_height hlo hhi hclosed
    have hsExt : Lemma51InExtendedRegion D s := ⟨hclosed.1,by
      linarith only [hh,haq,pow_nonneg hLp.le 405]⟩
    have hT : 0 < lemma51PaperT0 D := by unfold lemma51PaperT0; positivity
    have hspos := hT.trans_le (lemma51_extended_region_data hL hsExt).2.2.1
    have hb := lemma52_offset_bounds hL hc (hsmall D hDs)
    exact ⟨hspos,by linarith only [hspos,hb.1.1],
      by linarith only [hspos,hb.2.1.1],by linarith only [hspos,hb.2.2.1]⟩
  have hNum : AnalyticOnNhd ℂ Num K := by
    intro s hs
    have hh := hdom hs
    exact lemma81_actual_tilde_numerator_analyticAt c ψ hψ.1.2.1 hψ.1.1.ne_one Y hY a₁ a₂
      hh.2.1 hh.2.2.1 hh.2.2.2
  have hMa : AnalyticOnNhd ℂ M K := by
    intro s hs
    exact lemma81_actual_M_analytic ψ hψ.1.2.1 hψ.1.1.ne_one Y hY s (hdom hs).1
  have hmember (ρ : ℂ) : ρ ∈ S ↔ Lemma23InZeroWindow D ρ ∧ ψ.LFunction ρ = 0 :=
    lemma81_mem_original_zero_finset ψ (lemma59_family_character_nonprincipal ψ hψ.1) ρ
  have hzeroSet : ∀ s ∈ K, M s = 0 ↔ s ∈ S := by
    intro s hs
    have hYne := lemma52_actual_branch_ne_zero ψ hψ.1.2.1 hψ.1.1.ne_one Y hY (hdom hs).1
    constructor
    · intro hzM
      have hzL : ψ.LFunction s = 0 := (mul_eq_zero.mp hzM).resolve_left hYne
      have hopen : Lemma81OpenRectangle D lo hi s := by
        by_contra hnot
        have hboundary := lemma81_closed_not_open_is_boundary (lemma81_closed_rectangle_iff.mp hs) hnot
        have hbad := hsep s hboundary s hzL
        simp only [sub_self,norm_zero] at hbad
        linarith only [hbad,ha]
      exact (hmember s).mpr ⟨(hzeros s hzL).mp hopen,hzL⟩
    · intro hmem
      have hz := ((hmember s).mp hmem).2
      change Y s * ψ.LFunction s = 0
      rw [hz,mul_zero]
  have hinside : ∀ ρ ∈ S, ρ ∈ Ioo (1/2-lemma44PaperAlpha D) (1/2+lemma44PaperAlpha D) ×ℂ Ioo lo hi := by
    intro ρ hρ
    have hh := (hmember ρ).mp hρ
    exact lemma81_open_rectangle_iff.mpr ((hzeros ρ hh.2).mpr hh.1)
  have hsimple : ∀ ρ ∈ S, deriv M ρ ≠ 0 := by
    intro ρ hρ
    have hh := (hmember ρ).mp hρ
    exact ((hcomp χ ψ hDc hψ).2.2 Y hY ρ hh.1 hh.2).1
  have hres := lemma81_finite_rectangle_residue_theorem Num M S
    (by linarith only [ha]) horder hNum hMa hzeroSet hinside hsimple
  have he : (fun s => Num s/M s) = lemma81TildeIntegrand D c ψ Y a₁ a₂ := by
    funext s
    exact (lemma81_tilde_integrand_eq_numerator_div D c ψ Y a₁ a₂ s).symm
  rw [he] at hres
  have hsum : (∑ ρ ∈ S, Num ρ/deriv M ρ) =
      ∑ ρ ∈ S, lemma81ActualResidueWeight D c ψ Y a₁ a₂ ρ := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    exact lemma81_actual_numerator_div_deriv D c ψ Y a₁ a₂ ρ
  rw [hsum] at hres
  rw [hres]
  have hfactor : 2*(Real.pi : ℂ)*I ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero
  rw [← mul_assoc,inv_mul_cancel₀ hfactor,one_mul]

end ZhangLS.Spec
