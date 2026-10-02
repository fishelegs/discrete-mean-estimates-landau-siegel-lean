import ZhangLS.Spec.Lemma56PrincipalPerronMellin
import ZhangLS.Spec.Lemma56ZetaLogDerivativeLeft
import ZhangLS.Spec.Lemma56PerronHorizontal

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set Metric
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

def Lemma56PerronPuncturedRectangle (a H : ℝ) : Set ℂ :=
  lemma44ClosedRectangle a 2 H \ {1}

def Lemma56PerronRectangleEdgesIntegrable (f : ℂ → ℂ) (a H : ℝ) : Prop :=
  IntervalIntegrable (fun x : ℝ => f ((x : ℂ) - (H : ℂ) * I)) volume a 2 ∧
  IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (H : ℂ) * I)) volume a 2 ∧
  IntervalIntegrable (fun y : ℝ => f (((2 : ℝ) : ℂ) + (y : ℂ) * I)) volume (-H) H ∧
  IntervalIntegrable (fun y : ℝ => f ((a : ℂ) + (y : ℂ) * I)) volume (-H) H

lemma lemma56_perron_rectangle_edges_mem {a H : ℝ} (ha : a < 1) (hH : 0 < H) :
    (∀ x ∈ uIcc a 2, (x : ℂ) - (H : ℂ) * I ∈ Lemma56PerronPuncturedRectangle a H) ∧
    (∀ x ∈ uIcc a 2, (x : ℂ) + (H : ℂ) * I ∈ Lemma56PerronPuncturedRectangle a H) ∧
    (∀ y ∈ uIcc (-H) H, ((2 : ℝ) : ℂ) + (y : ℂ) * I ∈ Lemma56PerronPuncturedRectangle a H) ∧
    (∀ y ∈ uIcc (-H) H, (a : ℂ) + (y : ℂ) * I ∈ Lemma56PerronPuncturedRectangle a H) := by
  have ha2 : a ≤ 2 := by linarith only [ha]
  have hHH : -H ≤ H := by linarith only [hH]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [uIcc_of_le ha2] at hx
    refine ⟨?_, ?_⟩
    · change _ ∈ Icc a 2 ×ℂ Icc (-H) H
      simp only [mem_reProdIm, mem_Icc, sub_re, sub_im, ofReal_re, ofReal_im,
        mul_re, mul_im, I_re, I_im, mul_zero, zero_mul, mul_one, zero_add, sub_zero]
      exact ⟨hx, by constructor <;> linarith only [hH]⟩
    · simp only [mem_singleton_iff]
      intro he
      have hi := congrArg Complex.im he
      simp at hi
      linarith only [hi, hH]
  · intro x hx
    rw [uIcc_of_le ha2] at hx
    refine ⟨?_, ?_⟩
    · change _ ∈ Icc a 2 ×ℂ Icc (-H) H
      simpa [mem_reProdIm] using And.intro hx (show -H ≤ H ∧ H ≤ H by constructor; exact hHH; rfl)
    · simp only [mem_singleton_iff]
      intro he
      have hi := congrArg Complex.im he
      simp at hi
      linarith only [hi, hH]
  · intro y hy
    rw [uIcc_of_le hHH] at hy
    refine ⟨?_, ?_⟩
    · change _ ∈ Icc a 2 ×ℂ Icc (-H) H
      simpa [mem_reProdIm] using And.intro (show a ≤ 2 ∧ (2 : ℝ) ≤ 2 from ⟨ha2, le_rfl⟩) hy
    · simp only [mem_singleton_iff]
      intro he
      have hr := congrArg Complex.re he
      norm_num at hr
  · intro y hy
    rw [uIcc_of_le hHH] at hy
    refine ⟨?_, ?_⟩
    · change _ ∈ Icc a 2 ×ℂ Icc (-H) H
      simpa [mem_reProdIm] using And.intro (show a ≤ a ∧ a ≤ 2 from ⟨le_rfl, ha2⟩) hy
    · simp only [mem_singleton_iff]
      intro he
      have hr := congrArg Complex.re he
      simp at hr
      linarith only [hr, ha]

lemma lemma56_perron_rectangle_edges_integrable {a H : ℝ} (ha : a < 1) (hH : 0 < H)
    (f : ℂ → ℂ) (hf : ContinuousOn f (Lemma56PerronPuncturedRectangle a H)) :
    Lemma56PerronRectangleEdgesIntegrable f a H := by
  have hm := lemma56_perron_rectangle_edges_mem ha hH
  have hline (γ : ℝ → ℂ) (hγ : Continuous γ) (u v : ℝ)
      (hg : MapsTo γ (uIcc u v) (Lemma56PerronPuncturedRectangle a H)) :
      IntervalIntegrable (fun t => f (γ t)) volume u v :=
    (hf.comp hγ.continuousOn hg).intervalIntegrable
  exact ⟨hline _ (by fun_prop) a 2 hm.1,
    hline _ (by fun_prop) a 2 hm.2.1,
    hline _ (by fun_prop) (-H) H hm.2.2.1,
    hline _ (by fun_prop) (-H) H hm.2.2.2⟩

lemma lemma56_perron_rectangle_boundary_add {a H : ℝ} (f g : ℂ → ℂ)
    (hf : Lemma56PerronRectangleEdgesIntegrable f a H)
    (hg : Lemma56PerronRectangleEdgesIntegrable g a H) :
    lemma44GeneralRectangleBoundaryIntegral (fun s => f s + g s) a 2 H =
      lemma44GeneralRectangleBoundaryIntegral f a 2 H +
        lemma44GeneralRectangleBoundaryIntegral g a 2 H := by
  unfold lemma44GeneralRectangleBoundaryIntegral
  rw [intervalIntegral.integral_add hf.1 hg.1,
    intervalIntegral.integral_add hf.2.1 hg.2.1,
    intervalIntegral.integral_add hf.2.2.1 hg.2.2.1,
    intervalIntegral.integral_add hf.2.2.2 hg.2.2.2]
  ring

lemma lemma56_perron_rectangle_boundary_congr {a H : ℝ} (ha : a < 1) (hH : 0 < H)
    (f g : ℂ → ℂ) (heq : ∀ s ∈ Lemma56PerronPuncturedRectangle a H, f s = g s) :
    lemma44GeneralRectangleBoundaryIntegral f a 2 H =
      lemma44GeneralRectangleBoundaryIntegral g a 2 H := by
  have hm := lemma56_perron_rectangle_edges_mem ha hH
  have hbot : (∫ x : ℝ in a..2, f ((x : ℂ) - (H : ℂ) * I)) =
      ∫ x : ℝ in a..2, g ((x : ℂ) - (H : ℂ) * I) :=
    intervalIntegral.integral_congr (fun x hx => heq _ (hm.1 x hx))
  have htop : (∫ x : ℝ in a..2, f ((x : ℂ) + (H : ℂ) * I)) =
      ∫ x : ℝ in a..2, g ((x : ℂ) + (H : ℂ) * I) :=
    intervalIntegral.integral_congr (fun x hx => heq _ (hm.2.1 x hx))
  have hright : (∫ y : ℝ in -H..H, f (((2 : ℝ) : ℂ) + (y : ℂ) * I)) =
      ∫ y : ℝ in -H..H, g (((2 : ℝ) : ℂ) + (y : ℂ) * I) :=
    intervalIntegral.integral_congr (fun y hy => heq _ (hm.2.2.1 y hy))
  have hleft : (∫ y : ℝ in -H..H, f ((a : ℂ) + (y : ℂ) * I)) =
      ∫ y : ℝ in -H..H, g ((a : ℂ) + (y : ℂ) * I) :=
    intervalIntegral.integral_congr (fun y hy => heq _ (hm.2.2.2 y hy))
  unfold lemma44GeneralRectangleBoundaryIntegral
  rw [hbot, htop, hright, hleft]

end ZhangLS.Spec
