import ZhangLS.Spec.Lemma32RectangleWinding
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Metric Set Filter
open scoped Classical
set_option maxHeartbeats 2000000

def lemma32BoundaryIntegrable (f : ℂ → ℂ) (a b T : ℝ) : Prop :=
  IntervalIntegrable (fun x : ℝ => f ((x : ℂ)-(T : ℂ)*I)) volume a b ∧
  IntervalIntegrable (fun x : ℝ => f ((x : ℂ)+(T : ℂ)*I)) volume a b ∧
  IntervalIntegrable (fun y : ℝ => f ((b : ℂ)+(y : ℂ)*I)) volume (-T) T ∧
  IntervalIntegrable (fun y : ℝ => f ((a : ℂ)+(y : ℂ)*I)) volume (-T) T

lemma lemma32_boundary_integrable_punctured (f : ℂ → ℂ)
    (hc : ContinuousOn f ({0} : Set ℂ)ᶜ) (a b T : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hT : 0 < T) : lemma32BoundaryIntegrable f a b T := by
  have hg (γ : ℝ → ℂ) (hγ : Continuous γ) (hn : ∀ t, γ t ≠ 0) : Continuous (fun t => f (γ t)) := by
    exact continuousOn_univ.mp (hc.comp hγ.continuousOn (by intro t ht;simpa using hn t))
  have hbot := hg (fun x => (x : ℂ)-(T : ℂ)*I) (by fun_prop)
    (by intro x hx;have hi := congrArg Complex.im hx;simp at hi;linarith)
  have htop := hg (fun x => (x : ℂ)+(T : ℂ)*I) (by fun_prop)
    (by intro x hx;have hi := congrArg Complex.im hx;simp at hi;linarith)
  have hright := hg (fun y => (b : ℂ)+(y : ℂ)*I) (by fun_prop)
    (by intro y hy;have hr := congrArg Complex.re hy;simp at hr;exact hb hr)
  have hleft := hg (fun y => (a : ℂ)+(y : ℂ)*I) (by fun_prop)
    (by intro y hy;have hr := congrArg Complex.re hy;simp at hr;exact ha hr)
  exact ⟨hbot.intervalIntegrable a b,htop.intervalIntegrable a b,
    hright.intervalIntegrable (-T) T,hleft.intervalIntegrable (-T) T⟩

lemma lemma32_boundary_integral_add (f g : ℂ → ℂ) (a b T : ℝ)
    (hf : lemma32BoundaryIntegrable f a b T) (hg : lemma32BoundaryIntegrable g a b T) :
    lemma44GeneralRectangleBoundaryIntegral (fun w => f w+g w) a b T =
      lemma44GeneralRectangleBoundaryIntegral f a b T+lemma44GeneralRectangleBoundaryIntegral g a b T := by
  unfold lemma44GeneralRectangleBoundaryIntegral
  rw [intervalIntegral.integral_add hf.1 hg.1,intervalIntegral.integral_add hf.2.1 hg.2.1,
    intervalIntegral.integral_add hf.2.2.1 hg.2.2.1,intervalIntegral.integral_add hf.2.2.2 hg.2.2.2]
  ring

lemma lemma32_boundary_integral_const_mul (c : ℂ) (f : ℂ → ℂ) (a b T : ℝ) :
    lemma44GeneralRectangleBoundaryIntegral (fun w => c*f w) a b T =
      c*lemma44GeneralRectangleBoundaryIntegral f a b T := by
  unfold lemma44GeneralRectangleBoundaryIntegral
  simp only [intervalIntegral.integral_const_mul]
  ring

lemma lemma32_boundary_integral_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) (a b T : ℝ)
    (hf : ∀ k ∈ s, lemma32BoundaryIntegrable (f k) a b T) :
    lemma44GeneralRectangleBoundaryIntegral (fun w => ∑ k ∈ s, f k w) a b T =
      ∑ k ∈ s, lemma44GeneralRectangleBoundaryIntegral (f k) a b T := by
  unfold lemma44GeneralRectangleBoundaryIntegral
  rw [intervalIntegral.integral_finsetSum (fun k hk => (hf k hk).1),
    intervalIntegral.integral_finsetSum (fun k hk => (hf k hk).2.1),
    intervalIntegral.integral_finsetSum (fun k hk => (hf k hk).2.2.1),
    intervalIntegral.integral_finsetSum (fun k hk => (hf k hk).2.2.2)]
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.mul_sum]

end ZhangLS.Spec
