import ZhangLS.Spec.ActualGramRamp
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.DenselyOrdered

/-! Fixed smooth profiles supply their own derivative traces and bounded
norms. These constants are chosen from the profile before D and chi; no
D-dependent cutoff or growing superposition coefficient is introduced. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace ZhangLS.Spec
open Complex Set Function
open scoped Classical ContDiff

/-- Continuity and closed support force zero traces at both endpoints. -/
lemma actualGram_zero_on_closed_exterior (f : ℝ → ℂ) (hf : Continuous f)
    {a b : ℝ} (hs : tsupport f ⊆ Icc a b) (x : ℝ) (hx : x≤a ∨ b≤x) : f x=0 := by
  by_contra hn
  have hm : x ∈ support f := hn
  have hsub : support f ⊆ interior (Icc a b) :=
    hf.isOpen_support.subset_interior_iff.mpr ((subset_tsupport f).trans hs)
  have hi := hsub hm
  rw [interior_Icc] at hi
  rcases hx with hx | hx <;> linarith [hi.1,hi.2]

/-- The original C-infinity profile gives actual first and second derivatives,
with the same closed support window. -/
theorem actualGram_smooth_profile_derivatives (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    {a b : ℝ} (hs : tsupport f ⊆ Icc a b) :
    (∀ x, HasDerivAt f (deriv f x) x) ∧
    (∀ x, HasDerivAt (deriv f) (deriv (deriv f) x) x) ∧
    Continuous (deriv (deriv f)) ∧
    tsupport (deriv f) ⊆ Icc a b ∧ tsupport (deriv (deriv f)) ⊆ Icc a b := by
  have h1 := (contDiff_infty_iff_deriv.mp hf).2
  have h2 := (contDiff_infty_iff_deriv.mp h1).2
  have hs1 : tsupport (deriv f) ⊆ Icc a b := tsupport_deriv_subset.trans hs
  exact ⟨fun x => ((contDiff_infty_iff_deriv.mp hf).1 x).hasDerivAt,
    fun x => ((contDiff_infty_iff_deriv.mp h1).1 x).hasDerivAt,
    h2.continuous,hs1,tsupport_deriv_subset.trans hs1⟩

/-- Both terminal traces and the whole density exterior vanish exactly. -/
theorem actualGram_smooth_profile_traces (ell : ℂ) (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    {a b : ℝ} (hs : tsupport f ⊆ Icc a b) :
    (∀ x, x≤a ∨ b≤x → f x=0) ∧
    (∀ x, x≤a ∨ b≤x → deriv f x=0) ∧
    (∀ x, x≤a ∨ b≤x → actualGramRampDensity ell f (deriv f) (deriv (deriv f)) x=0) := by
  have h1 := (contDiff_infty_iff_deriv.mp hf).2
  have h2 := (contDiff_infty_iff_deriv.mp h1).2
  have hd := actualGram_smooth_profile_derivatives f hf hs
  have hz0 := actualGram_zero_on_closed_exterior f hf.continuous hs
  have hz1 := actualGram_zero_on_closed_exterior (deriv f) h1.continuous hd.2.2.2.1
  have hz2 := actualGram_zero_on_closed_exterior (deriv (deriv f)) h2.continuous hd.2.2.2.2
  refine ⟨hz0,hz1,?_⟩
  intro x hx
  simp [actualGramRampDensity,hz0 x hx,hz1 x hx,hz2 x hx]

/-- One fixed global derivative bound is obtained from compactness of the
profile window. Its existential quantifier has no arithmetic parameters. -/
theorem actualGram_smooth_profile_global_bound (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    {a b : ℝ} (hs : tsupport f ⊆ Icc a b) :
    ∃ C : ℝ, 0<C ∧ ∀ x : ℝ, ‖f x‖+‖deriv f x‖+‖deriv (deriv f) x‖≤C := by
  have h1 := (contDiff_infty_iff_deriv.mp hf).2
  have h2 := (contDiff_infty_iff_deriv.mp h1).2
  have hc : Continuous (fun x : ℝ => ‖f x‖+‖deriv f x‖+‖deriv (deriv f) x‖) :=
    (hf.continuous.norm.add h1.continuous.norm).add h2.continuous.norm
  obtain ⟨M,hM⟩ := (isCompact_Icc : IsCompact (Icc a b)).bddAbove_image hc.continuousOn
  refine ⟨max M 1,lt_of_lt_of_le (by norm_num : (0 : ℝ)<1) (le_max_right _ _),?_⟩
  intro x
  by_cases hx : x ∈ Icc a b
  · exact (hM (mem_image_of_mem _ hx)).trans (le_max_left _ _)
  · have hex : x≤a ∨ b≤x := by
      simp only [mem_Icc,not_and_or,not_le] at hx
      rcases hx with hx | hx
      · exact Or.inl hx.le
      · exact Or.inr hx.le
    have hd := actualGram_smooth_profile_derivatives f hf hs
    have hz0 := actualGram_zero_on_closed_exterior f hf.continuous hs x hex
    have hz1 := actualGram_zero_on_closed_exterior (deriv f) h1.continuous hd.2.2.2.1 x hex
    have hz2 := actualGram_zero_on_closed_exterior (deriv (deriv f)) h2.continuous hd.2.2.2.2 x hex
    simp only [hz0,hz1,hz2,norm_zero,zero_add]
    exact (by norm_num : (0 : ℝ)≤1).trans (le_max_right _ _)

/-- The ramp density has a D-free global bound for every fixed original ell.
The same construction is available for the opposite/conjugate smoothing shift. -/
theorem actualGram_smooth_profile_density_bound (ell : ℂ) (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    {a b : ℝ} (hs : tsupport f ⊆ Icc a b) :
    ∃ C : ℝ, 0<C ∧ ∀ x : ℝ,
      ‖actualGramRampDensity ell f (deriv f) (deriv (deriv f)) x‖≤C := by
  obtain ⟨K,hK,hbound⟩ := actualGram_smooth_profile_global_bound f hf hs
  refine ⟨K*(1+2*‖ell‖+‖ell‖^2),by positivity,?_⟩
  intro x
  have h0 : ‖f x‖≤K := by nlinarith [hbound x,norm_nonneg (deriv f x),norm_nonneg (deriv (deriv f) x)]
  have h1 : ‖deriv f x‖≤K := by nlinarith [hbound x,norm_nonneg (f x),norm_nonneg (deriv (deriv f) x)]
  have h2 : ‖deriv (deriv f) x‖≤K := by nlinarith [hbound x,norm_nonneg (f x),norm_nonneg (deriv f x)]
  unfold actualGramRampDensity
  calc
    _ ≤ ‖deriv (deriv f) x‖+‖2*ell*deriv f x‖+‖ell^2*f x‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = ‖deriv (deriv f) x‖+2*‖ell‖*‖deriv f x‖+‖ell‖^2*‖f x‖ := by
      simp only [norm_mul,norm_pow,Complex.norm_ofNat]
    _ ≤ K+2*‖ell‖*K+‖ell‖^2*K := add_le_add (add_le_add h2
      (mul_le_mul_of_nonneg_left h1 (by positivity))) (mul_le_mul_of_nonneg_left h0 (sq_nonneg _))
    _ = _ := by ring

end ZhangLS.Spec
