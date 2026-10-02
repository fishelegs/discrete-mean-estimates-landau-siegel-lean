import ZhangLS.Spec.Lemma32DistinctRootFieldSize
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma32_quadratic_unpaired_quartic_collision_bound {F : Type*}
    [Field F] [Fintype F] (χ : MulChar F ℂ) (hn : χ ≠ 1) (hq : χ^2=1)
    (a b c d : F)
    (hpaired : ¬ ((a=b ∧ c=d) ∨ (a=c ∧ b=d) ∨ (a=d ∧ b=c)))
    (hrepeat : a=b ∨ a=c ∨ a=d ∨ b=c ∨ b=d ∨ c=d) :
    ‖∑ x : F, χ (lemma32QuarticRootProduct a b c d x)‖ ≤ 2 := by
  have haux (r s t : F) (hst : s ≠ t)
      (hid : ∀ x : F, lemma32QuarticRootProduct a b c d x =
        (x+r)^2*(x+s)*(x+t)) :
      ‖∑ x : F, χ (lemma32QuarticRootProduct a b c d x)‖ ≤ 2 := by
    have he : (∑ x : F, χ (lemma32QuarticRootProduct a b c d x)) =
        ∑ x : F, χ ((x+r)^2*(x+s)*(x+t)) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [hid x]
    rw [he]
    exact lemma32_quadratic_repeated_root_correlation_norm χ hn hq r s t hst
  rcases hrepeat with hab | hac | had | hbc | hbd | hcd
  · have hst : c ≠ d := by
      intro h
      exact hpaired (Or.inl ⟨hab,h⟩)
    apply haux a c d hst
    intro x
    unfold lemma32QuarticRootProduct
    rw [← hab]
    ring
  · have hst : b ≠ d := by
      intro h
      exact hpaired (Or.inr (Or.inl ⟨hac,h⟩))
    apply haux a b d hst
    intro x
    unfold lemma32QuarticRootProduct
    rw [← hac]
    ring
  · have hst : b ≠ c := by
      intro h
      exact hpaired (Or.inr (Or.inr ⟨had,h⟩))
    apply haux a b c hst
    intro x
    unfold lemma32QuarticRootProduct
    rw [← had]
    ring
  · have hst : a ≠ d := by
      intro h
      exact hpaired (Or.inr (Or.inr ⟨h,hbc⟩))
    apply haux b a d hst
    intro x
    unfold lemma32QuarticRootProduct
    rw [← hbc]
    ring
  · have hst : a ≠ c := by
      intro h
      exact hpaired (Or.inr (Or.inl ⟨h,hbd⟩))
    apply haux b a c hst
    intro x
    unfold lemma32QuarticRootProduct
    rw [← hbd]
    ring
  · have hst : a ≠ b := by
      intro h
      exact hpaired (Or.inl ⟨h,hcd⟩)
    apply haux c a b hst
    intro x
    unfold lemma32QuarticRootProduct
    rw [← hcd]
    ring

end ZhangLS.Spec
