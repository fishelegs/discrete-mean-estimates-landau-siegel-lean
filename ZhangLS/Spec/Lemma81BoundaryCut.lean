import ZhangLS.Spec.Lemma81ContourIntegrability

/-! # A separated real cut preserving strict zero membership

The construction also handles a zero exactly on the original cut: the upper
cut excludes that zero, and the lower-cut version excludes it from below.
No finite-set enumeration or zero-existence assumption is needed.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Set
set_option maxHeartbeats 2000000

lemma lemma81_separated_upper_cut (S : Set ℝ) {δ H : ℝ} (hδ : 0 < δ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ |x-y|) :
    ∃ B : ℝ, |B-H| ≤ δ/2 ∧ ∀ x ∈ S, δ/2 ≤ |x-B| ∧ (x < B ↔ x < H) := by
  classical
  by_cases hex : ∃ z ∈ S, |z-H| ≤ δ/2
  · obtain ⟨z,hz,hzH⟩ := hex
    have hzlo := (abs_le.mp hzH).1
    have hzhi := (abs_le.mp hzH).2
    by_cases hzlt : z < H
    · refine ⟨z+δ/2,abs_le.mpr ⟨by linarith,by linarith⟩,?_⟩
      intro x hx
      by_cases he : x = z
      · subst x
        refine ⟨?_,?_⟩
        · rw [show z-(z+δ/2) = -(δ/2) by ring,abs_neg,abs_of_pos (by positivity)]
        · constructor <;> intro h <;> linarith
      · have hd := hsep x hx z hz he
        rcases le_abs.mp hd with hh | hh
        · have hdist := le_abs_self (x-(z+δ/2))
          refine ⟨by linarith,?_⟩
          constructor <;> intro h <;> linarith
        · have hdist := neg_le_abs (x-(z+δ/2))
          refine ⟨by linarith,?_⟩
          constructor <;> intro h <;> linarith
    · have hzge : H ≤ z := le_of_not_gt hzlt
      refine ⟨z-δ/2,abs_le.mpr ⟨by linarith,by linarith⟩,?_⟩
      intro x hx
      by_cases he : x = z
      · subst x
        refine ⟨?_,?_⟩
        · rw [show z-(z-δ/2) = δ/2 by ring,abs_of_pos (by positivity)]
        · constructor <;> intro h <;> linarith
      · have hd := hsep x hx z hz he
        rcases le_abs.mp hd with hh | hh
        · have hdist := le_abs_self (x-(z-δ/2))
          refine ⟨by linarith,?_⟩
          constructor <;> intro h <;> linarith
        · have hdist := neg_le_abs (x-(z-δ/2))
          refine ⟨by linarith,?_⟩
          constructor <;> intro h <;> linarith
  · refine ⟨H,by simp; positivity,?_⟩
    intro x hx
    have hdist : δ/2 < |x-H| := lt_of_not_ge (fun hh => hex ⟨x,hx,hh⟩)
    exact ⟨hdist.le,Iff.rfl⟩

lemma lemma81_separated_lower_cut (S : Set ℝ) {δ H : ℝ} (hδ : 0 < δ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ |x-y|) :
    ∃ B : ℝ, |B-H| ≤ δ/2 ∧ ∀ x ∈ S, δ/2 ≤ |x-B| ∧ (B < x ↔ H < x) := by
  have hs : ∀ x ∈ {x : ℝ | -x ∈ S}, ∀ y ∈ {x : ℝ | -x ∈ S},
      x ≠ y → δ ≤ |x-y| := by
    intro x hx y hy hxy
    have hh := hsep (-x) hx (-y) hy (fun h => hxy (neg_injective h))
    simpa only [neg_sub_neg,abs_sub_comm] using hh
  obtain ⟨B,hB,hcut⟩ := lemma81_separated_upper_cut {x : ℝ | -x ∈ S} (H := -H) hδ hs
  refine ⟨-B,?_,?_⟩
  · have he : -B-H = -(B-(-H)) := by ring
    rw [he,abs_neg]
    exact hB
  · intro x hx
    have hh := hcut (-x) (by simpa using hx)
    constructor
    · have he : x-(-B) = -(-x-B) := by ring
      rw [he,abs_neg]
      exact hh.1
    · constructor
      · intro hb
        have hhx := hh.2.mp (by linarith only [hb])
        linarith only [hhx]
      · intro hxH
        have hhx := hh.2.mpr (by linarith only [hxH])
        linarith only [hhx]

end ZhangLS.Spec
