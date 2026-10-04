import ZhangLS.Spec.FixedHProfileNormalization

/-! The literal affine rescaling, including its zero endpoints. -/
set_option autoImplicit false
namespace ZhangLS.Spec.FixedHProfile
open Set Function
open scoped Classical ContDiff
set_option maxHeartbeats 2000000

noncomputable def f (x : ℝ) : ℝ := F0 (2000 * (x - 251 / 500))

lemma f_contDiff : ContDiff ℝ ∞ f := by
  exact F0_contDiff.comp (contDiff_const.mul (contDiff_id.sub contDiff_const))

lemma f_abs_le_one (x : ℝ) : |f x| ≤ 1 := F0_abs_le_one _

lemma f_tsupport : tsupport f ⊆ Set.Icc (251 / 500 : ℝ) (201 / 400) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have hm := F0_tsupport (subset_tsupport _ hx)
  change 0 ≤ 2000 * (x - 251 / 500) ∧ 2000 * (x - 251 / 500) ≤ 1 at hm
  constructor <;> linarith [hm.1, hm.2]

lemma f_hasCompactSupport : HasCompactSupport f := by
  exact isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) f_tsupport

lemma supported_endpoints {K : ℝ → ℝ} {a b : ℝ}
    (hK : Continuous K) (hs : Function.support K ⊆ Set.Icc a b) : K a = 0 ∧ K b = 0 := by
  have hclosed : IsClosed {t : ℝ | K t = 0} := isClosed_eq hK continuous_const
  have hl : Set.Iio a ⊆ {t : ℝ | K t = 0} := by
    intro t ht
    by_contra hn
    exact (not_le_of_gt ht) (hs hn).1
  have hr : Set.Ioi b ⊆ {t : ℝ | K t = 0} := by
    intro t ht
    by_contra hn
    exact (not_le_of_gt ht) (hs hn).2
  constructor
  · exact hclosed.closure_subset_iff.mpr hl (by simp [closure_Iio])
  · exact hclosed.closure_subset_iff.mpr hr (by simp [closure_Ioi])

lemma F0_endpoints : F0 0 = 0 ∧ F0 1 = 0 :=
  supported_endpoints F0_contDiff.continuous (fun _ h => F0_tsupport (subset_tsupport _ h))

lemma f_endpoints : f (251 / 500) = 0 ∧ f (201 / 400) = 0 :=
  supported_endpoints f_contDiff.continuous (fun _ h => f_tsupport (subset_tsupport _ h))

lemma f_support : Function.support f ⊆ Set.Ioo (251 / 500 : ℝ) (201 / 400) := by
  intro x hx
  have hm := f_tsupport (subset_tsupport _ hx)
  constructor
  · apply lt_of_le_of_ne hm.1
    intro he
    exact hx (he ▸ f_endpoints.1)
  · apply lt_of_le_of_ne hm.2
    intro he
    exact hx (he.symm ▸ f_endpoints.2)

lemma f_not_zero : ∃ x : ℝ, f x ≠ 0 := by
  obtain ⟨v, hv⟩ := F0_not_zero
  refine ⟨v / 2000 + 251 / 500, ?_⟩
  have he : 2000 * (v / 2000 + 251 / 500 - 251 / 500) = v := by ring
  simpa only [f, he] using hv

lemma f_eq_zero_of_le {x : ℝ} (hx : x ≤ 251 / 500) : f x = 0 := by
  by_contra h
  exact (not_lt_of_ge hx) (f_support h).1

lemma f_eq_zero_of_ge {x : ℝ} (hx : 201 / 400 ≤ x) : f x = 0 := by
  by_contra h
  exact (not_lt_of_ge hx) (f_support h).2

end ZhangLS.Spec.FixedHProfile
