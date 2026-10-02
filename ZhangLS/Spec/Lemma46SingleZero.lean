import ZhangLS.Spec.Lemma23ModelRouche

/-! # Extracting simplicity and uniqueness from a multiplicity count of one -/

namespace ZhangLS.Spec

open Complex Metric Set Filter
open scoped Topology

set_option maxHeartbeats 1000000

/-- A disk with total zero multiplicity one has a unique simple zero.
Nonzero boundary values also exclude an identically zero analytic germ. -/
theorem lemma46_unique_simple_zero_of_count_one
    {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hboundary : ∀ z ∈ sphere (0 : ℂ) R, f z ≠ 0)
    (hcount :
      (∑ a ∈ (lemma23_support_finite_of_isCompact (isCompact_closedBall 0 R)
        (MeromorphicOn.divisor f (closedBall 0 R))).toFinset,
        (((MeromorphicOn.divisor f (closedBall 0 R)) a).toNat : ℂ)) = 1)
    {x : ℂ} (hx : x ∈ closedBall 0 R) (hzero : f x = 0) :
    deriv f x ≠ 0 ∧ ∀ y ∈ closedBall 0 R, f y = 0 → y = x := by
  classical
  let K : Set ℂ := closedBall 0 R
  let D := MeromorphicOn.divisor f K
  let hfin := lemma23_support_finite_of_isCompact (isCompact_closedBall 0 R) D
  let roots := hfin.toFinset
  have hnat : ∑ a ∈ roots, (D a).toNat = 1 := by
    change (∑ a ∈ roots, ((D a).toNat : ℂ)) = 1 at hcount
    exact_mod_cast hcount
  have hyR : (R : ℂ) ∈ sphere (0 : ℂ) R := by
    simp [mem_sphere, dist_zero_right, abs_of_pos hR]
  have hyK : (R : ℂ) ∈ K := sphere_subset_closedBall hyR
  have horderR : meromorphicOrderAt f (R : ℂ) ≠ ⊤ := by
    apply (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hf _ hyK).meromorphicAt).2
    exact eventually_nhdsWithin_of_eventually_nhds
      ((hf _ hyK).continuousAt.eventually_ne (hboundary _ hyR))
  have horders : ∀ z ∈ K, analyticOrderAt f z ≠ ⊤ := by
    intro z hz
    have hm := hf.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_closedBall (0 : ℂ) R).isPreconnected hyK hz horderR
    rw [(hf z hz).meromorphicOrderAt_eq] at hm
    intro he
    rw [he] at hm
    simp at hm
  have hmult (z : ℂ) (hz : z ∈ K) (hzz : f z = 0) :
      0 < (D z).toNat ∧ z ∈ roots ∧
        analyticOrderAt f z = ((D z).toNat : ℕ∞) := by
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (horders z hz)
    have hnpos : 0 < n := by
      have hh := (hf z hz).analyticOrderAt_ne_zero.mpr hzz
      rw [← hn] at hh
      exact Nat.pos_of_ne_zero (by intro he; simp [he] at hh)
    have hDz : D z = (n : ℤ) := by
      change MeromorphicOn.divisor f K z = _
      rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hf hz, ← hn]
      simp
    have hroot : z ∈ roots := by
      apply hfin.mem_toFinset.mpr
      apply Function.mem_support.mpr
      rw [hDz]
      exact_mod_cast hnpos.ne'
    exact ⟨by simpa [hDz] using hnpos, hroot, by simpa [hDz] using hn.symm⟩
  have hmx := hmult x hx hzero
  have hxle : (D x).toNat ≤ 1 := by
    rw [← hnat]
    exact Finset.single_le_sum (f := fun a => (D a).toNat)
      (fun a _ => Nat.zero_le ((D a).toNat)) hmx.2.1
  have hxone : (D x).toNat = 1 := by omega
  have hxorder : analyticOrderAt f x = 1 := by simpa [hxone] using hmx.2.2
  have hdorder : analyticOrderAt (deriv f) x = 0 :=
    analyticOrderAt_deriv_of_pos (hf x hx) (n := 0) (by simpa using hxorder)
  refine ⟨(hf x hx).deriv.analyticOrderAt_eq_zero.mp hdorder, ?_⟩
  intro y hy hyzero
  have hmy := hmult y hy hyzero
  by_contra hyx
  have hyerase : y ∈ roots.erase x := Finset.mem_erase.mpr ⟨hyx, hmy.2.1⟩
  have hsum := Finset.sum_erase_add roots (fun a => (D a).toNat) hmx.2.1
  dsimp only at hsum
  rw [hnat, hxone] at hsum
  have hyle : (D y).toNat ≤ ∑ a ∈ roots.erase x, (D a).toNat :=
    Finset.single_le_sum (f := fun a => (D a).toNat)
      (fun a _ => Nat.zero_le ((D a).toNat)) hyerase
  omega

end ZhangLS.Spec
