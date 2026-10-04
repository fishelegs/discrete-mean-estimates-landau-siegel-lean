import ZhangLS.Spec.RamifiedHeadHarmonicCharacter

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Finset
open scoped Classical

noncomputable def ramifiedHeadPairs (D X : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 X) ×ˢ (Icc 1 X)).filter (fun dm => D ∣ dm.1 * dm.2)

noncomputable def ramifiedHeadSplit (D : ℕ) (dm : ℕ × ℕ) : ℕ × (ℕ × ℕ) :=
  let g := Nat.gcd dm.1 D
  (g, dm.1 / g, dm.2 / (D / g))

lemma ramifiedHead_split_data {D X : ℕ} (hD : 0 < D) {dm : ℕ × ℕ}
    (h : dm ∈ ramifiedHeadPairs D X) :
    let t := ramifiedHeadSplit D dm
    t.1 ∈ D.divisors ∧ t.2.1 ∈ Icc 1 X ∧ t.2.2 ∈ Icc 1 X ∧
      t.1*t.2.1 = dm.1 ∧ (D/t.1)*t.2.2 = dm.2 := by
  obtain ⟨hdm, hdiv⟩ := mem_filter.mp h
  obtain ⟨hd, hm⟩ := mem_product.mp hdm
  obtain ⟨hd1, hdX⟩ := mem_Icc.mp hd
  obtain ⟨hm1, hmX⟩ := mem_Icc.mp hm
  let g := Nat.gcd dm.1 D
  have hg : 0 < g := Nat.gcd_pos_of_pos_right _ hD
  have hgd : g ∣ dm.1 := Nat.gcd_dvd_left _ _
  have hgD : g ∣ D := Nat.gcd_dvd_right _ _
  have hdg : g*(dm.1/g) = dm.1 := Nat.mul_div_cancel' hgd
  have hDg : g*(D/g) = D := Nat.mul_div_cancel' hgD
  have hcop : (dm.1/g).Coprime (D/g) :=
    Nat.gcd_div_gcd_div_gcd_of_pos_right hD
  have hdiv' : D/g ∣ (dm.1/g)*dm.2 := by
    apply Nat.dvd_of_mul_dvd_mul_left hg
    rwa [← mul_assoc, hdg, hDg]
  have hqm : D/g ∣ dm.2 := hcop.symm.dvd_of_dvd_mul_left hdiv'
  have hq : 0 < D/g := Nat.div_pos (Nat.le_of_dvd hD hgD) hg
  have ha : 0 < dm.1/g := Nat.div_pos (Nat.le_of_dvd hd1 hgd) hg
  have hb : 0 < dm.2/(D/g) := Nat.div_pos (Nat.le_of_dvd hm1 hqm) hq
  change g ∈ D.divisors ∧ dm.1/g ∈ Icc 1 X ∧ dm.2/(D/g) ∈ Icc 1 X ∧
    g*(dm.1/g)=dm.1 ∧ (D/g)*(dm.2/(D/g))=dm.2
  exact ⟨Nat.mem_divisors.mpr ⟨hgD, hD.ne'⟩,
    mem_Icc.mpr ⟨ha, (Nat.div_le_self _ _).trans hdX⟩,
    mem_Icc.mpr ⟨hb, (Nat.div_le_self _ _).trans hmX⟩,
    hdg, Nat.mul_div_cancel' hqm⟩

/-- The gcd split is injective because it retains both original coordinates. -/
lemma ramifiedHead_split_injective {D X : ℕ} (hD : 0 < D) :
    Set.InjOn (ramifiedHeadSplit D) (ramifiedHeadPairs D X) := by
  intro x hx y hy he
  have hx' := ramifiedHead_split_data hD hx
  have hy' := ramifiedHead_split_data hD hy
  apply Prod.ext
  · calc
      x.1 = (ramifiedHeadSplit D x).1 * (ramifiedHeadSplit D x).2.1 := hx'.2.2.2.1.symm
      _ = (ramifiedHeadSplit D y).1 * (ramifiedHeadSplit D y).2.1 := by rw [he]
      _ = y.1 := hy'.2.2.2.1
  · calc
      x.2 = (D/(ramifiedHeadSplit D x).1) * (ramifiedHeadSplit D x).2.2 := hx'.2.2.2.2.symm
      _ = (D/(ramifiedHeadSplit D y).1) * (ramifiedHeadSplit D y).2.2 := by rw [he]
      _ = y.2 := hy'.2.2.2.2

/-- All pairs are retained, including zero-valued coefficients and prime-power
conductors; only nonnegative extra fibres are added. -/
theorem ramifiedHead_reindex_le {D X : ℕ} (hD : 0 < D)
    (W : ℕ × ℕ → ℝ) (F : ℕ → ℕ → ℕ → ℝ)
    (hF : ∀ g ∈ D.divisors, ∀ a ∈ Icc 1 X, ∀ b ∈ Icc 1 X, 0 ≤ F g a b)
    (hW : ∀ dm ∈ ramifiedHeadPairs D X,
      W dm ≤ F (ramifiedHeadSplit D dm).1
        (ramifiedHeadSplit D dm).2.1 (ramifiedHeadSplit D dm).2.2) :
    (∑ dm ∈ ramifiedHeadPairs D X, W dm) ≤
      ∑ g ∈ D.divisors, ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X, F g a b := by
  let S := D.divisors ×ˢ ((Icc 1 X) ×ˢ (Icc 1 X))
  let f : ℕ × (ℕ × ℕ) → ℝ := fun t => F t.1 t.2.1 t.2.2
  have hsub : (ramifiedHeadPairs D X).image (ramifiedHeadSplit D) ⊆ S := by
    intro t ht
    obtain ⟨dm, hdm, rfl⟩ := mem_image.mp ht
    have hh := ramifiedHead_split_data hD hdm
    exact mem_product.mpr ⟨hh.1, mem_product.mpr ⟨hh.2.1, hh.2.2.1⟩⟩
  calc
    _ ≤ ∑ dm ∈ ramifiedHeadPairs D X, f (ramifiedHeadSplit D dm) := sum_le_sum hW
    _ = ∑ t ∈ (ramifiedHeadPairs D X).image (ramifiedHeadSplit D), f t :=
      (sum_image (ramifiedHead_split_injective hD)).symm
    _ ≤ ∑ t ∈ S, f t := by
      apply sum_le_sum_of_subset_of_nonneg hsub
      intro t ht _
      obtain ⟨hg, hab⟩ := mem_product.mp ht
      obtain ⟨ha, hb⟩ := mem_product.mp hab
      exact hF t.1 hg t.2.1 ha t.2.2 hb
    _ = _ := by simp only [S, f, sum_product]

end ZhangLS.Spec
