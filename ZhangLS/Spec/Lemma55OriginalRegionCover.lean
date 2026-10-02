import ZhangLS.Spec.Lemma55ActualLocalZeros
import ZhangLS.Spec.Lemma55

/-!
# A finite Jensen-disk covering of the original full zero region

A half-unit grid runs from -2D to 2D, including the height endpoints.
Every point in the original region with Re s≤1 belongs to one of the
closed Jensen disks, using its actual height to choose a natural index.
-/

namespace ZhangLS.Spec

open Complex Metric Set
open scoped Real

noncomputable def lemma55ZeroGridHeight (D j : ℕ) : ℝ := (j : ℝ) / 2 - 2 * (D : ℝ)

noncomputable def lemma55ZeroGridIndex (D : ℕ) (γ : ℝ) : ℕ :=
  ⌊2 * (γ + 2 * (D : ℝ))⌋₊

theorem lemma55_zero_grid_height_bound {D j : ℕ} (hj : j ≤ 8 * D) :
    |lemma55ZeroGridHeight D j| ≤ 2 * (D : ℝ) := by
  have hj' : (j : ℝ) ≤ 8 * (D : ℝ) := by exact_mod_cast hj
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  rw [abs_le]
  dsimp [lemma55ZeroGridHeight]
  constructor <;> linarith only [hj', hj0]

theorem lemma55_zero_grid_index_bound {D : ℕ} {γ : ℝ} (hγ : |γ| ≤ 2 * (D : ℝ)) :
    lemma55ZeroGridIndex D γ ≤ 8 * D := by
  have hlo := (abs_le.mp hγ).1
  have hhi := (abs_le.mp hγ).2
  have hp : 0 ≤ 2 * (γ + 2 * (D : ℝ)) := by linarith only [hlo]
  have hf := Nat.floor_le hp
  have hcast : (lemma55ZeroGridIndex D γ : ℝ) ≤ 8 * (D : ℝ) := by
    dsimp [lemma55ZeroGridIndex]
    linarith only [hf, hhi]
  exact_mod_cast hcast

theorem lemma55_zero_grid_height_approximation {D : ℕ} {γ : ℝ}
    (hγ : |γ| ≤ 2 * (D : ℝ)) :
    0 ≤ γ - lemma55ZeroGridHeight D (lemma55ZeroGridIndex D γ) ∧
      γ - lemma55ZeroGridHeight D (lemma55ZeroGridIndex D γ) < 1 / 2 := by
  have hlo := (abs_le.mp hγ).1
  have hp : 0 ≤ 2 * (γ + 2 * (D : ℝ)) := by linarith only [hlo]
  have hflo := Nat.floor_le hp
  have hfhi := Nat.lt_floor_add_one (2 * (γ + 2 * (D : ℝ)))
  dsimp [lemma55ZeroGridHeight, lemma55ZeroGridIndex]
  constructor <;> linarith only [hflo, hfhi]

theorem lemma55_original_region_disk_cover
    {D : ℕ} (hL : 2000 ≤ Real.log (D : ℝ)) {s : ℂ}
    (hs : Lemma55InZeroRegion D s) (hσ : s.re ≤ 1) :
    ∃ j : ℕ, j ≤ 8 * D ∧
      |lemma55ZeroGridHeight D j| ≤ 2 * (D : ℝ) ∧
      s ∈ closedBall (lemma55JensenCenter (lemma55ZeroGridHeight D j)) (5 / 4 : ℝ) := by
  have hγ : |s.im| ≤ 2 * (D : ℝ) := hs.2.le
  let j := lemma55ZeroGridIndex D s.im
  have hj : j ≤ 8 * D := lemma55_zero_grid_index_bound hγ
  have ht := lemma55_zero_grid_height_approximation hγ
  have hL20 : 20 ≤ Real.log (D : ℝ) := by linarith only [hL]
  have hinv := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 20) hL20
  have hleft : (9 : ℝ) / 10 ≤ s.re := by
    have h := hs.1
    rw [div_eq_mul_inv] at h hinv
    linarith only [h, hinv]
  have hre : |s.re - 2| ≤ (11 : ℝ) / 10 := by
    rw [abs_le]
    constructor <;> linarith only [hleft, hσ]
  have him : |s.im - lemma55ZeroGridHeight D j| ≤ (1 : ℝ) / 2 := by
    rw [abs_of_nonneg ht.1]
    exact ht.2.le
  have hreSq : (s.re - 2) ^ 2 ≤ (11 / 10 : ℝ) ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 11 / 10)).2 hre
    simpa only [sq_abs] using h
  have himSq : (s.im - lemma55ZeroGridHeight D j) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 2)).2 him
    simpa only [sq_abs] using h
  refine ⟨j, hj, lemma55_zero_grid_height_bound hj, ?_⟩
  rw [mem_closedBall_iff_norm]
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 5 / 4)).mp
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    lemma55_jensen_center_re, lemma55_jensen_center_im]
  nlinarith only [hreSq, himSq]

end ZhangLS.Spec
