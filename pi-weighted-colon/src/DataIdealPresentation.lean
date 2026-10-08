import WeightedColon
import Mathlib.RingTheory.Ideal.Maps

noncomputable section

namespace PiWeightedColon

open Polynomial

def mono {R : Type*} [Semiring R] (k c : ℕ) : Bivariate R :=
  monomial k (monomial c 1)

theorem mono_mul {R : Type*} [CommSemiring R] (k c l e : ℕ) :
    mono (R := R) k c * mono l e = mono (k + l) (c + e) := by
  simp [mono, monomial_mul_monomial]

theorem data_mono {R : Type*} [CommRing R] {d m k c : ℕ}
    (h : m ≤ weight d k c) : Data d m (coeff (mono (R := R) k c)) := by
  intro l e hle
  by_cases hl : k = l
  · subst l
    have hc : c ≠ e := by intro he; subst e; omega
    simp [coeff, mono, Polynomial.coeff_monomial, hc]
  · simp [coeff, mono, Polynomial.coeff_monomial, hl]

theorem data_product {R : Type*} [CommRing R] {d m n : ℕ}
    (a f : Bivariate R) (ha : Data d m (coeff a)) (hf : Data d n (coeff f)) :
    Data d (m + n) (coeff (a * f)) := by
  intro k c hkc
  unfold coeff
  rw [Polynomial.coeff_mul, Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro ij hij
  rw [Polynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro uv huv
  have hk := Finset.mem_antidiagonal.mp hij
  have hc := Finset.mem_antidiagonal.mp huv
  have hc' : uv.1 / d + uv.2 / d ≤ c / d := by
    rw [← hc]
    exact Nat.add_div_le_add_div _ _ _
  by_cases hl : weight d ij.1 uv.1 < m
  · change coeff a ij.1 uv.1 * coeff f ij.2 uv.2 = 0
    rw [ha _ _ hl, zero_mul]
  · have hr : weight d ij.2 uv.2 < n := by simp only [weight] at *; omega
    change coeff a ij.1 uv.1 * coeff f ij.2 uv.2 = 0
    rw [hf _ _ hr, mul_zero]

theorem dataIdeal_mul_le {R : Type*} [CommRing R] (d m n : ℕ) :
    dataIdeal R d m * dataIdeal R d n ≤ dataIdeal R d (m + n) := by
  apply Ideal.mul_le.mpr
  intro a ha f hf
  exact data_product a f ha hf

theorem dataIdeal_le_of_mono {R : Type*} [CommRing R] {d m : ℕ}
    (I : Ideal (Bivariate R))
    (hI : ∀ k c, m ≤ weight d k c → mono (R := R) k c ∈ I) :
    dataIdeal R d m ≤ I := by
  intro f hf
  rw [← sum_monomial_eq f, sum_def]
  apply I.sum_mem
  intro k _
  rw [← sum_monomial_eq (f.coeff k), sum_def, map_sum]
  apply I.sum_mem
  intro c hc
  have hw : m ≤ weight d k c := by
    by_contra h
    exact mem_support_iff.mp hc (hf k c (by omega))
  have hmem := I.mul_mem_left (C (C (coeff f k c))) (hI k c hw)
  simpa only [mono, C_mul_monomial, mul_one, coeff] using hmem

def localJ (R : Type*) [CommRing R] (d : ℕ) : Ideal (Bivariate R) :=
  Ideal.span {mono 1 0, mono 0 d}

def localK (R : Type*) [CommRing R] (d : ℕ) : Ideal (Bivariate R) :=
  Ideal.span {mono 2 0, mono 0 d}

theorem mono_mem_localJK {R : Type*} [CommRing R] {d : ℕ} (hd : 0 < d) :
    ∀ N k c, 2 * N + 1 ≤ weight d k c →
      mono (R := R) k c ∈ localJ R d * localK R d ^ N := by
  intro N
  induction N with
  | zero =>
    intro k c hw
    rw [Submodule.pow_zero, Ideal.IsTwoSided.mul_one]
    by_cases hk : 1 ≤ k
    · have hg : mono (R := R) 1 0 ∈ localJ R d := Ideal.subset_span (by simp)
      have h := (localJ R d).mul_mem_left (mono (R := R) (k - 1) c) hg
      simpa only [mono_mul, show k - 1 + 1 = k by omega, add_zero] using h
    · have hc : d ≤ c := by
        have hq : 1 ≤ c / d := by simp only [weight] at hw; omega
        simpa using (Nat.le_div_iff_mul_le hd).mp hq
      have hg : mono (R := R) 0 d ∈ localJ R d := Ideal.subset_span (by simp)
      have h := (localJ R d).mul_mem_left (mono (R := R) k (c - d)) hg
      simpa only [mono_mul, add_zero, show c - d + d = c by omega] using h
  | succ N ih =>
    intro k c hw
    rw [Submodule.pow_succ, ← Ideal.mul_assoc]
    by_cases hk : 2 ≤ k
    · have hw' : 2 * N + 1 ≤ weight d (k - 2) c := by simp only [weight] at *; omega
      have hg : mono (R := R) 2 0 ∈ localK R d := Ideal.subset_span (by simp)
      have h := Ideal.mul_mem_mul (ih (k - 2) c hw') hg
      simpa only [mono_mul, show k - 2 + 2 = k by omega, add_zero] using h
    · have hc : d ≤ c := by
        have hq : 1 ≤ c / d := by simp only [weight] at hw; omega
        simpa using (Nat.le_div_iff_mul_le hd).mp hq
      have hdiv : (c - d) / d + 1 = c / d := (Nat.div_eq_sub_div hd hc).symm
      have hw' : 2 * N + 1 ≤ weight d k (c - d) := by simp only [weight] at *; omega
      have hg : mono (R := R) 0 d ∈ localK R d := Ideal.subset_span (by simp)
      have h := Ideal.mul_mem_mul (ih k (c - d) hw') hg
      simpa only [mono_mul, add_zero, show c - d + d = c by omega] using h

theorem localJ_le_dataIdeal {R : Type*} [CommRing R] {d : ℕ} (hd : 0 < d) :
    localJ R d ≤ dataIdeal R d 1 := by
  apply Ideal.span_le.mpr
  intro f hf
  rcases Set.mem_insert_iff.mp hf with rfl | hf
  · exact data_mono (by simp [weight])
  · have he := Set.mem_singleton_iff.mp hf
    subst f
    exact data_mono (by simp [weight, Nat.div_self hd])

theorem localK_le_dataIdeal {R : Type*} [CommRing R] {d : ℕ} (hd : 0 < d) :
    localK R d ≤ dataIdeal R d 2 := by
  apply Ideal.span_le.mpr
  intro f hf
  rcases Set.mem_insert_iff.mp hf with rfl | hf
  · exact data_mono (by simp [weight])
  · have he := Set.mem_singleton_iff.mp hf
    subst f
    exact data_mono (by simp [weight, Nat.div_self hd])

/-- Membership in `(x,y^d) * (x²,y^d)^N` is exactly vanishing below weight
`2N+1`. The reverse inclusion expands an arbitrary polynomial in its actual
nonzero coefficients and factors each eligible monomial into the generators. -/
theorem localJK_eq_dataIdeal {R : Type*} [CommRing R] {d : ℕ} (hd : 0 < d) (N : ℕ) :
    localJ R d * localK R d ^ N = dataIdeal R d (2 * N + 1) := by
  apply le_antisymm
  · induction N with
    | zero => simpa only [Submodule.pow_zero, Ideal.IsTwoSided.mul_one, Nat.mul_zero, Nat.zero_add] using localJ_le_dataIdeal (R := R) hd
    | succ N ih =>
      rw [Submodule.pow_succ, ← Ideal.mul_assoc]
      have h := (Ideal.mul_mono ih (localK_le_dataIdeal (R := R) hd)).trans
        (dataIdeal_mul_le (R := R) d (2 * N + 1) 2)
      have ht : (2 * N + 1) + 2 = 2 * (N + 1) + 1 := by omega
      rwa [ht] at h
  · exact dataIdeal_le_of_mono _ (mono_mem_localJK hd N)

theorem localJK_colon {R : Type*} [CommRing R] {d : ℕ}
    (hd : d = 1 ∨ d = 3) (N : ℕ) :
    (localJ R d * localK R d ^ (N + 1)).colon {localQ R} =
      localJ R d * localK R d ^ N := by
  have hd' : 0 < d := by rcases hd with rfl | rfl <;> omega
  rw [localJK_eq_dataIdeal hd', localJK_eq_dataIdeal hd']
  have ht : 2 * (N + 1) + 1 = (2 * N + 1) + 2 := by omega
  rw [ht]
  exact dataIdeal_colon hd

end PiWeightedColon
