import ZhangLS.Spec.Lemma101Definitions

set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace ZhangLS.Spec
open Complex Finset
open scoped Real

lemma lemma101_log_cutoff {D : ℕ} {y : ℝ} (hy : 0<y) (a : ℝ) :
    Real.log (lemma101Cutoff D y a) = a * Real.log (lemma23PaperP D) - Real.log y := by
  have hP : 0<lemma23PaperP D := Real.exp_pos _
  rw [lemma101Cutoff, Real.log_div (Real.rpow_pos_of_pos hP a).ne' hy.ne', Real.log_rpow hP]

lemma lemma101_cutoff_pos (D : ℕ) {y : ℝ} (hy : 0<y) (a : ℝ) :
    0<lemma101Cutoff D y a := div_pos (Real.rpow_pos_of_pos (Real.exp_pos _) _) hy

lemma lemma101_cutoff_mono {D : ℕ} (hD : 1<D) {y : ℝ} (hy : 0<y)
    {a b : ℝ} (hab : a≤b) : lemma101Cutoff D y a ≤ lemma101Cutoff D y b := by
  apply div_le_div_of_nonneg_right _ hy.le
  apply Real.rpow_le_rpow_of_exponent_le _ hab
  unfold lemma23PaperP
  exact Real.one_le_exp (pow_nonneg (Real.log_nonneg (by exact_mod_cast hD.le)) _)

lemma lemma101_positive_log_sum {D : ℕ} (χ : RealPrimitiveCharacter D)
    {x : ℝ} (hx : 0<x) (N : ℕ) (hN : ⌊x⌋₊≤N) (s : ℂ) :
    (∑ n ∈ Finset.Icc 1 N,
      χ.evalNat n * (n:ℂ)^(-s) * (max (Real.log (x/(n:ℝ))) 0:ℝ)) =
      lemma82WeightedPolynomial χ x s := by
  unfold lemma82WeightedPolynomial
  symm
  calc
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ.evalNat n * (n:ℂ)^(-s) * (Real.log (x/(n:ℝ)):ℂ)) =
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ.evalNat n * (n:ℂ)^(-s) * (max (Real.log (x/(n:ℝ))) 0:ℝ) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hn0 : (0:ℝ)<n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      have hnx : (n:ℝ)≤x := (Nat.le_floor_iff hx.le).mp (Finset.mem_Icc.mp hn).2
      rw [max_eq_left (Real.log_nonneg ((le_div_iff₀ hn0).mpr (by simpa using hnx)))]
    _ = _ := by
      apply Finset.sum_subset (Finset.Icc_subset_Icc le_rfl hN)
      intro n hn hnnot
      have hn0 : (0:ℝ)<n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      have hnx : x<(n:ℝ) := by
        have hnot : ¬n≤⌊x⌋₊ := fun hh => hnnot (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,hh⟩)
        exact (Nat.floor_lt hx.le).mp (lt_of_not_ge hnot)
      rw [max_eq_right (Real.log_nonpos (div_nonneg hx.le hn0.le)
        ((div_le_one hn0).mpr hnx.le))]
      simp

lemma lemma101_tent_log_kernel {D : ℕ} (hD : 1<D) {y : ℝ} (hy : 0<y)
    {n : ℕ} (hn : 0<n) :
    lemma111Tent (Real.log (y*(n:ℝ))/Real.log (lemma23PaperP D)) =
      500/Real.log (lemma23PaperP D) *
        (max (Real.log (lemma101Cutoff D y (63/125)/(n:ℝ))) 0 -
          2*max (Real.log (lemma101Cutoff D y (251/500)/(n:ℝ))) 0 +
          max (Real.log (lemma101Cutoff D y (1/2)/(n:ℝ))) 0) := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have hL : 0<Real.log (lemma23PaperP D) := by
    simp only [lemma23PaperP,Real.log_exp]
    exact pow_pos (Real.log_pos (by exact_mod_cast hD)) _
  have he (a : ℝ) : a-Real.log (y*(n:ℝ))/Real.log (lemma23PaperP D) =
      Real.log (lemma101Cutoff D y a/(n:ℝ))/Real.log (lemma23PaperP D) := by
    rw [Real.log_div (lemma101_cutoff_pos D hy a).ne' hn0.ne', lemma101_log_cutoff hy,
      Real.log_mul hy.ne' hn0.ne']
    field_simp
    ring
  rw [lemma111_tent_second_difference, he, he, he]
  have hm (z : ℝ) : max (z / Real.log (lemma23PaperP D)) 0 =
      max z 0 / Real.log (lemma23PaperP D) := by
    simpa only [zero_div] using max_div_div_right hL.le z 0
  rw [hm, hm, hm]
  ring

lemma lemma101_sum_exact_bridge {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (c : ℝ) (j : Fin 3) {y : ℝ} (hy : 0<y) :
    lemma101Sum χ c j y = (500/(Real.log (lemma23PaperP D):ℂ)) *
      (lemma82WeightedPolynomial χ (lemma101Cutoff D y (63/125)) (1-lemma82PaperBeta D c j) -
        2*lemma82WeightedPolynomial χ (lemma101Cutoff D y (251/500)) (1-lemma82PaperBeta D c j) +
        lemma82WeightedPolynomial χ (lemma101Cutoff D y (1/2)) (1-lemma82PaperBeta D c j)) := by
  unfold lemma101Sum
  simp_rw [← lemma101_positive_log_sum χ (lemma101_cutoff_pos D hy (63/125)) _ le_rfl]
  rw [← lemma101_positive_log_sum χ (lemma101_cutoff_pos D hy (251/500)) _
    (Nat.floor_mono (lemma101_cutoff_mono hD hy (by norm_num : (251/500:ℝ)≤63/125))),
    ← lemma101_positive_log_sum χ (lemma101_cutoff_pos D hy (1/2)) _
    (Nat.floor_mono (lemma101_cutoff_mono hD hy (by norm_num : (1/2:ℝ)≤63/125)))]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 := (Finset.mem_Icc.mp hn).1
  rw [lemma101_tent_log_kernel hD hy hn0]
  simp only [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_add,
    Complex.ofReal_ofNat, div_eq_mul_inv, ← Complex.cpow_neg, Complex.ofReal_inv]
  ring

lemma lemma101_weighted_zero_of_le_one {D : ℕ} (χ : RealPrimitiveCharacter D)
    {x : ℝ} (hx : 0<x) (hx1 : x≤1) (s : ℂ) :
    lemma82WeightedPolynomial χ x s = 0 := by
  unfold lemma82WeightedPolynomial
  apply Finset.sum_eq_zero
  intro n hn
  have hn0 : 0<n := (Finset.mem_Icc.mp hn).1
  have hnx : (n:ℝ)≤x := (Nat.le_floor_iff hx.le).mp (Finset.mem_Icc.mp hn).2
  have hn1 : n=1 := by
    have h : (n:ℝ)≤1 := hnx.trans hx1
    exact Nat.le_antisymm (by exact_mod_cast h) hn0
  subst n
  have hx' : x=1 := le_antisymm hx1 (by simpa using hnx)
  simp [hx']

lemma lemma101_tent_zero_of_ge {u : ℝ} (hu : 63/125≤u) : lemma111Tent u=0 := by
  unfold lemma111Tent
  split_ifs with h₁ h₂ h₃
  · linarith
  · linarith
  · have he : u=63/125 := le_antisymm h₃ hu
    rw [he]
    ring
  · rfl

lemma lemma101_term_zero_beyond_support {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (c : ℝ) (j : Fin 3) {y : ℝ} (hy : 0<y)
    {n : ℕ} (hn : 0<n) (hcut : lemma101Cutoff D y (63/125)≤(n:ℝ)) :
    χ.evalNat n/(n:ℂ)^(1-lemma82PaperBeta D c j)*
      (lemma111Tent (Real.log (y*(n:ℝ))/Real.log (lemma23PaperP D)):ℂ)=0 := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hP : 0<lemma23PaperP D := Real.exp_pos _
  have hlogP : 0<Real.log (lemma23PaperP D) := by
    rw [lemma23PaperP,Real.log_exp]
    exact pow_pos (Real.log_pos (by exact_mod_cast hD)) _
  have hmul : lemma23PaperP D^(63/125:ℝ)≤y*(n:ℝ) := by
    have hh := (div_le_iff₀ hy).mp hcut
    simpa only [mul_comm] using hh
  have hh := Real.log_le_log (Real.rpow_pos_of_pos hP (63/125)) hmul
  rw [Real.log_rpow hP] at hh
  have ht : (63/125:ℝ)≤Real.log (y*(n:ℝ))/Real.log (lemma23PaperP D) :=
    (le_div_iff₀ hlogP).mpr hh
  rw [lemma101_tent_zero_of_ge ht]
  simp

/-- Equality with the literal sum over all natural-number coefficients; zero
and the included top endpoint make no contribution. -/
lemma lemma101_sum_eq_tsum {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (c : ℝ) (j : Fin 3) {y : ℝ} (hy : 0<y) :
    lemma101Sum χ c j y = ∑' n : ℕ,
      χ.evalNat n/(n:ℂ)^(1-lemma82PaperBeta D c j)*
        (lemma111Tent (Real.log (y*(n:ℝ))/Real.log (lemma23PaperP D)):ℂ) := by
  unfold lemma101Sum
  symm
  apply tsum_eq_sum
  intro n hn
  by_cases hn0 : n=0
  · subst n
    simp [lemma111Tent]
  · have hnpos : 0<n := Nat.pos_of_ne_zero hn0
    have hfloor : ⌊lemma101Cutoff D y (63/125)⌋₊<n := by
      apply lt_of_not_ge
      intro hle
      exact hn (Finset.mem_Icc.mpr ⟨hnpos,hle⟩)
    exact lemma101_term_zero_beyond_support χ hD c j hy hnpos
      ((Nat.floor_lt (lemma101_cutoff_pos D hy (63/125)).le).mp hfloor).le

end ZhangLS.Spec
