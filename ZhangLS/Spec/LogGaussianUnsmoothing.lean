import ZhangLS.Spec.LogGaussianComparison
import ZhangLS.Spec.Lemma171GaussianUnsmoothing

/-! Weighted short comparison and summable far tail, without an assumed Mellin error. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex MeasureTheory Filter
open scoped Topology

lemma lemma171_log_short_smoothed_error {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 3 ≤ lemma23PaperL D)
    (hT : 5 * lemma23PaperL D ≤ Real.log (lemma56PaperT D)) :
    |(∑ n ∈ Finset.Icc 1 (D ^ 4), lemma171LogSmoothedTerm χ n) -
      ∑ n ∈ Finset.Icc 1 (D ^ 4), lemma171Coefficient χ n / (n : ℝ) * Real.log (lemma56PaperT D / n)| ≤
        lemma23PaperL D ^ (-180 : ℤ) := by
  let L := lemma23PaperL D
  have hL0 : 0 < L := by linarith
  have hDp : (0 : ℝ) < D := by exact_mod_cast Nat.zero_lt_of_lt hD
  have hdiff : |(∑ n ∈ Finset.Icc 1 (D ^ 4), lemma171LogSmoothedTerm χ n) -
      ∑ n ∈ Finset.Icc 1 (D ^ 4), lemma171Coefficient χ n / (n : ℝ) * Real.log (lemma56PaperT D / n)| ≤
        (D : ℝ) ^ 8 * Real.exp (-(L ^ 16)) := by
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ n ∈ Finset.Icc 1 (D ^ 4), |lemma171LogSmoothedTerm χ n -
          lemma171Coefficient χ n / (n : ℝ) * Real.log (lemma56PaperT D / n)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _n ∈ Finset.Icc 1 (D ^ 4), (D : ℝ) ^ 4 * Real.exp (-(L ^ 16)) := by
        apply Finset.sum_le_sum
        intro n hn
        have hcoef : lemma171Coefficient χ n / (n : ℝ) ≤ (D : ℝ) ^ 4 :=
          (lemma171_harmonic_coefficient_le_nat χ n).trans (by exact_mod_cast (Finset.mem_Icc.mp hn).2)
        have hc0 : 0 ≤ lemma171Coefficient χ n / (n : ℝ) :=
          div_nonneg (lemma171_coefficient_nonneg χ n) (Nat.cast_nonneg n)
        rw [lemma171LogSmoothedTerm,lemma171WeightArgument,
          show lemma171Coefficient χ n / (n : ℝ) * lemma171LogGaussianWeight D (lemma56PaperT D / n) -
              lemma171Coefficient χ n / (n : ℝ) * Real.log (lemma56PaperT D / n) =
            (lemma171Coefficient χ n / (n : ℝ)) *
              (lemma171LogGaussianWeight D (lemma56PaperT D / n) - Real.log (lemma56PaperT D / n)) by ring,
          abs_mul,abs_of_nonneg hc0]
        exact mul_le_mul hcoef (lemma171_log_gaussian_short_weight_error hD hL hT hn)
          (abs_nonneg _) (by positivity)
      _ = _ := by
        simp [Finset.sum_const,Nat.card_Icc]
        ring
  calc
    _ ≤ (D : ℝ) ^ 8 * Real.exp (-(L ^ 16)) := hdiff
    _ = Real.exp (8 * L - L ^ 16) := by
      have heD : Real.exp L = (D : ℝ) := Real.exp_log hDp
      rw [← heD,← Real.exp_nat_mul,← Real.exp_add]
      norm_num
      congr 1
    _ ≤ Real.exp (-180 * Real.log L) := by
      apply Real.exp_le_exp.mpr
      have hlog := Real.log_le_sub_one_of_pos hL0
      have h5 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hL 5
      have h6 : 188 * L ≤ L ^ 6 := by
        calc
          _ ≤ L ^ 5 * L := by norm_num at h5; nlinarith only [h5,hL0]
          _ = _ := by ring
      have h616 : L ^ 6 ≤ L ^ 16 := pow_le_pow_right₀ (by linarith) (by norm_num)
      linarith only [hlog,h6,h616,hL0]
    _ = L ^ (-180 : ℤ) := by
      rw [← Real.rpow_intCast,Real.rpow_def_of_pos hL0]
      congr 1
      norm_num
      ring

lemma lemma171_log_far_tail_term_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 3 ≤ lemma23PaperL D) (n : ℕ) :
    |if ⌊lemma23PaperP D ^ 2⌋₊ < n then lemma171LogSmoothedTerm χ n else 0| ≤
      lemma23PaperL D ^ (-180 : ℤ) * ((n : ℝ) ^ 2)⁻¹ := by
  split_ifs with hn
  · have hnp : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
    rw [abs_of_nonneg (lemma171_log_smoothed_term_nonneg χ hD n)]
    unfold lemma171LogSmoothedTerm lemma171WeightArgument
    calc
      _ ≤ (n : ℝ) * (Real.exp (-(lemma23PaperL D ^ 24) / 10) * ((n : ℝ) ^ 3)⁻¹) :=
        mul_le_mul (lemma171_harmonic_coefficient_le_nat χ n) (lemma171_log_gaussian_tail_weight hD hL hn)
          (lemma171_log_gaussian_weight_nonneg hD (div_pos (Real.exp_pos _) hnp)) hnp.le
      _ = Real.exp (-(lemma23PaperL D ^ 24) / 10) * ((n : ℝ) ^ 2)⁻¹ := by
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (lemma44_gaussian_tail_budget hL) (by positivity)
  · simp only [abs_zero]
    positivity

lemma lemma171_log_far_tail_summable_and_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 3 ≤ lemma23PaperL D) :
    Summable (fun n : ℕ => if ⌊lemma23PaperP D ^ 2⌋₊ < n then lemma171LogSmoothedTerm χ n else 0) ∧
      |∑' n : ℕ, if ⌊lemma23PaperP D ^ 2⌋₊ < n then lemma171LogSmoothedTerm χ n else 0| ≤
        lemma44InverseSquareMass * lemma23PaperL D ^ (-180 : ℤ) := by
  have hmajor := lemma44_inverse_square_summable.mul_left (lemma23PaperL D ^ (-180 : ℤ))
  have habs : Summable (fun n : ℕ =>
      |if ⌊lemma23PaperP D ^ 2⌋₊ < n then lemma171LogSmoothedTerm χ n else 0|) :=
    hmajor.of_nonneg_of_le (fun n => abs_nonneg _)
      (lemma171_log_far_tail_term_bound χ hD hL)
  have hnorm : Summable (fun n : ℕ =>
      ‖if ⌊lemma23PaperP D ^ 2⌋₊ < n then lemma171LogSmoothedTerm χ n else 0‖) := by
    simpa only [Real.norm_eq_abs] using habs
  refine ⟨hnorm.of_norm,?_⟩
  calc
    _ ≤ ∑' n : ℕ, |if ⌊lemma23PaperP D ^ 2⌋₊ < n then lemma171LogSmoothedTerm χ n else 0| := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, lemma23PaperL D ^ (-180 : ℤ) * ((n : ℝ) ^ 2)⁻¹ :=
      habs.tsum_le_tsum (lemma171_log_far_tail_term_bound χ hD hL) hmajor
    _ = _ := by rw [tsum_mul_left]; exact mul_comm _ _

lemma lemma171_log_smoothed_decomposition {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 3 ≤ lemma23PaperL D) :
    lemma171LogSmoothedSum χ =
      (∑ n ∈ Finset.Icc 1 (D ^ 4), lemma171LogSmoothedTerm χ n) +
      (∑ n ∈ Finset.Ioc (D ^ 4) ⌊lemma23PaperP D ^ 2⌋₊, lemma171LogSmoothedTerm χ n) +
      ∑' n : ℕ, if ⌊lemma23PaperP D ^ 2⌋₊ < n then lemma171LogSmoothedTerm χ n else 0 := by
  classical
  let f := lemma171LogSmoothedTerm χ
  let S := Finset.Icc 1 (D ^ 4)
  let M := Finset.Ioc (D ^ 4) ⌊lemma23PaperP D ^ 2⌋₊
  let short : ℕ → ℝ := fun n => if n ∈ S then f n else 0
  let middle : ℕ → ℝ := fun n => if n ∈ M then f n else 0
  let tail : ℕ → ℝ := fun n => if ⌊lemma23PaperP D ^ 2⌋₊ < n then f n else 0
  have hshort : Summable short :=
    summable_of_ne_finset_zero (s := S) (by intro n hn; simp [short,hn])
  have hmiddle : Summable middle :=
    summable_of_ne_finset_zero (s := M) (by intro n hn; simp [middle,hn])
  have htail : Summable tail := (lemma171_log_far_tail_summable_and_bound χ hD hL).1
  have hcut : D ^ 4 ≤ ⌊lemma23PaperP D ^ 2⌋₊ := by
    apply (Nat.le_floor_iff (by positivity)).mpr
    simpa only [Nat.cast_pow] using lemma44_D4_le_P2 χ hL
  have hpoint (n : ℕ) : f n = short n + middle n + tail n := by
    by_cases hn : n = 0
    · subst n
      simp [f,short,middle,tail,S,M,lemma171LogSmoothedTerm]
    dsimp [short,middle,tail,S,M]
    simp only [Finset.mem_Icc,Finset.mem_Ioc]
    by_cases hns : n ≤ D ^ 4
    · simp [hns,Nat.one_le_iff_ne_zero.mpr hn,
        not_lt.mpr hns,not_lt.mpr (hns.trans hcut)]
    · have hnD : D ^ 4 < n := Nat.lt_of_not_ge hns
      by_cases hnM : n ≤ ⌊lemma23PaperP D ^ 2⌋₊
      · simp [hns,hnD,hnM,not_lt.mpr hnM]
      · simp [hns,hnD,hnM,Nat.lt_of_not_ge hnM]
  have hshortsum : (∑' n : ℕ, short n) = ∑ n ∈ S, f n := by
    rw [tsum_eq_sum (s := S) (by intro n hn; simp [short,hn])]
    exact Finset.sum_congr rfl (fun n hn => by simp only [short,if_pos hn])
  have hmiddlesum : (∑' n : ℕ, middle n) = ∑ n ∈ M, f n := by
    rw [tsum_eq_sum (s := M) (by intro n hn; simp [middle,hn])]
    exact Finset.sum_congr rfl (fun n hn => by simp only [middle,if_pos hn])
  change (∑' n : ℕ, f n) = _
  simp_rw [hpoint]
  rw [(hshort.add hmiddle).tsum_add htail,hshort.tsum_add hmiddle,hshortsum,hmiddlesum]


lemma lemma171_log_unsmoothing_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 3 ≤ lemma23PaperL D)
    (hT : 5 * lemma23PaperL D ≤ Real.log (lemma56PaperT D))
    (hA : NormalizedAssumptionA χ)
    (hAbs : (Real.sqrt (D : ℝ))⁻¹ ≤ lemma23PaperL D ^ (-2013 : ℤ)) :
    |lemma171LogSmoothedSum χ -
      (Real.log (lemma56PaperT D) * lemma171ShortHarmonicSum χ - lemma171FirstLogMoment χ)| ≤
      (1 + lemma44InverseSquareMass) * lemma23PaperL D ^ (-180 : ℤ) +
      2520 * lemma23PaperL D ^ (-2002 : ℤ) + lemma23PaperL D ^ 9 * (D : ℝ) ^ (-4 : ℤ) := by
  let A := ∑ n ∈ Finset.Icc 1 (D ^ 4), lemma171LogSmoothedTerm χ n
  let B := ∑ n ∈ Finset.Ioc (D ^ 4) ⌊lemma23PaperP D ^ 2⌋₊, lemma171LogSmoothedTerm χ n
  let C := ∑' n : ℕ, if ⌊lemma23PaperP D ^ 2⌋₊ < n then lemma171LogSmoothedTerm χ n else 0
  let H := ∑ n ∈ Finset.Icc 1 (D ^ 4), lemma171Coefficient χ n / (n : ℝ) *
    Real.log (lemma56PaperT D / n)
  let E := (Real.log (lemma56PaperT D) - 4 * lemma23PaperL D) * (D : ℝ) ^ (-4 : ℤ)
  have hs := lemma171_log_short_smoothed_error χ hD hL hT
  change |A - H| ≤ _ at hs
  have hb := lemma171_log_middle_smoothed_tail_le χ hD (by linarith) hA hAbs
  change B ≤ _ at hb
  have hb0 : 0 ≤ B := Finset.sum_nonneg (fun n _ => lemma171_log_smoothed_term_nonneg χ hD n)
  have hc := (lemma171_log_far_tail_summable_and_bound χ hD hL).2
  change |C| ≤ _ at hc
  have he : H = Real.log (lemma56PaperT D) * lemma171ShortHarmonicSum χ -
      lemma171FirstLogMoment χ + E := lemma171_log_strict_cutoff_endpoint χ
  have hE0 : 0 ≤ E := by dsimp [E]; apply mul_nonneg _ (by positivity); linarith
  have hEle : E ≤ lemma23PaperL D ^ 9 * (D : ℝ) ^ (-4 : ℤ) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have ht := lemma171_log_T_le (D := D) (by linarith)
    linarith
  have hd : lemma171LogSmoothedSum χ = A + B + C := lemma171_log_smoothed_decomposition χ hD hL
  rw [hd]
  calc
    _ = |((A - H) + B + C) + E| := by congr 1; linarith only [he]
    _ ≤ |A - H| + |B| + |C| + |E| := by
      have h₁ := abs_add_le (A - H) B
      have h₂ := abs_add_le (A - H + B) C
      have h₃ := abs_add_le (A - H + B + C) E
      linarith only [h₁, h₂, h₃]
    _ ≤ lemma23PaperL D ^ (-180 : ℤ) + 2520 * lemma23PaperL D ^ (-2002 : ℤ) +
        lemma44InverseSquareMass * lemma23PaperL D ^ (-180 : ℤ) +
        lemma23PaperL D ^ 9 * (D : ℝ) ^ (-4 : ℤ) := by
      rw [abs_of_nonneg hb0, abs_of_nonneg hE0]
      gcongr
    _ = _ := by ring

end ZhangLS.Spec
