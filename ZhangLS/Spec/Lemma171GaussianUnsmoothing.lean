import ZhangLS.Spec.Lemma171GaussianTail
import ZhangLS.Spec.Lemma171GaussianComparison

/-! # Actual short and far-tail Gaussian errors for Lemma 17.1

The original coefficient ν(n)²/n and the paper's scale T are used throughout.
The lower segment and the infinite tail above P² have uniform explicit bounds.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Filter
open scoped Topology
set_option maxHeartbeats 2000000

lemma lemma171_short_smoothed_error {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 3 ≤ lemma23PaperL D)
    (hT : 5 * lemma23PaperL D ≤ Real.log (lemma56PaperT D)) :
    |(∑ n ∈ Finset.Icc 1 (D ^ 4), lemma171SmoothedTerm χ n) -
      ∑ n ∈ Finset.Icc 1 (D ^ 4), lemma171Coefficient χ n / (n : ℝ)| ≤
        lemma23PaperL D ^ (-180 : ℤ) := by
  let L := lemma23PaperL D
  have hL0 : 0 < L := by linarith
  have hDp : (0 : ℝ) < D := by exact_mod_cast Nat.zero_lt_of_lt hD
  have hdiff : |(∑ n ∈ Finset.Icc 1 (D ^ 4), lemma171SmoothedTerm χ n) -
      ∑ n ∈ Finset.Icc 1 (D ^ 4), lemma171Coefficient χ n / (n : ℝ)| ≤
        (D : ℝ) ^ 8 * Real.exp (-(L ^ 16)) := by
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ n ∈ Finset.Icc 1 (D ^ 4), |lemma171SmoothedTerm χ n -
          lemma171Coefficient χ n / (n : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _n ∈ Finset.Icc 1 (D ^ 4), (D : ℝ) ^ 4 * Real.exp (-(L ^ 16)) := by
        apply Finset.sum_le_sum
        intro n hn
        have hcoef : lemma171Coefficient χ n / (n : ℝ) ≤ (D : ℝ) ^ 4 :=
          (lemma171_harmonic_coefficient_le_nat χ n).trans (by exact_mod_cast (Finset.mem_Icc.mp hn).2)
        have hc0 : 0 ≤ lemma171Coefficient χ n / (n : ℝ) :=
          div_nonneg (lemma171_coefficient_nonneg χ n) (Nat.cast_nonneg n)
        rw [lemma171SmoothedTerm,lemma171WeightArgument,
          show lemma171Coefficient χ n / (n : ℝ) * zhangGaussianWeight D (lemma56PaperT D / n) -
              lemma171Coefficient χ n / (n : ℝ) =
            (lemma171Coefficient χ n / (n : ℝ)) *
              (zhangGaussianWeight D (lemma56PaperT D / n) - 1) by ring,
          abs_mul,abs_of_nonneg hc0]
        exact mul_le_mul hcoef (lemma171_gaussian_short_weight_error hD hL hT hn)
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

lemma lemma171_far_tail_term_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 3 ≤ lemma23PaperL D) (n : ℕ) :
    |if ⌊lemma23PaperP D ^ 2⌋₊ < n then lemma171SmoothedTerm χ n else 0| ≤
      lemma23PaperL D ^ (-180 : ℤ) * ((n : ℝ) ^ 2)⁻¹ := by
  split_ifs with hn
  · have hnp : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
    rw [abs_of_nonneg (lemma171_smoothed_term_nonneg χ hD n)]
    unfold lemma171SmoothedTerm lemma171WeightArgument
    calc
      _ ≤ (n : ℝ) * (Real.exp (-(lemma23PaperL D ^ 24) / 10) * ((n : ℝ) ^ 3)⁻¹) :=
        mul_le_mul (lemma171_harmonic_coefficient_le_nat χ n) (lemma171_gaussian_tail_weight hL hn)
          (zhangGaussianWeight_nonneg hD (div_pos (Real.exp_pos _) hnp)) hnp.le
      _ = Real.exp (-(lemma23PaperL D ^ 24) / 10) * ((n : ℝ) ^ 2)⁻¹ := by
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (lemma44_gaussian_tail_budget hL) (by positivity)
  · simp only [abs_zero]
    positivity

lemma lemma171_far_tail_summable_and_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 3 ≤ lemma23PaperL D) :
    Summable (fun n : ℕ => if ⌊lemma23PaperP D ^ 2⌋₊ < n then lemma171SmoothedTerm χ n else 0) ∧
      |∑' n : ℕ, if ⌊lemma23PaperP D ^ 2⌋₊ < n then lemma171SmoothedTerm χ n else 0| ≤
        lemma44InverseSquareMass * lemma23PaperL D ^ (-180 : ℤ) := by
  have hmajor := lemma44_inverse_square_summable.mul_left (lemma23PaperL D ^ (-180 : ℤ))
  have habs : Summable (fun n : ℕ =>
      |if ⌊lemma23PaperP D ^ 2⌋₊ < n then lemma171SmoothedTerm χ n else 0|) :=
    hmajor.of_nonneg_of_le (fun n => abs_nonneg _)
      (lemma171_far_tail_term_bound χ hD hL)
  have hnorm : Summable (fun n : ℕ =>
      ‖if ⌊lemma23PaperP D ^ 2⌋₊ < n then lemma171SmoothedTerm χ n else 0‖) := by
    simpa only [Real.norm_eq_abs] using habs
  refine ⟨hnorm.of_norm,?_⟩
  calc
    _ ≤ ∑' n : ℕ, |if ⌊lemma23PaperP D ^ 2⌋₊ < n then lemma171SmoothedTerm χ n else 0| := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, lemma23PaperL D ^ (-180 : ℤ) * ((n : ℝ) ^ 2)⁻¹ :=
      habs.tsum_le_tsum (lemma171_far_tail_term_bound χ hD hL) hmajor
    _ = _ := by rw [tsum_mul_left]; exact mul_comm _ _

lemma lemma171_smoothed_decomposition {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 3 ≤ lemma23PaperL D) :
    lemma171SmoothedSum χ =
      (∑ n ∈ Finset.Icc 1 (D ^ 4), lemma171SmoothedTerm χ n) +
      (∑ n ∈ Finset.Ioc (D ^ 4) ⌊lemma23PaperP D ^ 2⌋₊, lemma171SmoothedTerm χ n) +
      ∑' n : ℕ, if ⌊lemma23PaperP D ^ 2⌋₊ < n then lemma171SmoothedTerm χ n else 0 := by
  classical
  let f := lemma171SmoothedTerm χ
  let S := Finset.Icc 1 (D ^ 4)
  let M := Finset.Ioc (D ^ 4) ⌊lemma23PaperP D ^ 2⌋₊
  let short : ℕ → ℝ := fun n => if n ∈ S then f n else 0
  let middle : ℕ → ℝ := fun n => if n ∈ M then f n else 0
  let tail : ℕ → ℝ := fun n => if ⌊lemma23PaperP D ^ 2⌋₊ < n then f n else 0
  have hshort : Summable short :=
    summable_of_ne_finset_zero (s := S) (by intro n hn; simp [short,hn])
  have hmiddle : Summable middle :=
    summable_of_ne_finset_zero (s := M) (by intro n hn; simp [middle,hn])
  have htail : Summable tail := (lemma171_far_tail_summable_and_bound χ hD hL).1
  have hcut : D ^ 4 ≤ ⌊lemma23PaperP D ^ 2⌋₊ := by
    apply (Nat.le_floor_iff (by positivity)).mpr
    simpa only [Nat.cast_pow] using lemma44_D4_le_P2 χ hL
  have hpoint (n : ℕ) : f n = short n + middle n + tail n := by
    by_cases hn : n = 0
    · subst n
      simp [f,short,middle,tail,S,M,lemma171SmoothedTerm]
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

lemma lemma171_unsmoothing_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 3 ≤ lemma23PaperL D)
    (hT : 5 * lemma23PaperL D ≤ Real.log (lemma56PaperT D))
    (hA : NormalizedAssumptionA χ)
    (hAbs : (Real.sqrt (D : ℝ))⁻¹ ≤ lemma23PaperL D ^ (-2013 : ℤ)) :
    |lemma171SmoothedSum χ - lemma171ShortHarmonicSum χ| ≤
      (1 + lemma44InverseSquareMass) * lemma23PaperL D ^ (-180 : ℤ) +
      1260 * lemma23PaperL D ^ (-2011 : ℤ) + (D : ℝ) ^ (-4 : ℤ) := by
  let A := ∑ n ∈ Finset.Icc 1 (D ^ 4), lemma171SmoothedTerm χ n
  let B := ∑ n ∈ Finset.Ioc (D ^ 4) ⌊lemma23PaperP D ^ 2⌋₊, lemma171SmoothedTerm χ n
  let C := ∑' n : ℕ, if ⌊lemma23PaperP D ^ 2⌋₊ < n then lemma171SmoothedTerm χ n else 0
  let H := ∑ n ∈ Finset.Icc 1 (D ^ 4), lemma171Coefficient χ n / (n : ℝ)
  have hs := lemma171_short_smoothed_error χ hD hL hT
  change |A - H| ≤ _ at hs
  have hb := lemma171_middle_smoothed_tail_le χ hD (by linarith) hA hAbs
  change B ≤ _ at hb
  have hb0 : 0 ≤ B := Finset.sum_nonneg (fun n _ => lemma171_smoothed_term_nonneg χ hD n)
  have hc := (lemma171_far_tail_summable_and_bound χ hD hL).2
  change |C| ≤ _ at hc
  have he : H = lemma171ShortHarmonicSum χ + (D : ℝ) ^ (-4 : ℤ) :=
    lemma171_strict_cutoff_endpoint χ
  have hd : lemma171SmoothedSum χ = A + B + C := lemma171_smoothed_decomposition χ hD hL
  rw [hd]
  calc
    _ = |((A - H) + B + C) + (D : ℝ) ^ (-4 : ℤ)| := by congr 1; linarith only [he]
    _ ≤ |A - H| + |B| + |C| + |(D : ℝ) ^ (-4 : ℤ)| := by
      have h₁ := abs_add_le (A - H) B
      have h₂ := abs_add_le (A - H + B) C
      have h₃ := abs_add_le (A - H + B + C) ((D : ℝ) ^ (-4 : ℤ))
      linarith only [h₁,h₂,h₃]
    _ ≤ lemma23PaperL D ^ (-180 : ℤ) + 1260 * lemma23PaperL D ^ (-2011 : ℤ) +
        lemma44InverseSquareMass * lemma23PaperL D ^ (-180 : ℤ) + (D : ℝ) ^ (-4 : ℤ) := by
      rw [abs_of_nonneg hb0,abs_of_nonneg (by positivity : 0 ≤ (D : ℝ) ^ (-4 : ℤ))]
      gcongr
    _ = _ := by ring

lemma lemma171_unsmoothing_uniform :
    ∀ ε : ℝ, 0 < ε → ∃ D₀ : ℕ, 2 ≤ D₀ ∧
      ∀ D : ℕ, D₀ ≤ D → ∀ χ : RealPrimitiveCharacter D,
        NormalizedAssumptionA χ → |lemma171SmoothedSum χ - lemma171ShortHarmonicSum χ| < ε := by
  intro ε hε
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have h180 : Tendsto (fun D : ℕ => lemma23PaperL D ^ (-180 : ℤ)) atTop (𝓝 0) :=
    (tendsto_zpow_atTop_zero (by norm_num : (-180 : ℤ) < 0)).comp ht
  have h2011 : Tendsto (fun D : ℕ => lemma23PaperL D ^ (-2011 : ℤ)) atTop (𝓝 0) :=
    (tendsto_zpow_atTop_zero (by norm_num : (-2011 : ℤ) < 0)).comp ht
  have h4 : Tendsto (fun D : ℕ => (D : ℝ) ^ (-4 : ℤ)) atTop (𝓝 0) :=
    (tendsto_zpow_atTop_zero (by norm_num : (-4 : ℤ) < 0)).comp tendsto_natCast_atTop_atTop
  have hb : Tendsto (fun D : ℕ =>
      (1 + lemma44InverseSquareMass) * lemma23PaperL D ^ (-180 : ℤ) +
      1260 * lemma23PaperL D ^ (-2011 : ℤ) + (D : ℝ) ^ (-4 : ℤ)) atTop (𝓝 0) := by
    simpa only [mul_zero,add_zero] using
      ((h180.const_mul (1 + lemma44InverseSquareMass)).add (h2011.const_mul 1260)).add h4
  obtain ⟨D₁,hD₁⟩ := eventually_atTop.mp (hb.eventually (eventually_lt_nhds hε))
  obtain ⟨D₂,hD₂,hscale⟩ := lemma171_smoothing_scale_threshold
  obtain ⟨D₃,habs⟩ := lemma31_exponential_absorption_threshold
  refine ⟨max D₂ (max D₁ D₃),hD₂.trans (le_max_left _ _),?_⟩
  intro D hD χ hA
  have h2 : D₂ ≤ D := (le_max_left _ _).trans hD
  have h1 : D₁ ≤ D := (le_max_left D₁ D₃).trans ((le_max_right _ _).trans hD)
  have h3 : D₃ ≤ D := (le_max_right D₁ D₃).trans ((le_max_right _ _).trans hD)
  exact (lemma171_unsmoothing_bound χ (habs D h3).1 (hscale D h2).1
    (hscale D h2).2 hA (habs D h3).2.2).trans_lt (hD₁ D h1)

end ZhangLS.Spec
