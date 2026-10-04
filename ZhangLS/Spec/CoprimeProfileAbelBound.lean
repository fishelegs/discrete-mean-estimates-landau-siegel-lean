import ZhangLS.Spec.CoprimeProfileAbelEuler
set_option autoImplicit false
namespace ZhangLS.Spec.CoprimeProfileAbel
open Finset Filter
open scoped Classical
set_option maxHeartbeats 2000000

lemma density_nonneg (D : ℕ) : 0 ≤ density D := by unfold density; positivity
lemma density_le_one {D : ℕ} (hD : 0 < D) : density D ≤ 1 := by
  unfold density
  exact (div_le_one (Nat.cast_pos.mpr hD)).mpr (Nat.cast_le.mpr (Nat.totient_le D))

lemma mainConstant_pos (D : ℕ) : 0 < mainConstant D := by
  unfold mainConstant
  apply mul_pos (by positivity)
  apply Finset.prod_pos
  intro p hp
  exact div_pos (Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors hp).pos) (by positivity)

lemma mainConstant_le_one (D : ℕ) : mainConstant D ≤ 1 := by
  have hb : 6 / Real.pi ^ 2 ≤ (1 : ℝ) := by
    apply (div_le_one (sq_pos_of_ne_zero Real.pi_ne_zero)).mpr
    nlinarith [Real.pi_gt_three]
  have hp : (∏ p ∈ D.primeFactors, (p : ℝ) / ((p : ℝ) + 1)) ≤ 1 := by
    calc
      _ ≤ ∏ _p ∈ D.primeFactors, (1 : ℝ) := by
        apply Finset.prod_le_prod
        · intros; positivity
        · intro p hp
          apply (div_le_one (by positivity : 0 < (p : ℝ) + 1)).mpr
          linarith
      _ = _ := by simp
  unfold mainConstant
  exact (mul_le_mul hb hp (by positivity) zero_le_one).trans_eq (by ring)

noncomputable def cumulativeMobius (D N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, mobiusWeight D n / (n : ℝ)

lemma cumulativeMobius_tendsto (D : ℕ) :
    Tendsto (cumulativeMobius D) atTop (nhds (∑' n : ℕ, mobiusWeight D n / (n : ℝ))) := by
  have ht := (mobius_square_summable D).hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  convert ht using 1
  funext M
  change cumulativeMobius D M = ∑ i ∈ range (M + 1), mobiusWeight D i / (i : ℝ)
  have hi : range (M + 1) = insert 0 (Ioc 0 M) := by
    ext n
    simp only [mem_range, mem_insert, mem_Ioc]
    omega
  rw [hi, Finset.sum_insert (by simp)]
  simp [cumulativeMobius, mobiusWeight]

lemma cumulativeMobius_difference (D : ℕ) {N M : ℕ} (hN : 0 < N) (hNM : N ≤ M) :
    |cumulativeMobius D M - cumulativeMobius D N| ≤ (N : ℝ)⁻¹ := by
  have hu : Ioc 0 M = Ioc 0 N ∪ Ioc N M := by
    ext n
    simp only [mem_Ioc, mem_union]
    omega
  have hd : Disjoint (Ioc 0 N) (Ioc N M) := by
    apply Finset.disjoint_left.mpr
    intro n hn hm
    simp only [mem_Ioc] at hn hm
    omega
  unfold cumulativeMobius
  rw [hu, Finset.sum_union hd, add_sub_cancel_left]
  calc
    _ ≤ ∑ n ∈ Ioc N M, |mobiusWeight D n / (n : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Ioc N M, ((n : ℝ) ^ 2)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      simp only [abs_div, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
      calc
        _ ≤ (n : ℝ)⁻¹ / (n : ℝ) :=
          div_le_div_of_nonneg_right (mobiusWeight_abs_le D n) (Nat.cast_nonneg n)
        _ = _ := by simp [div_eq_mul_inv, pow_two]
    _ ≤ (N : ℝ)⁻¹ - (M : ℝ)⁻¹ := sum_Ioc_inv_sq_le_sub hN.ne' hNM
    _ ≤ _ := sub_le_self _ (by positivity)

lemma cumulativeMobius_tail (D : ℕ) {N : ℕ} (hN : 0 < N) :
    |(∑' n : ℕ, mobiusWeight D n / (n : ℝ)) - cumulativeMobius D N| ≤ (N : ℝ)⁻¹ := by
  apply le_of_tendsto (((cumulativeMobius_tendsto D).sub_const _).abs)
  filter_upwards [eventually_ge_atTop N] with M hM
  exact cumulativeMobius_difference D hN hM

lemma summatory_integer_error {D N : ℕ} (hD : 0 < D) (hN : 0 < N) :
    |summatory D (N : ℝ) - mainConstant D * (N : ℝ)| ≤
      (D.divisors.card : ℝ) * (harmonic N : ℝ) + 1 := by
  have hfinite := finite_density_error hD N
  have htail := cumulativeMobius_tail D hN
  have hmain := total_density_eq_main hD
  have hdensity := density_nonneg D
  have hnR : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have he : summatory D (N : ℝ) - mainConstant D * (N : ℝ) =
      (summatory D (N : ℝ) - (N : ℝ) * truncatedDensity D N) +
      (N : ℝ) * density D * (cumulativeMobius D N - (∑' n : ℕ, mobiusWeight D n / (n : ℝ))) := by
    rw [← hmain, truncatedDensity, cumulativeMobius]
    ring
  rw [he]
  apply (abs_add_le _ _).trans
  apply add_le_add hfinite
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (N : ℝ) * density D), abs_sub_comm]
  calc
    _ ≤ (N : ℝ) * density D * (N : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left htail (by positivity)
    _ = density D := by field_simp
    _ ≤ 1 := density_le_one hD

/-- A stronger bound than the requested `(τ(D)+1)(1+log x)+2`, proved
for the actual inclusive positive coprime totient sum. -/
theorem summatory_error {D : ℕ} (hD : 0 < D) {x : ℝ} (hx : 1 ≤ x) :
    |summatory D x - mainConstant D * x| ≤
      (D.divisors.card : ℝ) * (1 + Real.log x) + 2 := by
  let N := ⌊x⌋₊
  have hN : 0 < N := Nat.floor_pos.mpr hx
  have hnle : (N : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hnlt : x < (N : ℝ) + 1 := Nat.lt_floor_add_one x
  have he : summatory D x = summatory D (N : ℝ) := by simp [summatory, N]
  rw [he]
  have hs := summatory_integer_error hD hN
  calc
    _ = |(summatory D (N : ℝ) - mainConstant D * (N : ℝ)) +
        mainConstant D * ((N : ℝ) - x)| := by congr 1; ring
    _ ≤ |summatory D (N : ℝ) - mainConstant D * (N : ℝ)| +
        |mainConstant D * ((N : ℝ) - x)| := abs_add_le _ _
    _ ≤ (D.divisors.card : ℝ) * (harmonic N : ℝ) + 1 + 1 := by
      apply add_le_add hs
      rw [abs_mul, abs_of_pos (mainConstant_pos D), abs_of_nonpos (sub_nonpos.mpr hnle)]
      have herr : -((N : ℝ) - x) ≤ 1 := by linarith
      exact (mul_le_mul (mainConstant_le_one D) herr (by linarith) zero_le_one).trans_eq (by ring)
    _ ≤ _ := by
      have hh : (harmonic N : ℝ) ≤ 1 + Real.log x := harmonic_floor_le_one_add_log x hx
      have hmul := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg D.divisors.card : (0 : ℝ) ≤ _)
      linarith

theorem requested_summatory_error {D : ℕ} (hD : 0 < D) {x : ℝ} (hx : 1 ≤ x) :
    |summatory D x - mainConstant D * x| ≤
      ((D.divisors.card : ℝ) + 1) * (1 + Real.log x) + 2 := by
  apply (summatory_error hD hx).trans
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  nlinarith

end ZhangLS.Spec.CoprimeProfileAbel
