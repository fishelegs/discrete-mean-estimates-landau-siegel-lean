import ZhangLS.Spec.SquareNuTailLinear
import ZhangLS.Spec.SquareNuTailMajorantDefs
import ZhangLS.Spec.SquareNuTailMajorantLift
import ZhangLS.Spec.SquareNuTailMajorantLocal
import ZhangLS.Spec.SquareNuTailMajorant
import ZhangLS.Spec.SquareNuTailConvolution
import ZhangLS.Spec.SquareNuTailConvolutionSquare
import ZhangLS.Spec.SquareNuTailConvolutionActual
import ZhangLS.Spec.SquareNuTailConvolutionCapstone
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Finset

/-- Exact real strict-cutoff indexing, including integral endpoints. -/
lemma squareNuTailLinear_filter_eq_Ioc {A : ℝ} (hA : 0 ≤ A) (N : ℕ) :
    ((Finset.Icc 1 N).filter (fun n : ℕ => A < (n : ℝ))) = Finset.Ioc ⌊A⌋₊ N := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc, Nat.floor_lt hA]
  constructor
  · exact fun h => ⟨h.2, h.1.2⟩
  · intro h
    have hn : 0 < n := by exact_mod_cast (lt_of_le_of_lt hA h.1)
    exact ⟨⟨by omega, h.2⟩, h.1⟩

/-- No term at the lower endpoint enters the tail. -/
lemma squareNuTailLinear_endpoint_zero {D : ℕ} (χ : RealPrimitiveCharacter D) :
    (∑ n ∈ Finset.Ioc ⌊(D : ℝ) ^ (21 / 20 : ℝ)⌋₊
      ⌊(D : ℝ) ^ (21 / 20 : ℝ)⌋₊, lemma31NuReal χ n * (n : ℝ)⁻¹) = 0 := by
  simp

/-- The first integer strictly above the lower real endpoint occurs exactly once. -/
lemma squareNuTailLinear_first_term {D : ℕ} (χ : RealPrimitiveCharacter D) :
    (∑ n ∈ Finset.Ioc ⌊(D : ℝ) ^ (21 / 20 : ℝ)⌋₊
      (⌊(D : ℝ) ^ (21 / 20 : ℝ)⌋₊ + 1), lemma31NuReal χ n * (n : ℝ)⁻¹) =
      lemma31NuReal χ (⌊(D : ℝ) ^ (21 / 20 : ℝ)⌋₊ + 1) *
        ((⌊(D : ℝ) ^ (21 / 20 : ℝ)⌋₊ + 1 : ℕ) : ℝ)⁻¹ := by
  simp

lemma squareNuTailLinear_integer_endpoint (m : ℕ) :
    ¬ ((m : ℝ) < (m : ℝ)) ∧ ((m : ℝ) < (m + 1 : ℕ)) := by
  constructor
  · exact lt_irrefl _
  · exact_mod_cast Nat.lt_succ_self m

/-- A regression for a genuinely nonintegral lower endpoint. -/
lemma squareNuTailLinear_fractional_endpoint :
    ¬ ((7 / 2 : ℝ) < (3 : ℕ)) ∧ (7 / 2 : ℝ) < (4 : ℕ) ∧
      ⌊(7 / 2 : ℝ)⌋₊ = 3 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  apply (Nat.floor_eq_iff (by norm_num : (0 : ℝ) ≤ 7 / 2)).mpr
  norm_num

/-- Actual strict real-endpoint tail, with the floor conversion proved, for every Z≤P^4. -/
lemma squareNuTailLinear_real_endpoint_le {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 1 ≤ lemma23PaperL D) (hA : NormalizedAssumptionA χ)
    (Z : ℝ) (hZP : Z ≤ lemma23PaperP D ^ 4) :
    (∑ n ∈ (Finset.Icc 1 ⌊Z⌋₊).filter
      (fun n : ℕ => (D : ℝ) ^ (21 / 20 : ℝ) < (n : ℝ)),
      lemma31NuReal χ n * (n : ℝ)⁻¹) ≤
      5 * lemma23PaperL D ^ (-2013 : ℤ) + 36 * (D : ℝ) ^ (-1 / 40 : ℝ) := by
  have hNP : (⌊Z⌋₊ : ℝ) ≤ lemma23PaperP D ^ 4 := by
    by_cases hz : 0 ≤ Z
    · exact (Nat.floor_le hz).trans hZP
    · rw [Nat.floor_of_nonpos (le_of_not_ge hz), Nat.cast_zero]
      positivity
  rw [squareNuTailLinear_filter_eq_Ioc (Real.rpow_nonneg (Nat.cast_nonneg D) _)]
  exact squareNuTailLinear_actual_le χ hD hL hA _ hNP

end ZhangLS.Spec


set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace ZhangLS.Spec
open Finset

noncomputable def squareNuRegressionAF : ArithmeticFunction ℝ :=
  ⟨fun n => if n=1 ∨ n=2 then 1 else 0, by norm_num⟩

lemma squareNu_regression_two_cross_terms :
    (squareNuRegressionAF*squareNuRegressionAF) 2 = 2 := by
  rw [ArithmeticFunction.mul_apply]
  have he : (2:ℕ).divisorsAntidiagonal = {(1,2),(2,1)} := by decide
  rw [he]
  norm_num [squareNuRegressionAF]

lemma squareNu_regression_strict_tail_cross_terms :
    squareNuHarmonicTail (squareNuRegressionAF*squareNuRegressionAF) 1 2 = 1 := by
  have he : (Icc 1 2).filter (fun n : ℕ => (1:ℝ)<n) = {2} := by
    have hh := squareNu_strict_nat_filter 1 2
    norm_num only [one_pow,Nat.cast_one] at hh
    rw [hh]
    decide
  unfold squareNuHarmonicTail
  rw [he,sum_singleton,squareNu_regression_two_cross_terms]
  norm_num

lemma squareNu_regression_strict_endpoint {f : ArithmeticFunction ℝ} (N : ℕ) :
    squareNuHarmonicTail f N N = 0 := by
  have he : (Icc 1 N).filter (fun n : ℕ => (N:ℝ)<n) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro n hn
    have hn' := mem_filter.mp hn
    have hnN := (mem_Icc.mp hn'.1).2
    have hnr : (n:ℝ)≤N := by exact_mod_cast hnN
    exact (not_lt_of_ge hnr) hn'.2
  unfold squareNuHarmonicTail
  rw [he,sum_empty]

lemma squareNu_regression_q9_exponent : ((4*9:ℕ):ℤ)-2015 = -1979 := by norm_num
lemma squareNu_regression_q7_exponent : ((4*7:ℕ):ℤ)-2015 = -1987 := by norm_num
lemma squareNu_regression_q1_exponent : ((4*1:ℕ):ℤ)-2015 = -2011 := by norm_num
lemma squareNu_regression_threshold_margin : (18:ℝ)*(21/20)<19 := by norm_num
lemma squareNu_regression_q10_threshold_failure : (20:ℝ)*(21/20)>19 := by norm_num
lemma squareNu_regression_square_order_zero : squareTau (2*2-2*2) = 1 := by
  norm_num only [Nat.reduceMul,Nat.sub_self]
  exact squareTau_zero_order

/-- At n=4 the entire tail can come from the square factor, so it cannot be dropped. -/
lemma squareNu_regression_square_factor_survives : squareTau 1 4 = 1 := by
  have hh := squareTau_sq 1 2
  norm_num [lemma34Tau] at hh
  exact hh

lemma squareNu_regression_lower_endpoint_excluded (D N : ℕ) :
    D^20 ∉ Ioc (D^20) N := by simp

lemma squareNu_regression_fractional_endpoint_included :
    (2:ℕ) ∈ Ioc (1^20) ⌊(5/2:ℝ)⌋₊ := by
  rw [mem_Ioc,Nat.le_floor_iff (by norm_num : 0≤(5/2:ℝ))]
  norm_num

lemma squareNu_regression_fractional_endpoint_excluded :
    (3:ℕ) ∉ Ioc (1^20) ⌊(5/2:ℝ)⌋₊ := by
  rw [mem_Ioc,Nat.le_floor_iff (by norm_num : 0≤(5/2:ℝ))]
  norm_num

/-- Compiling the full actual endpoint at q=9 checks the largest permitted power. -/
lemma squareNu_regression_actual_q9 :
    ∃ D₀ : ℕ, 2 ≤ D₀ ∧ ∀ D : ℕ, D₀ ≤ D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ → ∀ Z : ℝ, Z ≤ lemma23PaperP D^4 →
      (∑ n ∈ Ioc (D^20) ⌊Z⌋₊, (lemma31NuReal χ n)^2*(lemma34Tau 9 n:ℝ)*(n:ℝ)⁻¹) ≤
        squareNuTailConstant 9 * lemma23PaperL D^(-1979:ℤ) := by
  obtain ⟨D₀,hD₀,hbound⟩ := squareNu_weighted_real_tail_uniform
  refine ⟨D₀,hD₀,?_⟩
  intro D hD χ hA Z hZ
  simpa using hbound D hD χ hA 9 (by norm_num) (by norm_num) Z hZ

end ZhangLS.Spec

set_option maxHeartbeats 24000000
set_option pp.all true
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners : Array Name := #[`ZhangLS.Spec.SquareNuTailLinear, `ZhangLS.Spec.SquareNuTailMajorantDefs, `ZhangLS.Spec.SquareNuTailMajorantLift, `ZhangLS.Spec.SquareNuTailMajorantLocal, `ZhangLS.Spec.SquareNuTailMajorant, `ZhangLS.Spec.SquareNuTailConvolution, `ZhangLS.Spec.SquareNuTailConvolutionSquare, `ZhangLS.Spec.SquareNuTailConvolutionActual, `ZhangLS.Spec.SquareNuTailConvolutionCapstone]
  let expected : Array (Name × Name) := #[(`ZhangLS.Spec.SquareNuTailLinear, `ZhangLS.Spec.squareNuTailLinear_strict_floor), (`ZhangLS.Spec.SquareNuTailLinear, `ZhangLS.Spec.squareNuTailLinear_D_le_floor), (`ZhangLS.Spec.SquareNuTailLinear, `ZhangLS.Spec.squareNuTailLinear_sqrt_ratio), (`ZhangLS.Spec.SquareNuTailLinear, `ZhangLS.Spec.squareNuTailLinear_log_factor), (`ZhangLS.Spec.SquareNuTailLinear, `ZhangLS.Spec.squareNuTailLinear_main_le), (`ZhangLS.Spec.SquareNuTailLinear, `ZhangLS.Spec.squareNuTailLinear_actual_le), (`ZhangLS.Spec.SquareNuTailLinear, `ZhangLS.Spec.squareNuTailLinear_mass_le), (`ZhangLS.Spec.SquareNuTailLinear, `ZhangLS.Spec.squareNuTailLinear_exponential_absorption_threshold), (`ZhangLS.Spec.SquareNuTailLinear, `ZhangLS.Spec.squareNuTailLinear_uniform_inputs), (`ZhangLS.Spec.SquareNuTailMajorantDefs, `ZhangLS.Spec.squareNu), (`ZhangLS.Spec.SquareNuTailMajorantDefs, `ZhangLS.Spec.squareNu_apply), (`ZhangLS.Spec.SquareNuTailMajorantDefs, `ZhangLS.Spec.squareNu_nonneg), (`ZhangLS.Spec.SquareNuTailMajorantDefs, `ZhangLS.Spec.squareNu_multiplicative), (`ZhangLS.Spec.SquareNuTailMajorantDefs, `ZhangLS.Spec.squareLift), (`ZhangLS.Spec.SquareNuTailMajorantDefs, `ZhangLS.Spec.squareLift_apply), (`ZhangLS.Spec.SquareNuTailMajorantDefs, `ZhangLS.Spec.squareLift_sq), (`ZhangLS.Spec.SquareNuTailMajorantDefs, `ZhangLS.Spec.squareLift_nonneg), (`ZhangLS.Spec.SquareNuTailMajorantDefs, `ZhangLS.Spec.squareLift_eq_zero), (`ZhangLS.Spec.SquareNuTailMajorantDefs, `ZhangLS.Spec.square_isSquare_mul_iff), (`ZhangLS.Spec.SquareNuTailMajorantDefs, `ZhangLS.Spec.squareLift_multiplicative), (`ZhangLS.Spec.SquareNuTailMajorantDefs, `ZhangLS.Spec.squareTau), (`ZhangLS.Spec.SquareNuTailMajorantDefs, `ZhangLS.Spec.squareTau_apply), (`ZhangLS.Spec.SquareNuTailMajorantDefs, `ZhangLS.Spec.squareTau_sq), (`ZhangLS.Spec.SquareNuTailMajorantDefs, `ZhangLS.Spec.squareTau_nonneg), (`ZhangLS.Spec.SquareNuTailMajorantDefs, `ZhangLS.Spec.squareTau_eq_zero), (`ZhangLS.Spec.SquareNuTailMajorantDefs, `ZhangLS.Spec.squareTau_multiplicative), (`ZhangLS.Spec.SquareNuTailMajorantDefs, `ZhangLS.Spec.squareLift_one), (`ZhangLS.Spec.SquareNuTailMajorantDefs, `ZhangLS.Spec.squareTau_zero_order), (`ZhangLS.Spec.SquareNuTailMajorantLift, `ZhangLS.Spec.squareLift_ne_zero_isSquare), (`ZhangLS.Spec.SquareNuTailMajorantLift, `ZhangLS.Spec.squareLift_mul), (`ZhangLS.Spec.SquareNuTailMajorantLift, `ZhangLS.Spec.squareLift_pow), (`ZhangLS.Spec.SquareNuTailMajorantLift, `ZhangLS.Spec.squareTau_mul), (`ZhangLS.Spec.SquareNuTailMajorantLift, `ZhangLS.Spec.squareTau_eq_pow), (`ZhangLS.Spec.SquareNuTailMajorantLift, `ZhangLS.Spec.square_prime_mul_apply), (`ZhangLS.Spec.SquareNuTailMajorantLift, `ZhangLS.Spec.square_prime_mul_congr), (`ZhangLS.Spec.SquareNuTailMajorantLift, `ZhangLS.Spec.square_prime_pow_congr), (`ZhangLS.Spec.SquareNuTailMajorantLift, `ZhangLS.Spec.square_prime_isSquare_iff), (`ZhangLS.Spec.SquareNuTailMajorantLift, `ZhangLS.Spec.squareTau_one_prime), (`ZhangLS.Spec.SquareNuTailMajorantLocal, `ZhangLS.Spec.squareDivisor), (`ZhangLS.Spec.SquareNuTailMajorantLocal, `ZhangLS.Spec.squareDivisor_apply), (`ZhangLS.Spec.SquareNuTailMajorantLocal, `ZhangLS.Spec.squareDivisor_pow), (`ZhangLS.Spec.SquareNuTailMajorantLocal, `ZhangLS.Spec.squareDivisor_multiplicative), (`ZhangLS.Spec.SquareNuTailMajorantLocal, `ZhangLS.Spec.square_function_pow_nonneg), (`ZhangLS.Spec.SquareNuTailMajorantLocal, `ZhangLS.Spec.square_function_pow_multiplicative), (`ZhangLS.Spec.SquareNuTailMajorantLocal, `ZhangLS.Spec.square_tau_mono), (`ZhangLS.Spec.SquareNuTailMajorantLocal, `ZhangLS.Spec.squareNu_prime_of_one), (`ZhangLS.Spec.SquareNuTailMajorantLocal, `ZhangLS.Spec.squareNu_prime_of_zero), (`ZhangLS.Spec.SquareNuTailMajorantLocal, `ZhangLS.Spec.squareNu_prime_of_neg_one), (`ZhangLS.Spec.SquareNuTailMajorantLocal, `ZhangLS.Spec.squareNu_pow_prime_of_one), (`ZhangLS.Spec.SquareNuTailMajorantLocal, `ZhangLS.Spec.squareNu_pow_prime_of_zero), (`ZhangLS.Spec.SquareNuTailMajorantLocal, `ZhangLS.Spec.squareNu_pow_prime_of_neg_one), (`ZhangLS.Spec.SquareNuTailMajorantLocal, `ZhangLS.Spec.squareNu_squareTau_prime_of_neg_one), (`ZhangLS.Spec.SquareNuTailMajorantLocal, `ZhangLS.Spec.squareNu_pow_le_mul_squareTau), (`ZhangLS.Spec.SquareNuTailMajorant, `ZhangLS.Spec.squareNu_majorant_prime_split), (`ZhangLS.Spec.SquareNuTailMajorant, `ZhangLS.Spec.squareNu_majorant_prime_ramified), (`ZhangLS.Spec.SquareNuTailMajorant, `ZhangLS.Spec.squareNu_majorant_prime_inert), (`ZhangLS.Spec.SquareNuTailMajorant, `ZhangLS.Spec.squareNu_majorant_prime), (`ZhangLS.Spec.SquareNuTailMajorant, `ZhangLS.Spec.squareNu_majorant_all), (`ZhangLS.Spec.SquareNuTailMajorant, `ZhangLS.Spec.squareNu_majorant), (`ZhangLS.Spec.SquareNuTailConvolution, `ZhangLS.Spec.squareNuHarmonicMass), (`ZhangLS.Spec.SquareNuTailConvolution, `ZhangLS.Spec.squareNuHarmonicTail), (`ZhangLS.Spec.SquareNuTailConvolution, `ZhangLS.Spec.squareNu_convolution_nonneg), (`ZhangLS.Spec.SquareNuTailConvolution, `ZhangLS.Spec.squareNu_pow_nonneg), (`ZhangLS.Spec.SquareNuTailConvolution, `ZhangLS.Spec.squareNu_mass_nonneg), (`ZhangLS.Spec.SquareNuTailConvolution, `ZhangLS.Spec.squareNu_tail_nonneg), (`ZhangLS.Spec.SquareNuTailConvolution, `ZhangLS.Spec.squareNu_convolution_sum_le), (`ZhangLS.Spec.SquareNuTailConvolution, `ZhangLS.Spec.squareNu_mass_mul_le), (`ZhangLS.Spec.SquareNuTailConvolution, `ZhangLS.Spec.squareNu_tail_mul_le), (`ZhangLS.Spec.SquareNuTailConvolution, `ZhangLS.Spec.squareNu_tail_antitone), (`ZhangLS.Spec.SquareNuTailConvolution, `ZhangLS.Spec.squareNu_mass_pow_le), (`ZhangLS.Spec.SquareNuTailConvolution, `ZhangLS.Spec.squareNu_tail_pow_succ_le), (`ZhangLS.Spec.SquareNuTailConvolution, `ZhangLS.Spec.squareNu_tail_pow_le), (`ZhangLS.Spec.SquareNuTailConvolution, `ZhangLS.Spec.squareNu_threshold_power_le), (`ZhangLS.Spec.SquareNuTailConvolution, `ZhangLS.Spec.squareNu_square_assembly_le), (`ZhangLS.Spec.SquareNuTailConvolutionSquare, `ZhangLS.Spec.squareTauMoment_rpow_square), (`ZhangLS.Spec.SquareNuTailConvolutionSquare, `ZhangLS.Spec.squareTauMoment_summable_of_quarter_bound), (`ZhangLS.Spec.SquareNuTailConvolutionSquare, `ZhangLS.Spec.squareTauMoment_summable_of_square_support), (`ZhangLS.Spec.SquareNuTailConvolutionSquare, `ZhangLS.Spec.squareTauMoment_harmonic_le), (`ZhangLS.Spec.SquareNuTailConvolutionSquare, `ZhangLS.Spec.squareTauMoment_tail_le), (`ZhangLS.Spec.SquareNuTailConvolutionSquare, `ZhangLS.Spec.squareTau_moment_summable), (`ZhangLS.Spec.SquareNuTailConvolutionSquare, `ZhangLS.Spec.squareTauMomentConstant), (`ZhangLS.Spec.SquareNuTailConvolutionSquare, `ZhangLS.Spec.squareTauMomentConstant_nonneg), (`ZhangLS.Spec.SquareNuTailConvolutionSquare, `ZhangLS.Spec.squareTau_harmonic_le_moment), (`ZhangLS.Spec.SquareNuTailConvolutionSquare, `ZhangLS.Spec.squareTau_strict_tail_le_moment), (`ZhangLS.Spec.SquareNuTailConvolutionSquare, `ZhangLS.Spec.squareTau_exists_harmonic_tail_constant), (`ZhangLS.Spec.SquareNuTailConvolutionActual, `ZhangLS.Spec.squareNu_actual_tail_eq_floor), (`ZhangLS.Spec.SquareNuTailConvolutionActual, `ZhangLS.Spec.squareNu_actual_convolution_explicit), (`ZhangLS.Spec.SquareNuTailConvolutionActual, `ZhangLS.Spec.squareNu_square_exponential_absorption_threshold), (`ZhangLS.Spec.SquareNuTailConvolutionActual, `ZhangLS.Spec.squareNu_main_scale), (`ZhangLS.Spec.SquareNuTailConvolutionActual, `ZhangLS.Spec.squareNu_square_scale), (`ZhangLS.Spec.SquareNuTailConvolutionActual, `ZhangLS.Spec.squareNuTailConstant), (`ZhangLS.Spec.SquareNuTailConvolutionActual, `ZhangLS.Spec.squareNuTailConstant_nonneg), (`ZhangLS.Spec.SquareNuTailConvolutionActual, `ZhangLS.Spec.squareNu_actual_convolution_uniform), (`ZhangLS.Spec.SquareNuTailConvolutionCapstone, `ZhangLS.Spec.squareNu_strict_nat_filter), (`ZhangLS.Spec.SquareNuTailConvolutionCapstone, `ZhangLS.Spec.squareNu_weighted_tail_le_convolution), (`ZhangLS.Spec.SquareNuTailConvolutionCapstone, `ZhangLS.Spec.squareNu_weighted_tail_uniform), (`ZhangLS.Spec.SquareNuTailConvolutionCapstone, `ZhangLS.Spec.squareNu_weighted_real_tail_uniform), (`ZhangLS.Spec.SquareNuTailConvolutionCapstone, `ZhangLS.Spec.squareNu_real_endpoint_mem), (`ZhangLS.Spec.SquareNuTailConvolutionCapstone, `ZhangLS.Spec.squareNuTailConstant_pos), (`ZhangLS.Spec.SquareNuTailConvolutionCapstone, `ZhangLS.Spec.squareNu_weighted_tail_explicit)]
  for p in expected do
    unless env.contains p.2 do throwError "Missing public {p.2}"
    let some idx := env.getModuleIdxFor? p.2 | throwError "Missing public owner {p.2}"
    unless env.header.moduleNames[idx]! == p.1 do throwError "Public owner mismatch {p.2}"
  let expectedOwned : Array (Name × Name) := #[(`ZhangLS.Spec.SquareNuTailConvolutionActual, `ZhangLS.Spec.squareNu_actual_tail_eq_floor._simp_1_1), (`ZhangLS.Spec.SquareNuTailConvolutionCapstone, `ZhangLS.Spec.squareNu_weighted_tail_uniform), (`ZhangLS.Spec.SquareNuTailConvolutionActual, `ZhangLS.Spec.squareNuTailConstant._proof_2), (`ZhangLS.Spec.SquareNuTailLinear, `ZhangLS.Spec.squareNuTailLinear_sqrt_ratio), (`ZhangLS.Spec.SquareNuTailConvolution, `ZhangLS.Spec.squareNu_convolution_sum_le), (`ZhangLS.Spec.SquareNuTailConvolutionSquare, `ZhangLS.Spec.squareTau_harmonic_le_moment), (`ZhangLS.Spec.SquareNuTailMajorantDefs, `ZhangLS.Spec.squareTau_eq_zero), (`ZhangLS.Spec.SquareNuTailMajorantDefs, `ZhangLS.Spec.squareTau_nonneg), (`ZhangLS.Spec.SquareNuTailMajorantDefs, `ZhangLS.Spec.squareTau_multiplicative), (`ZhangLS.Spec.SquareNuTailMajorantLocal, `ZhangLS.Spec.square_tau_mono), (`ZhangLS.Spec.SquareNuTailConvolution, `ZhangLS.Spec.squareNu_mass_pow_le), (`ZhangLS.Spec.SquareNuTailConvolutionActual, `ZhangLS.Spec.squareNuHarmonicTail.eq_1), (`ZhangLS.Spec.SquareNuTailMajorantDefs, `ZhangLS.Spec.squareTau_sq), (`ZhangLS.Spec.SquareNuTailConvolutionActual, `ZhangLS.Spec.squareNu_actual_tail_eq_floor), (`ZhangLS.Spec.SquareNuTailMajorant, `ZhangLS.Spec.squareNu_majorant_prime_ramified), (`ZhangLS.Spec.SquareNuTailMajorant, `ZhangLS.Spec.squareNu_majorant_prime_inert._proof_1_1), (`ZhangLS.Spec.SquareNuTailMajorantDefs, `ZhangLS.Spec.squareLift_multiplicative), (`ZhangLS.Spec.SquareNuTailConvolution, `ZhangLS.Spec.squareNu_convolution_nonneg), (`ZhangLS.Spec.SquareNuTailConvolution, `ZhangLS.Spec.squareNu_tail_pow_succ_le), (`ZhangLS.Spec.SquareNuTailConvolutionActual, `ZhangLS.Spec.squareNu_actual_convolution_uniform._proof_1_1), (`ZhangLS.Spec.SquareNuTailMajorantLocal, `ZhangLS.Spec.square_function_pow_multiplicative), (`ZhangLS.Spec.SquareNuTailMajorantLift, `ZhangLS.Spec.squareTau_eq_pow), (`ZhangLS.Spec.SquareNuTailConvolutionActual, `ZhangLS.Spec.squareNu_actual_convolution_explicit._proof_1_1), (`ZhangLS.Spec.SquareNuTailLinear, `ZhangLS.Spec.squareNuTailLinear_sqrt_ratio._proof_1_3), (`ZhangLS.Spec.SquareNuTailLinear, `ZhangLS.Spec.squareNuTailLinear_main_le), (`ZhangLS.Spec.SquareNuTailConvolutionActual, `ZhangLS.Spec.squareNu_main_scale), (`ZhangLS.Spec.SquareNuTailMajorantDefs, `ZhangLS.Spec.squareTau), (`ZhangLS.Spec.SquareNuTailMajorantLift, `ZhangLS.Spec.squareLift_pow), (`ZhangLS.Spec.SquareNuTailConvolutionActual, `ZhangLS.Spec.squareNu_actual_tail_eq_floor._simp_1_3), (`ZhangLS.Spec.SquareNuTailConvolution, `ZhangLS.Spec.squareNu_tail_antitone), (`ZhangLS.Spec.SquareNuTailMajorant, `ZhangLS.Spec.squareNu_majorant_prime), (`ZhangLS.Spec.SquareNuTailMajorantDefs, `ZhangLS.Spec.squareLift_apply), (`ZhangLS.Spec.SquareNuTailConvolutionActual, `ZhangLS.Spec.squareNu_actual_convolution_uniform._proof_1_2), (`ZhangLS.Spec.SquareNuTailMajorantLift, `ZhangLS.Spec.squareTau_mul), (`ZhangLS.Spec.SquareNuTailConvolutionCapstone, `ZhangLS.Spec.squareNu_strict_nat_filter), (`ZhangLS.Spec.SquareNuTailConvolution, `ZhangLS.Spec.squareNu_tail_pow_succ_le._proof_1_1), (`ZhangLS.Spec.SquareNuTailMajorantLocal, `ZhangLS.Spec.squareDivisor_pow), (`ZhangLS.Spec.SquareNuTailLinear, `ZhangLS.Spec.squareNuTailLinear_mass_le._proof_1_2), (`ZhangLS.Spec.SquareNuTailMajorantDefs, `ZhangLS.Spec.squareNu_multiplicative), (`ZhangLS.Spec.SquareNuTailConvolutionCapstone, `ZhangLS.Spec.squareNu_strict_nat_filter._simp_1_2), (`ZhangLS.Spec.SquareNuTailMajorant, `ZhangLS.Spec.squareNu_majorant_prime_ramified._proof_1_1), (`ZhangLS.Spec.SquareNuTailLinear, `ZhangLS.Spec.squareNuTailLinear_actual_le._proof_1_1), (`ZhangLS.Spec.SquareNuTailMajorantLocal, `ZhangLS.Spec.squareNu_pow_prime_of_one), (`ZhangLS.Spec.SquareNuTailConvolutionSquare, `ZhangLS.Spec.squareTau_strict_tail_le_moment), (`ZhangLS.Spec.SquareNuTailLinear, `ZhangLS.Spec.squareNuTailLinear_D_le_floor), (`ZhangLS.Spec.SquareNuTailMajorantDefs, `ZhangLS.Spec.squareLift_multiplicative._simp_1_2), (`ZhangLS.Spec.SquareNuTailMajorantDefs, `ZhangLS.Spec.squareLift_multiplicative._simp_1_3), (`ZhangLS.Spec.SquareNuTailMajorantLocal, `ZhangLS.Spec.squareNu_prime_of_neg_one._simp_1_1), (`ZhangLS.Spec.SquareNuTailMajorantDefs, `ZhangLS.Spec.squareLift), (`ZhangLS.Spec.SquareNuTailMajorantLift, `ZhangLS.Spec.squareTau_one_prime), (`ZhangLS.Spec.SquareNuTailLinear, `ZhangLS.Spec.squareNuTailLinear_log_factor), (`ZhangLS.Spec.SquareNuTailConvolutionActual, `ZhangLS.Spec.squareNu_square_scale), (`ZhangLS.Spec.SquareNuTailConvolutionSquare, `ZhangLS.Spec.squareTauMomentConstant._proof_2), (`ZhangLS.Spec.SquareNuTailConvolution, `ZhangLS.Spec.squareNu_tail_mul_le._simp_1_1), (`ZhangLS.Spec.SquareNuTailConvolutionActual, `ZhangLS.Spec.squareNu_actual_convolution_explicit._proof_1_2), (`ZhangLS.Spec.SquareNuTailMajorantLift, `ZhangLS.Spec.squareTau_one_prime._proof_1_1), (`ZhangLS.Spec.SquareNuTailConvolutionCapstone, `ZhangLS.Spec.squareNu_real_endpoint_mem), (`ZhangLS.Spec.SquareNuTailConvolution, `ZhangLS.Spec.squareNuHarmonicTail), (`ZhangLS.Spec.SquareNuTailMajorantLocal, `ZhangLS.Spec.squareNu_pow_prime_of_neg_one), (`ZhangLS.Spec.SquareNuTailMajorantDefs, `ZhangLS.Spec.squareTau_apply), (`ZhangLS.Spec.SquareNuTailConvolutionActual, `ZhangLS.Spec.squareNu_actual_tail_eq_floor._simp_1_2), (`ZhangLS.Spec.SquareNuTailLinear, `ZhangLS.Spec.squareNuTailLinear_mass_le), (`ZhangLS.Spec.SquareNuTailLinear, `ZhangLS.Spec.squareNuTailLinear_actual_le._proof_1_2), (`ZhangLS.Spec.SquareNuTailMajorantLift, `ZhangLS.Spec.squareLift_mul._simp_1_1), (`ZhangLS.Spec.SquareNuTailMajorant, `ZhangLS.Spec.squareNu_majorant_prime_split), (`ZhangLS.Spec.SquareNuTailMajorantDefs, `ZhangLS.Spec.squareLift_eq_zero), (`ZhangLS.Spec.SquareNuTailMajorantDefs, `ZhangLS.Spec.squareNu._proof_1), (`ZhangLS.Spec.SquareNuTailMajorantLocal, `ZhangLS.Spec.squareNu_prime_of_neg_one), (`ZhangLS.Spec.SquareNuTailConvolutionActual, `ZhangLS.Spec.squareNu_actual_convolution_uniform), (`ZhangLS.Spec.SquareNuTailConvolutionActual, `ZhangLS.Spec.squareNuTailConstant), (`ZhangLS.Spec.SquareNuTailMajorantLocal, `ZhangLS.Spec.squareNu_pow_prime_of_zero), (`ZhangLS.Spec.SquareNuTailConvolutionActual, `ZhangLS.Spec.squareNu_main_scale._proof_1_1), (`ZhangLS.Spec.SquareNuTailMajorantLocal, `ZhangLS.Spec.squareDivisor.eq_1), (`ZhangLS.Spec.SquareNuTailConvolutionSquare, `ZhangLS.Spec.squareTauMoment_summable_of_square_support), (`ZhangLS.Spec.SquareNuTailMajorantLocal, `ZhangLS.Spec.squareDivisor_multiplicative), (`ZhangLS.Spec.SquareNuTailLinear, `ZhangLS.Spec.squareNuTailLinear_sqrt_ratio._proof_1_2), (`ZhangLS.Spec.SquareNuTailMajorantLift, `ZhangLS.Spec.square_prime_mul_apply._proof_1_1), (`ZhangLS.Spec.SquareNuTailMajorantLocal, `ZhangLS.Spec.square_tau_mono._proof_1_1), (`ZhangLS.Spec.SquareNuTailMajorant, `ZhangLS.Spec.squareNu_majorant_prime_inert._proof_1_2), (`ZhangLS.Spec.SquareNuTailMajorant, `ZhangLS.Spec.squareNu_majorant_prime_inert), (`ZhangLS.Spec.SquareNuTailConvolutionActual, `ZhangLS.Spec.squareNu_actual_convolution_explicit), (`ZhangLS.Spec.SquareNuTailConvolution, `ZhangLS.Spec.squareNu_square_assembly_le), (`ZhangLS.Spec.SquareNuTailMajorantLift, `ZhangLS.Spec.square_prime_mul_congr), (`ZhangLS.Spec.SquareNuTailConvolutionCapstone, `ZhangLS.Spec.squareNu_weighted_tail_le_convolution), (`ZhangLS.Spec.SquareNuTailMajorantLift, `ZhangLS.Spec.square_prime_isSquare_iff), (`ZhangLS.Spec.SquareNuTailMajorantDefs, `ZhangLS.Spec.squareLift.eq_1), (`ZhangLS.Spec.SquareNuTailMajorant, `ZhangLS.Spec.squareNu_majorant_all), (`ZhangLS.Spec.SquareNuTailMajorantLift, `ZhangLS.Spec.squareLift_mul), (`ZhangLS.Spec.SquareNuTailConvolution, `ZhangLS.Spec.squareNuHarmonicMass), (`ZhangLS.Spec.SquareNuTailConvolution, `ZhangLS.Spec.squareNuHarmonicMass.eq_1), (`ZhangLS.Spec.SquareNuTailMajorantDefs, `ZhangLS.Spec.squareNu.eq_1), (`ZhangLS.Spec.SquareNuTailConvolutionSquare, `ZhangLS.Spec.squareTauMoment_rpow_square), (`ZhangLS.Spec.SquareNuTailLinear, `ZhangLS.Spec.squareNuTailLinear_uniform_inputs), (`ZhangLS.Spec.SquareNuTailMajorantLift, `ZhangLS.Spec.square_prime_isSquare_iff._proof_1_1), (`ZhangLS.Spec.SquareNuTailConvolutionCapstone, `ZhangLS.Spec.squareNu_weighted_real_tail_uniform), (`ZhangLS.Spec.SquareNuTailConvolutionSquare, `ZhangLS.Spec.squareTauMomentConstant), (`ZhangLS.Spec.SquareNuTailMajorantDefs, `ZhangLS.Spec.square_isSquare_mul_iff), (`ZhangLS.Spec.SquareNuTailMajorantDefs, `ZhangLS.Spec.squareNu_nonneg), (`ZhangLS.Spec.SquareNuTailMajorantDefs, `ZhangLS.Spec.squareNu_apply), (`ZhangLS.Spec.SquareNuTailMajorantLift, `ZhangLS.Spec.square_prime_pow_congr), (`ZhangLS.Spec.SquareNuTailMajorant, `ZhangLS.Spec.squareNu_majorant_prime_split._proof_1_1), (`ZhangLS.Spec.SquareNuTailConvolutionSquare, `ZhangLS.Spec.squareTauMoment_summable_of_quarter_bound), (`ZhangLS.Spec.SquareNuTailConvolution, `ZhangLS.Spec.squareNu_mass_mul_le), (`ZhangLS.Spec.SquareNuTailConvolution, `ZhangLS.Spec.squareNu_tail_pow_le), (`ZhangLS.Spec.SquareNuTailConvolutionCapstone, `ZhangLS.Spec.squareNu_strict_nat_filter._simp_1_3), (`ZhangLS.Spec.SquareNuTailMajorantDefs, `ZhangLS.Spec.squareNu), (`ZhangLS.Spec.SquareNuTailConvolutionActual, `ZhangLS.Spec.squareNu_square_exponential_absorption_threshold), (`ZhangLS.Spec.SquareNuTailConvolutionCapstone, `ZhangLS.Spec.squareNuTailConstant_pos), (`ZhangLS.Spec.SquareNuTailConvolutionActual, `ZhangLS.Spec.squareNuTailConstant_nonneg), (`ZhangLS.Spec.SquareNuTailMajorantDefs, `ZhangLS.Spec.squareLift_sq), (`ZhangLS.Spec.SquareNuTailConvolutionCapstone, `ZhangLS.Spec.squareNu_strict_nat_filter._simp_1_1), (`ZhangLS.Spec.SquareNuTailConvolutionActual, `ZhangLS.Spec.squareNu_actual_convolution_uniform._proof_1_3), (`ZhangLS.Spec.SquareNuTailMajorantLocal, `ZhangLS.Spec.squareNu_prime_of_zero), (`ZhangLS.Spec.SquareNuTailMajorantDefs, `ZhangLS.Spec.squareLift_nonneg), (`ZhangLS.Spec.SquareNuTailMajorantDefs, `ZhangLS.Spec.squareLift_one._simp_1_2), (`ZhangLS.Spec.SquareNuTailLinear, `ZhangLS.Spec.squareNuTailLinear_sqrt_ratio._proof_1_1), (`ZhangLS.Spec.SquareNuTailConvolution, `ZhangLS.Spec.squareNu_tail_mul_le), (`ZhangLS.Spec.SquareNuTailConvolutionSquare, `ZhangLS.Spec.squareTau_exists_harmonic_tail_constant), (`ZhangLS.Spec.SquareNuTailMajorantLocal, `ZhangLS.Spec.squareDivisor_apply), (`ZhangLS.Spec.SquareNuTailLinear, `ZhangLS.Spec.squareNuTailLinear_actual_le), (`ZhangLS.Spec.SquareNuTailLinear, `ZhangLS.Spec.squareNuTailLinear_exponential_absorption_threshold), (`ZhangLS.Spec.SquareNuTailConvolution, `ZhangLS.Spec.squareNu_threshold_power_le), (`ZhangLS.Spec.SquareNuTailConvolutionActual, `ZhangLS.Spec.squareNu_actual_tail_eq_floor._proof_1_4), (`ZhangLS.Spec.SquareNuTailConvolution, `ZhangLS.Spec.squareNu_tail_pow_le._proof_1_1), (`ZhangLS.Spec.SquareNuTailConvolutionSquare, `ZhangLS.Spec.squareTauMoment_tail_le), (`ZhangLS.Spec.SquareNuTailLinear, `ZhangLS.Spec.squareNuTailLinear_exponential_absorption_threshold._proof_1_1), (`ZhangLS.Spec.SquareNuTailConvolution, `ZhangLS.Spec.squareNu_tail_nonneg), (`ZhangLS.Spec.SquareNuTailConvolutionSquare, `ZhangLS.Spec.squareTau_moment_summable._proof_1_1), (`ZhangLS.Spec.SquareNuTailMajorantDefs, `ZhangLS.Spec.squareTau_zero_order), (`ZhangLS.Spec.SquareNuTailMajorant, `ZhangLS.Spec.squareNu_majorant), (`ZhangLS.Spec.SquareNuTailConvolutionSquare, `ZhangLS.Spec.squareTauMoment_harmonic_le), (`ZhangLS.Spec.SquareNuTailConvolutionActual, `ZhangLS.Spec.squareNu_actual_convolution_uniform._proof_1_4), (`ZhangLS.Spec.SquareNuTailConvolution, `ZhangLS.Spec.squareNu_mass_nonneg), (`ZhangLS.Spec.SquareNuTailMajorantLift, `ZhangLS.Spec.square_prime_mul_apply), (`ZhangLS.Spec.SquareNuTailMajorantDefs, `ZhangLS.Spec.squareLift_one), (`ZhangLS.Spec.SquareNuTailConvolutionCapstone, `ZhangLS.Spec.squareNu_strict_nat_filter._proof_1_4), (`ZhangLS.Spec.SquareNuTailConvolutionSquare, `ZhangLS.Spec.squareTauMomentConstant_nonneg), (`ZhangLS.Spec.SquareNuTailMajorantDefs, `ZhangLS.Spec.squareLift._proof_1), (`ZhangLS.Spec.SquareNuTailMajorantLocal, `ZhangLS.Spec.squareNu_squareTau_prime_of_neg_one), (`ZhangLS.Spec.SquareNuTailMajorantLift, `ZhangLS.Spec.squareLift_ne_zero_isSquare), (`ZhangLS.Spec.SquareNuTailMajorantLocal, `ZhangLS.Spec.squareDivisor), (`ZhangLS.Spec.SquareNuTailMajorantDefs, `ZhangLS.Spec.squareLift_one._simp_1_1), (`ZhangLS.Spec.SquareNuTailMajorantLocal, `ZhangLS.Spec.square_function_pow_nonneg), (`ZhangLS.Spec.SquareNuTailConvolutionSquare, `ZhangLS.Spec.squareTauMomentConstant._proof_1), (`ZhangLS.Spec.SquareNuTailLinear, `ZhangLS.Spec.squareNuTailLinear_strict_floor), (`ZhangLS.Spec.SquareNuTailConvolutionActual, `ZhangLS.Spec.squareNu_square_exponential_absorption_threshold._proof_1_2), (`ZhangLS.Spec.SquareNuTailConvolutionActual, `ZhangLS.Spec.squareNu_square_exponential_absorption_threshold._proof_1_1), (`ZhangLS.Spec.SquareNuTailConvolutionCapstone, `ZhangLS.Spec.squareNu_weighted_tail_explicit), (`ZhangLS.Spec.SquareNuTailConvolutionActual, `ZhangLS.Spec.squareNuTailConstant._proof_1), (`ZhangLS.Spec.SquareNuTailMajorantLocal, `ZhangLS.Spec.squareNu_pow_le_mul_squareTau), (`ZhangLS.Spec.SquareNuTailLinear, `ZhangLS.Spec.squareNuTailLinear_mass_le._proof_1_1), (`ZhangLS.Spec.SquareNuTailConvolutionSquare, `ZhangLS.Spec.squareTau_moment_summable), (`ZhangLS.Spec.SquareNuTailLinear, `ZhangLS.Spec.squareNuTailLinear_exponential_absorption_threshold._proof_1_2), (`ZhangLS.Spec.SquareNuTailConvolution, `ZhangLS.Spec.squareNu_pow_nonneg), (`ZhangLS.Spec.SquareNuTailMajorantLocal, `ZhangLS.Spec.squareNu_prime_of_one), (`audit.CloudSquareNuTailCentralAudit, `ZhangLS.Spec.squareNu_regression_lower_endpoint_excluded), (`audit.CloudSquareNuTailCentralAudit, `ZhangLS.Spec.squareNu_regression_threshold_margin), (`audit.CloudSquareNuTailCentralAudit, `ZhangLS.Spec.squareNuRegressionAF._proof_1), (`audit.CloudSquareNuTailCentralAudit, `ZhangLS.Spec.squareNuRegressionAF), (`audit.CloudSquareNuTailCentralAudit, `ZhangLS.Spec.squareNu_regression_square_order_zero), (`audit.CloudSquareNuTailCentralAudit, `ZhangLS.Spec.squareNu_regression_two_cross_terms), (`audit.CloudSquareNuTailCentralAudit, `ZhangLS.Spec.squareNuTailLinear_fractional_endpoint), (`audit.CloudSquareNuTailCentralAudit, `ZhangLS.Spec.squareNu_regression_fractional_endpoint_included), (`audit.CloudSquareNuTailCentralAudit, `ZhangLS.Spec.squareNu_regression_strict_tail_cross_terms), (`audit.CloudSquareNuTailCentralAudit, `ZhangLS.Spec.squareNu_regression_square_factor_survives), (`audit.CloudSquareNuTailCentralAudit, `ZhangLS.Spec.squareNuTailLinear_filter_eq_Ioc._simp_1_3), (`audit.CloudSquareNuTailCentralAudit, `ZhangLS.Spec.squareNuTailLinear_integer_endpoint), (`audit.CloudSquareNuTailCentralAudit, `ZhangLS.Spec.squareNu_regression_q10_threshold_failure), (`audit.CloudSquareNuTailCentralAudit, `ZhangLS.Spec.squareNuTailLinear_first_term), (`audit.CloudSquareNuTailCentralAudit, `ZhangLS.Spec.squareNu_regression_strict_endpoint), (`audit.CloudSquareNuTailCentralAudit, `ZhangLS.Spec.squareNuTailLinear_filter_eq_Ioc._simp_1_1), (`audit.CloudSquareNuTailCentralAudit, `ZhangLS.Spec.squareNuTailLinear_endpoint_zero), (`audit.CloudSquareNuTailCentralAudit, `ZhangLS.Spec.squareNuTailLinear_filter_eq_Ioc._proof_1_4), (`audit.CloudSquareNuTailCentralAudit, `ZhangLS.Spec.squareNu_regression_q9_exponent), (`audit.CloudSquareNuTailCentralAudit, `ZhangLS.Spec.squareNuRegressionAF.eq_1), (`audit.CloudSquareNuTailCentralAudit, `ZhangLS.Spec.squareNu_regression_fractional_endpoint_excluded), (`audit.CloudSquareNuTailCentralAudit, `ZhangLS.Spec.squareNuTailLinear_filter_eq_Ioc._simp_1_2), (`audit.CloudSquareNuTailCentralAudit, `ZhangLS.Spec.squareNu_regression_q1_exponent), (`audit.CloudSquareNuTailCentralAudit, `ZhangLS.Spec.squareNuTailLinear_filter_eq_Ioc), (`audit.CloudSquareNuTailCentralAudit, `ZhangLS.Spec.squareNu_regression_q7_exponent), (`audit.CloudSquareNuTailCentralAudit, `ZhangLS.Spec.squareNuTailLinear_real_endpoint_le), (`audit.CloudSquareNuTailCentralAudit, `ZhangLS.Spec.squareNu_regression_actual_q9)]
  let mut seen : Array (Name × Name) := #[]
  let mut proofCount := 0
  let mut testCount := 0
  for (n,ci) in env.constants do
    let owner := match env.getModuleIdxFor? n with
      | some idx => env.header.moduleNames[idx]!
      | none => env.mainModule
    let isProof := owners.contains owner
    let isTest := owner == env.mainModule && n.toString.startsWith "ZhangLS.Spec."
    if isProof || isTest then
      unless expectedOwned.contains (owner,n) do throwError "Unexpected owned declaration {owner} {n}"
      seen := seen.push (owner,n)
      let axs ← collectAxioms n
      unless axs.all (fun a => a == ``propext || a == ``Classical.choice || a == ``Quot.sound) do
        throwError "Nonstandard axiom {n}: {axs}"
      logInfo m!"OWNER {owner} DECL {n} AXIOMS {axs}"
      logInfo m!"OWNED_TYPE {owner} {n} {ci.type}"
      for dep in ci.getUsedConstantsAsSet do logInfo m!"DECL_REF {n} {dep}"
      if isProof then proofCount := proofCount+1 else testCount := testCount+1
  unless proofCount == 155 && testCount == 27 && expected.size == 100 && seen.size == 182 do
    throwError "Exact ownership count drift"
  for p in expectedOwned do
    unless seen.contains p do throwError "Missing owned declaration {p.2}"
  for mod in env.header.moduleNames do logInfo m!"LOADED_MODULE {mod}"
  logInfo m!"OWNERSHIP_PASS PROOF {proofCount} PUBLIC {expected.size} TEST {testCount}"

set_option pp.all true in
#check @ZhangLS.Spec.squareNuTailLinear_strict_floor
set_option pp.all true in
#check @ZhangLS.Spec.squareNuTailLinear_D_le_floor
set_option pp.all true in
#check @ZhangLS.Spec.squareNuTailLinear_sqrt_ratio
set_option pp.all true in
#check @ZhangLS.Spec.squareNuTailLinear_log_factor
set_option pp.all true in
#check @ZhangLS.Spec.squareNuTailLinear_main_le
set_option pp.all true in
#check @ZhangLS.Spec.squareNuTailLinear_actual_le
set_option pp.all true in
#check @ZhangLS.Spec.squareNuTailLinear_mass_le
set_option pp.all true in
#check @ZhangLS.Spec.squareNuTailLinear_exponential_absorption_threshold
set_option pp.all true in
#check @ZhangLS.Spec.squareNuTailLinear_uniform_inputs
set_option pp.all true in
#check @ZhangLS.Spec.squareNu
set_option pp.all true in
#check @ZhangLS.Spec.squareNu_apply
set_option pp.all true in
#check @ZhangLS.Spec.squareNu_nonneg
set_option pp.all true in
#check @ZhangLS.Spec.squareNu_multiplicative
set_option pp.all true in
#check @ZhangLS.Spec.squareLift
set_option pp.all true in
#check @ZhangLS.Spec.squareLift_apply
set_option pp.all true in
#check @ZhangLS.Spec.squareLift_sq
set_option pp.all true in
#check @ZhangLS.Spec.squareLift_nonneg
set_option pp.all true in
#check @ZhangLS.Spec.squareLift_eq_zero
set_option pp.all true in
#check @ZhangLS.Spec.square_isSquare_mul_iff
set_option pp.all true in
#check @ZhangLS.Spec.squareLift_multiplicative
set_option pp.all true in
#check @ZhangLS.Spec.squareTau
set_option pp.all true in
#check @ZhangLS.Spec.squareTau_apply
set_option pp.all true in
#check @ZhangLS.Spec.squareTau_sq
set_option pp.all true in
#check @ZhangLS.Spec.squareTau_nonneg
set_option pp.all true in
#check @ZhangLS.Spec.squareTau_eq_zero
set_option pp.all true in
#check @ZhangLS.Spec.squareTau_multiplicative
set_option pp.all true in
#check @ZhangLS.Spec.squareLift_one
set_option pp.all true in
#check @ZhangLS.Spec.squareTau_zero_order
set_option pp.all true in
#check @ZhangLS.Spec.squareLift_ne_zero_isSquare
set_option pp.all true in
#check @ZhangLS.Spec.squareLift_mul
set_option pp.all true in
#check @ZhangLS.Spec.squareLift_pow
set_option pp.all true in
#check @ZhangLS.Spec.squareTau_mul
set_option pp.all true in
#check @ZhangLS.Spec.squareTau_eq_pow
set_option pp.all true in
#check @ZhangLS.Spec.square_prime_mul_apply
set_option pp.all true in
#check @ZhangLS.Spec.square_prime_mul_congr
set_option pp.all true in
#check @ZhangLS.Spec.square_prime_pow_congr
set_option pp.all true in
#check @ZhangLS.Spec.square_prime_isSquare_iff
set_option pp.all true in
#check @ZhangLS.Spec.squareTau_one_prime
set_option pp.all true in
#check @ZhangLS.Spec.squareDivisor
set_option pp.all true in
#check @ZhangLS.Spec.squareDivisor_apply
set_option pp.all true in
#check @ZhangLS.Spec.squareDivisor_pow
set_option pp.all true in
#check @ZhangLS.Spec.squareDivisor_multiplicative
set_option pp.all true in
#check @ZhangLS.Spec.square_function_pow_nonneg
set_option pp.all true in
#check @ZhangLS.Spec.square_function_pow_multiplicative
set_option pp.all true in
#check @ZhangLS.Spec.square_tau_mono
set_option pp.all true in
#check @ZhangLS.Spec.squareNu_prime_of_one
set_option pp.all true in
#check @ZhangLS.Spec.squareNu_prime_of_zero
set_option pp.all true in
#check @ZhangLS.Spec.squareNu_prime_of_neg_one
set_option pp.all true in
#check @ZhangLS.Spec.squareNu_pow_prime_of_one
set_option pp.all true in
#check @ZhangLS.Spec.squareNu_pow_prime_of_zero
set_option pp.all true in
#check @ZhangLS.Spec.squareNu_pow_prime_of_neg_one
set_option pp.all true in
#check @ZhangLS.Spec.squareNu_squareTau_prime_of_neg_one
set_option pp.all true in
#check @ZhangLS.Spec.squareNu_pow_le_mul_squareTau
set_option pp.all true in
#check @ZhangLS.Spec.squareNu_majorant_prime_split
set_option pp.all true in
#check @ZhangLS.Spec.squareNu_majorant_prime_ramified
set_option pp.all true in
#check @ZhangLS.Spec.squareNu_majorant_prime_inert
set_option pp.all true in
#check @ZhangLS.Spec.squareNu_majorant_prime
set_option pp.all true in
#check @ZhangLS.Spec.squareNu_majorant_all
set_option pp.all true in
#check @ZhangLS.Spec.squareNu_majorant
set_option pp.all true in
#check @ZhangLS.Spec.squareNuHarmonicMass
set_option pp.all true in
#check @ZhangLS.Spec.squareNuHarmonicTail
set_option pp.all true in
#check @ZhangLS.Spec.squareNu_convolution_nonneg
set_option pp.all true in
#check @ZhangLS.Spec.squareNu_pow_nonneg
set_option pp.all true in
#check @ZhangLS.Spec.squareNu_mass_nonneg
set_option pp.all true in
#check @ZhangLS.Spec.squareNu_tail_nonneg
set_option pp.all true in
#check @ZhangLS.Spec.squareNu_convolution_sum_le
set_option pp.all true in
#check @ZhangLS.Spec.squareNu_mass_mul_le
set_option pp.all true in
#check @ZhangLS.Spec.squareNu_tail_mul_le
set_option pp.all true in
#check @ZhangLS.Spec.squareNu_tail_antitone
set_option pp.all true in
#check @ZhangLS.Spec.squareNu_mass_pow_le
set_option pp.all true in
#check @ZhangLS.Spec.squareNu_tail_pow_succ_le
set_option pp.all true in
#check @ZhangLS.Spec.squareNu_tail_pow_le
set_option pp.all true in
#check @ZhangLS.Spec.squareNu_threshold_power_le
set_option pp.all true in
#check @ZhangLS.Spec.squareNu_square_assembly_le
set_option pp.all true in
#check @ZhangLS.Spec.squareTauMoment_rpow_square
set_option pp.all true in
#check @ZhangLS.Spec.squareTauMoment_summable_of_quarter_bound
set_option pp.all true in
#check @ZhangLS.Spec.squareTauMoment_summable_of_square_support
set_option pp.all true in
#check @ZhangLS.Spec.squareTauMoment_harmonic_le
set_option pp.all true in
#check @ZhangLS.Spec.squareTauMoment_tail_le
set_option pp.all true in
#check @ZhangLS.Spec.squareTau_moment_summable
set_option pp.all true in
#check @ZhangLS.Spec.squareTauMomentConstant
set_option pp.all true in
#check @ZhangLS.Spec.squareTauMomentConstant_nonneg
set_option pp.all true in
#check @ZhangLS.Spec.squareTau_harmonic_le_moment
set_option pp.all true in
#check @ZhangLS.Spec.squareTau_strict_tail_le_moment
set_option pp.all true in
#check @ZhangLS.Spec.squareTau_exists_harmonic_tail_constant
set_option pp.all true in
#check @ZhangLS.Spec.squareNu_actual_tail_eq_floor
set_option pp.all true in
#check @ZhangLS.Spec.squareNu_actual_convolution_explicit
set_option pp.all true in
#check @ZhangLS.Spec.squareNu_square_exponential_absorption_threshold
set_option pp.all true in
#check @ZhangLS.Spec.squareNu_main_scale
set_option pp.all true in
#check @ZhangLS.Spec.squareNu_square_scale
set_option pp.all true in
#check @ZhangLS.Spec.squareNuTailConstant
set_option pp.all true in
#check @ZhangLS.Spec.squareNuTailConstant_nonneg
set_option pp.all true in
#check @ZhangLS.Spec.squareNu_actual_convolution_uniform
set_option pp.all true in
#check @ZhangLS.Spec.squareNu_strict_nat_filter
set_option pp.all true in
#check @ZhangLS.Spec.squareNu_weighted_tail_le_convolution
set_option pp.all true in
#check @ZhangLS.Spec.squareNu_weighted_tail_uniform
set_option pp.all true in
#check @ZhangLS.Spec.squareNu_weighted_real_tail_uniform
set_option pp.all true in
#check @ZhangLS.Spec.squareNu_real_endpoint_mem
set_option pp.all true in
#check @ZhangLS.Spec.squareNuTailConstant_pos
set_option pp.all true in
#check @ZhangLS.Spec.squareNu_weighted_tail_explicit
