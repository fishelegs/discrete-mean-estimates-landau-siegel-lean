import ZhangLS.Spec.ActualGramPiCollapse
import ZhangLS.Spec.ActualGramArithmeticAttachment
import ZhangLS.Spec.ActualGramRamp
import ZhangLS.Spec.ActualGramClosedWeightLayer
import ZhangLS.Spec.ActualGramFiniteSuperposition
import ZhangLS.Spec.ActualGramLogKernelBridge
import ZhangLS.Spec.ActualGramOriginalScaling
import ZhangLS.Spec.ActualGramOneSidedSuperposition
import ZhangLS.Spec.ActualGramMainKernelBridge
import ZhangLS.Spec.ActualGramSmoothingBounds
set_option autoImplicit false
set_option maxHeartbeats 24000000
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let owners : Array Name := #[`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.ActualGramClosedWeightLayer, `ZhangLS.Spec.ActualGramFiniteSuperposition, `ZhangLS.Spec.ActualGramLogKernelBridge, `ZhangLS.Spec.ActualGramMainKernelBridge, `ZhangLS.Spec.ActualGramOneSidedSuperposition, `ZhangLS.Spec.ActualGramOriginalScaling, `ZhangLS.Spec.ActualGramPiCollapse, `ZhangLS.Spec.ActualGramRamp, `ZhangLS.Spec.ActualGramSmoothingBounds]
  let expected : Array (Name × Name) := #[(`ZhangLS.Spec.ActualGramPiCollapse, `ZhangLS.Spec.actualGram_totient_prime_product), (`ZhangLS.Spec.ActualGramPiCollapse, `ZhangLS.Spec.actualGram_squarefree_divisor_expansion), (`ZhangLS.Spec.ActualGramPiCollapse, `ZhangLS.Spec.actualGram_character_prime_denominator), (`ZhangLS.Spec.ActualGramPiCollapse, `ZhangLS.Spec.actualGram_local_pi_collapse), (`ZhangLS.Spec.ActualGramPiCollapse, `ZhangLS.Spec.actualGram_totient_ratio_product), (`ZhangLS.Spec.ActualGramPiCollapse, `ZhangLS.Spec.actualGram_pi_divisor_collapse), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGram_character_mul), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGram_character_square), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGramProfileSequence), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGram_profile_conjugate), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGramFirst), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGramSecond), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGram_P7_profile_factorization), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGram_weight_pi_collapse), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGram_finite_main_attachment), (`ZhangLS.Spec.ActualGramRamp, `ZhangLS.Spec.actualGramRampDensity), (`ZhangLS.Spec.ActualGramRamp, `ZhangLS.Spec.actualGram_ramp_antiderivative), (`ZhangLS.Spec.ActualGramRamp, `ZhangLS.Spec.actualGram_ramp_identity), (`ZhangLS.Spec.ActualGramRamp, `ZhangLS.Spec.actualGram_exponential_antiderivative), (`ZhangLS.Spec.ActualGramRamp, `ZhangLS.Spec.actualGram_exponential_identity), (`ZhangLS.Spec.ActualGramRamp, `ZhangLS.Spec.actualGram_first_main_identity), (`ZhangLS.Spec.ActualGramRamp, `ZhangLS.Spec.actualGram_density_integral), (`ZhangLS.Spec.ActualGramRamp, `ZhangLS.Spec.actualGram_second_main_identity), (`ZhangLS.Spec.ActualGramClosedWeightLayer, `ZhangLS.Spec.actualGram_weight_product_endpoint), (`ZhangLS.Spec.ActualGramClosedWeightLayer, `ZhangLS.Spec.actualGram_actual_weight_closed_layer), (`ZhangLS.Spec.ActualGramFiniteSuperposition, `ZhangLS.Spec.actualGramClippedRamp), (`ZhangLS.Spec.ActualGramFiniteSuperposition, `ZhangLS.Spec.actualGram_clipped_ramp_of_le), (`ZhangLS.Spec.ActualGramFiniteSuperposition, `ZhangLS.Spec.actualGram_clipped_ramp_of_ge), (`ZhangLS.Spec.ActualGramFiniteSuperposition, `ZhangLS.Spec.actualGram_clipped_ramp_continuous), (`ZhangLS.Spec.ActualGramFiniteSuperposition, `ZhangLS.Spec.actualGram_ramp_density_continuous), (`ZhangLS.Spec.ActualGramFiniteSuperposition, `ZhangLS.Spec.actualGram_fixed_interval_ramp), (`ZhangLS.Spec.ActualGramFiniteSuperposition, `ZhangLS.Spec.actualGram_finite_ramp_superposition), (`ZhangLS.Spec.ActualGramLogKernelBridge, `ZhangLS.Spec.actualGramLogSmoothedSum), (`ZhangLS.Spec.ActualGramLogKernelBridge, `ZhangLS.Spec.actualGram_log_smoothing_term), (`ZhangLS.Spec.ActualGramLogKernelBridge, `ZhangLS.Spec.actualGram_smoothing_cutoff_inside_original), (`ZhangLS.Spec.ActualGramLogKernelBridge, `ZhangLS.Spec.actualGram_clipped_sum_eq_smoothed), (`ZhangLS.Spec.ActualGramLogKernelBridge, `ZhangLS.Spec.actualGram_log_smoothed_superposition), (`ZhangLS.Spec.ActualGramLogKernelBridge, `ZhangLS.Spec.actualGram_log_kernel_first), (`ZhangLS.Spec.ActualGramLogKernelBridge, `ZhangLS.Spec.actualGram_log_kernel_second), (`ZhangLS.Spec.ActualGramLogKernelBridge, `ZhangLS.Spec.actualGram_first_smoothed_superposition), (`ZhangLS.Spec.ActualGramLogKernelBridge, `ZhangLS.Spec.actualGram_second_smoothed_superposition), (`ZhangLS.Spec.ActualGramOriginalScaling, `ZhangLS.Spec.actualGram_original_log_scale), (`ZhangLS.Spec.ActualGramOriginalScaling, `ZhangLS.Spec.actualGram_original_log_scale_pos), (`ZhangLS.Spec.ActualGramOriginalScaling, `ZhangLS.Spec.actualGram_original_mu6_scaled), (`ZhangLS.Spec.ActualGramOriginalScaling, `ZhangLS.Spec.actualGram_original_mu6_negative_scaled), (`ZhangLS.Spec.ActualGramOriginalScaling, `ZhangLS.Spec.actualGram_original_exp_power), (`ZhangLS.Spec.ActualGramOriginalScaling, `ZhangLS.Spec.actualGram_log_moving_band), (`ZhangLS.Spec.ActualGramOriginalScaling, `ZhangLS.Spec.actualGram_original_moving_T_band), (`ZhangLS.Spec.ActualGramOneSidedSuperposition, `ZhangLS.Spec.actualGram_ramp_above_left_endpoint), (`ZhangLS.Spec.ActualGramOneSidedSuperposition, `ZhangLS.Spec.actualGram_log_superposition_from_product), (`ZhangLS.Spec.ActualGramMainKernelBridge, `ZhangLS.Spec.actualGram_log_ratio_scale), (`ZhangLS.Spec.ActualGramMainKernelBridge, `ZhangLS.Spec.actualGram_positive_cutoff_cpow), (`ZhangLS.Spec.ActualGramMainKernelBridge, `ZhangLS.Spec.actualGram_first_main_kernel), (`ZhangLS.Spec.ActualGramMainKernelBridge, `ZhangLS.Spec.actualGram_mu6_nonzero), (`ZhangLS.Spec.ActualGramMainKernelBridge, `ZhangLS.Spec.actualGram_second_main_kernel), (`ZhangLS.Spec.ActualGramMainKernelBridge, `ZhangLS.Spec.actualGram_first_main_superposition), (`ZhangLS.Spec.ActualGramMainKernelBridge, `ZhangLS.Spec.actualGram_second_main_superposition), (`ZhangLS.Spec.ActualGramMainKernelBridge, `ZhangLS.Spec.actualGram_volterra_terminal_extension), (`ZhangLS.Spec.ActualGramSmoothingBounds, `ZhangLS.Spec.actualGramFirstBoundaryBudget), (`ZhangLS.Spec.ActualGramSmoothingBounds, `ZhangLS.Spec.actualGramSecondBoundaryBudget), (`ZhangLS.Spec.ActualGramSmoothingBounds, `ZhangLS.Spec.actualGram_first_small_error), (`ZhangLS.Spec.ActualGramSmoothingBounds, `ZhangLS.Spec.actualGram_second_small_error), (`ZhangLS.Spec.ActualGramSmoothingBounds, `ZhangLS.Spec.actualGram_smoothing_errors_uniform)]
  let expectedOwned : Array (Name × Name) := #[(`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGramFirst.eq_1), (`ZhangLS.Spec.ActualGramClosedWeightLayer, `ZhangLS.Spec.actualGram_weight_product_endpoint), (`ZhangLS.Spec.ActualGramPiCollapse, `ZhangLS.Spec.actualGram_character_prime_denominator), (`ZhangLS.Spec.ActualGramClosedWeightLayer, `ZhangLS.Spec.actualGram_actual_weight_closed_layer), (`ZhangLS.Spec.ActualGramSmoothingBounds, `ZhangLS.Spec.actualGramFirstBoundaryBudget._proof_2), (`ZhangLS.Spec.ActualGramMainKernelBridge, `ZhangLS.Spec.actualGram_second_main_kernel), (`ZhangLS.Spec.ActualGramMainKernelBridge, `ZhangLS.Spec.actualGram_positive_cutoff_cpow), (`ZhangLS.Spec.ActualGramLogKernelBridge, `ZhangLS.Spec.actualGram_second_smoothed_superposition), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGramSecond), (`ZhangLS.Spec.ActualGramFiniteSuperposition, `ZhangLS.Spec.actualGram_clipped_ramp_of_le), (`ZhangLS.Spec.ActualGramRamp, `ZhangLS.Spec.actualGram_ramp_identity), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGram_P7_profile_factorization), (`ZhangLS.Spec.ActualGramSmoothingBounds, `ZhangLS.Spec.actualGramSecondBoundaryBudget), (`ZhangLS.Spec.ActualGramPiCollapse, `ZhangLS.Spec.actualGram_squarefree_divisor_expansion._simp_1_2), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGram_weight_pi_collapse._simp_1_5), (`ZhangLS.Spec.ActualGramOriginalScaling, `ZhangLS.Spec.actualGram_original_mu6_scaled), (`ZhangLS.Spec.ActualGramMainKernelBridge, `ZhangLS.Spec.actualGram_log_ratio_scale._simp_1_2), (`ZhangLS.Spec.ActualGramOriginalScaling, `ZhangLS.Spec.actualGram_original_log_scale), (`ZhangLS.Spec.ActualGramOriginalScaling, `ZhangLS.Spec.actualGram_original_mu6_negative_scaled), (`ZhangLS.Spec.ActualGramMainKernelBridge, `ZhangLS.Spec.actualGram_log_ratio_scale._simp_1_7), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGram_profile_conjugate), (`ZhangLS.Spec.ActualGramLogKernelBridge, `ZhangLS.Spec.actualGram_log_smoothing_term._simp_1_4), (`ZhangLS.Spec.ActualGramFiniteSuperposition, `ZhangLS.Spec.actualGram_fixed_interval_ramp), (`ZhangLS.Spec.ActualGramFiniteSuperposition, `ZhangLS.Spec.actualGramClippedRamp), (`ZhangLS.Spec.ActualGramRamp, `ZhangLS.Spec.actualGram_ramp_antiderivative), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGramProfileSequence), (`ZhangLS.Spec.ActualGramOriginalScaling, `ZhangLS.Spec.actualGram_original_mu6_scaled._simp_1_6), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGramSecond.eq_1), (`ZhangLS.Spec.ActualGramSmoothingBounds, `ZhangLS.Spec.actualGramSecondBoundaryBudget._proof_3), (`ZhangLS.Spec.ActualGramPiCollapse, `ZhangLS.Spec.lemma83Pi.eq_1), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGram_weight_pi_collapse), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGram_finite_main_attachment), (`ZhangLS.Spec.ActualGramPiCollapse, `ZhangLS.Spec.actualGram_totient_ratio_product), (`ZhangLS.Spec.ActualGramOriginalScaling, `ZhangLS.Spec.actualGram_original_log_scale_pos), (`ZhangLS.Spec.ActualGramSmoothingBounds, `ZhangLS.Spec.actualGram_second_small_error), (`ZhangLS.Spec.ActualGramRamp, `ZhangLS.Spec.actualGram_exponential_identity), (`ZhangLS.Spec.ActualGramMainKernelBridge, `ZhangLS.Spec.actualGram_mu6_nonzero), (`ZhangLS.Spec.ActualGramPiCollapse, `ZhangLS.Spec.actualGram_pi_divisor_collapse), (`ZhangLS.Spec.ActualGramLogKernelBridge, `ZhangLS.Spec.actualGram_log_smoothing_term._simp_1_2), (`ZhangLS.Spec.ActualGramRamp, `ZhangLS.Spec.actualGram_density_integral), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGram_weight_pi_collapse._simp_1_7), (`ZhangLS.Spec.ActualGramPiCollapse, `ZhangLS.Spec.actualGram_squarefree_divisor_expansion._simp_1_1), (`ZhangLS.Spec.ActualGramMainKernelBridge, `ZhangLS.Spec.actualGram_log_ratio_scale._simp_1_3), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGram_weight_pi_collapse._simp_1_6), (`ZhangLS.Spec.ActualGramSmoothingBounds, `ZhangLS.Spec.actualGramFirstBoundaryBudget._proof_1), (`ZhangLS.Spec.ActualGramMainKernelBridge, `ZhangLS.Spec.actualGram_first_main_superposition), (`ZhangLS.Spec.ActualGramRamp, `ZhangLS.Spec.actualGram_exponential_antiderivative), (`ZhangLS.Spec.ActualGramOriginalScaling, `ZhangLS.Spec.actualGram_log_moving_band), (`ZhangLS.Spec.ActualGramPiCollapse, `ZhangLS.Spec.actualGram_local_pi_collapse), (`ZhangLS.Spec.ActualGramOriginalScaling, `ZhangLS.Spec.actualGram_original_moving_T_band), (`ZhangLS.Spec.ActualGramRamp, `ZhangLS.Spec.actualGramRampDensity.eq_1), (`ZhangLS.Spec.ActualGramFiniteSuperposition, `ZhangLS.Spec.actualGram_clipped_ramp_continuous), (`ZhangLS.Spec.ActualGramMainKernelBridge, `ZhangLS.Spec.actualGram_first_main_kernel), (`ZhangLS.Spec.ActualGramPiCollapse, `ZhangLS.Spec.actualGram_totient_prime_product), (`ZhangLS.Spec.ActualGramMainKernelBridge, `ZhangLS.Spec.actualGram_log_ratio_scale._simp_1_6), (`ZhangLS.Spec.ActualGramLogKernelBridge, `ZhangLS.Spec.actualGram_log_kernel_second), (`ZhangLS.Spec.ActualGramOriginalScaling, `ZhangLS.Spec.actualGram_original_mu6_scaled._simp_1_3), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGram_weight_pi_collapse._simp_1_8), (`ZhangLS.Spec.ActualGramSmoothingBounds, `ZhangLS.Spec.actualGramSecondBoundaryBudget._proof_2), (`ZhangLS.Spec.ActualGramMainKernelBridge, `ZhangLS.Spec.actualGram_log_ratio_scale._simp_1_1), (`ZhangLS.Spec.ActualGramSmoothingBounds, `ZhangLS.Spec.actualGramSecondBoundaryBudget._proof_1), (`ZhangLS.Spec.ActualGramOneSidedSuperposition, `ZhangLS.Spec.actualGram_log_superposition_from_product), (`ZhangLS.Spec.ActualGramFiniteSuperposition, `ZhangLS.Spec.actualGram_finite_ramp_superposition), (`ZhangLS.Spec.ActualGramRamp, `ZhangLS.Spec.actualGramRampDensity), (`ZhangLS.Spec.ActualGramSmoothingBounds, `ZhangLS.Spec.actualGram_first_small_error), (`ZhangLS.Spec.ActualGramRamp, `ZhangLS.Spec.actualGramRampDensity._proof_1), (`ZhangLS.Spec.ActualGramLogKernelBridge, `ZhangLS.Spec.actualGram_first_smoothed_superposition), (`ZhangLS.Spec.ActualGramLogKernelBridge, `ZhangLS.Spec.actualGram_log_smoothing_term._simp_1_6), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGram_character_mul), (`ZhangLS.Spec.ActualGramLogKernelBridge, `ZhangLS.Spec.actualGram_clipped_sum_eq_smoothed), (`ZhangLS.Spec.ActualGramMainKernelBridge, `ZhangLS.Spec.actualGram_log_ratio_scale), (`ZhangLS.Spec.ActualGramOriginalScaling, `ZhangLS.Spec.actualGram_original_mu6_scaled._simp_1_7), (`ZhangLS.Spec.ActualGramOriginalScaling, `ZhangLS.Spec.actualGram_original_mu6_scaled._simp_1_4), (`ZhangLS.Spec.ActualGramSmoothingBounds, `ZhangLS.Spec.actualGram_smoothing_errors_uniform), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGram_weight_pi_collapse._simp_1_1), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGram_character_square), (`ZhangLS.Spec.ActualGramMainKernelBridge, `ZhangLS.Spec.actualGram_log_ratio_scale._simp_1_4), (`ZhangLS.Spec.ActualGramMainKernelBridge, `ZhangLS.Spec.actualGram_log_ratio_scale._simp_1_5), (`ZhangLS.Spec.ActualGramOriginalScaling, `ZhangLS.Spec.lemma82SmoothingBeta.eq_1), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGramFirst), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGram_P7_profile_factorization._simp_1_4), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGram_weight_pi_collapse._simp_1_3), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGram_weight_pi_collapse._simp_1_4), (`ZhangLS.Spec.ActualGramMainKernelBridge, `ZhangLS.Spec.actualGram_volterra_terminal_extension), (`ZhangLS.Spec.ActualGramSmoothingBounds, `ZhangLS.Spec.actualGramFirstBoundaryBudget), (`ZhangLS.Spec.ActualGramOriginalScaling, `ZhangLS.Spec.actualGram_original_mu6_scaled._simp_1_8), (`ZhangLS.Spec.ActualGramMainKernelBridge, `ZhangLS.Spec.actualGram_second_main_superposition), (`ZhangLS.Spec.ActualGramFiniteSuperposition, `ZhangLS.Spec.actualGramClippedRamp.eq_1), (`ZhangLS.Spec.ActualGramOriginalScaling, `ZhangLS.Spec.actualGram_original_mu6_scaled._simp_1_2), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGram_weight_pi_collapse._simp_1_2), (`ZhangLS.Spec.ActualGramLogKernelBridge, `ZhangLS.Spec.actualGramLogSmoothedSum), (`ZhangLS.Spec.ActualGramOneSidedSuperposition, `ZhangLS.Spec.actualGram_ramp_above_left_endpoint), (`ZhangLS.Spec.ActualGramLogKernelBridge, `ZhangLS.Spec.actualGram_log_smoothing_term._simp_1_3), (`ZhangLS.Spec.ActualGramOriginalScaling, `ZhangLS.Spec.actualGram_original_exp_power), (`ZhangLS.Spec.ActualGramFiniteSuperposition, `ZhangLS.Spec.actualGram_clipped_ramp_of_ge), (`ZhangLS.Spec.ActualGramLogKernelBridge, `ZhangLS.Spec.actualGram_smoothing_cutoff_inside_original), (`ZhangLS.Spec.ActualGramLogKernelBridge, `ZhangLS.Spec.actualGram_clipped_sum_eq_smoothed._simp_1_1), (`ZhangLS.Spec.ActualGramOriginalScaling, `ZhangLS.Spec.actualGram_original_mu6_scaled._simp_1_5), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGramProfileSequence.eq_1), (`ZhangLS.Spec.ActualGramLogKernelBridge, `ZhangLS.Spec.actualGram_log_smoothing_term._simp_1_1), (`ZhangLS.Spec.ActualGramLogKernelBridge, `ZhangLS.Spec.actualGram_log_smoothing_term), (`ZhangLS.Spec.ActualGramRamp, `ZhangLS.Spec.actualGram_second_main_identity), (`ZhangLS.Spec.ActualGramSmoothingBounds, `ZhangLS.Spec.actualGram_smoothing_errors_uniform._proof_1_1), (`ZhangLS.Spec.ActualGramLogKernelBridge, `ZhangLS.Spec.actualGram_log_kernel_first), (`ZhangLS.Spec.ActualGramLogKernelBridge, `ZhangLS.Spec.actualGram_log_smoothed_superposition), (`ZhangLS.Spec.ActualGramLogKernelBridge, `ZhangLS.Spec.actualGram_log_smoothing_term._simp_1_7), (`ZhangLS.Spec.ActualGramPiCollapse, `ZhangLS.Spec.actualGram_squarefree_divisor_expansion), (`ZhangLS.Spec.ActualGramLogKernelBridge, `ZhangLS.Spec.actualGram_log_smoothing_term._simp_1_5), (`ZhangLS.Spec.ActualGramRamp, `ZhangLS.Spec.actualGram_first_main_identity), (`ZhangLS.Spec.ActualGramFiniteSuperposition, `ZhangLS.Spec.actualGram_ramp_density_continuous)]
  let expectedCounts : Array (Name × Nat) := #[(`ZhangLS.Spec.ActualGramArithmeticAttachment, 21), (`ZhangLS.Spec.ActualGramClosedWeightLayer, 2), (`ZhangLS.Spec.ActualGramFiniteSuperposition, 8), (`ZhangLS.Spec.ActualGramLogKernelBridge, 17), (`ZhangLS.Spec.ActualGramMainKernelBridge, 15), (`ZhangLS.Spec.ActualGramOneSidedSuperposition, 2), (`ZhangLS.Spec.ActualGramOriginalScaling, 15), (`ZhangLS.Spec.ActualGramPiCollapse, 9), (`ZhangLS.Spec.ActualGramRamp, 10), (`ZhangLS.Spec.ActualGramSmoothingBounds, 11)]
  for pair in expected do
    unless env.contains pair.2 do
      throwError "Missing public declaration {pair.2}"
    let some idx := env.getModuleIdxFor? pair.2 | throwError "Missing public owner {pair.2}"
    unless moduleNames[idx]! == pair.1 do
      throwError "Public owner mismatch {pair.2}"
  let mut seen : Array (Name × Name) := #[]
  for (name, ci) in env.constants do
    if let some idx := env.getModuleIdxFor? name then
      let owner := moduleNames[idx]!
      if owners.contains owner then
        unless expectedOwned.contains (owner,name) do
          throwError "Unexpected owned declaration {owner} {name}"
        if seen.contains (owner,name) then
          throwError "Duplicate owned declaration {name}"
        let axs ← collectAxioms name
        unless axs.all (fun a => a == ``propext || a == ``Classical.choice || a == ``Quot.sound) do
          throwError "Nonstandard axiom at {name}: {axs}"
        logInfo m!"OWNER {owner} DECL {name} AXIOMS {axs}"
        for dep in ci.getUsedConstantsAsSet do
          logInfo m!"DECL_REF {name} {dep}"
        seen := seen.push (owner,name)
  unless seen.size == 110 && expectedOwned.size == 110 && expected.size == 63 do
    throwError "Exact ownership/public count drift {seen.size}"
  for pair in expectedOwned do
    unless seen.contains pair do
      throwError "Missing owned declaration {pair.2}"
  for owner in owners do
    let count := (seen.filter (fun p => p.1 == owner)).size
    unless count > 0 && expectedCounts.contains (owner,count) do
      throwError "Owner count mismatch {owner} {count}"
    logInfo m!"OWNER_COUNT {owner} {count}"
  for mod in moduleNames do
    logInfo m!"LOADED_MODULE {mod}"
  logInfo m!"OWNERSHIP_PASS {seen.size} PUBLIC {expected.size}"
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_totient_prime_product
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_squarefree_divisor_expansion
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_character_prime_denominator
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_local_pi_collapse
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_totient_ratio_product
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_pi_divisor_collapse
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_character_mul
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_character_square
set_option pp.all true in
#check @ZhangLS.Spec.actualGramProfileSequence
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_profile_conjugate
set_option pp.all true in
#check @ZhangLS.Spec.actualGramFirst
set_option pp.all true in
#check @ZhangLS.Spec.actualGramSecond
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_P7_profile_factorization
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_weight_pi_collapse
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_finite_main_attachment
set_option pp.all true in
#check @ZhangLS.Spec.actualGramRampDensity
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_ramp_antiderivative
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_ramp_identity
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_exponential_antiderivative
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_exponential_identity
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_first_main_identity
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_density_integral
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_second_main_identity
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_weight_product_endpoint
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_actual_weight_closed_layer
set_option pp.all true in
#check @ZhangLS.Spec.actualGramClippedRamp
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_clipped_ramp_of_le
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_clipped_ramp_of_ge
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_clipped_ramp_continuous
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_ramp_density_continuous
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_fixed_interval_ramp
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_finite_ramp_superposition
set_option pp.all true in
#check @ZhangLS.Spec.actualGramLogSmoothedSum
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_log_smoothing_term
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_smoothing_cutoff_inside_original
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_clipped_sum_eq_smoothed
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_log_smoothed_superposition
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_log_kernel_first
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_log_kernel_second
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_first_smoothed_superposition
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_second_smoothed_superposition
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_original_log_scale
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_original_log_scale_pos
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_original_mu6_scaled
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_original_mu6_negative_scaled
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_original_exp_power
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_log_moving_band
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_original_moving_T_band
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_ramp_above_left_endpoint
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_log_superposition_from_product
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_log_ratio_scale
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_positive_cutoff_cpow
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_first_main_kernel
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_mu6_nonzero
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_second_main_kernel
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_first_main_superposition
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_second_main_superposition
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_volterra_terminal_extension
set_option pp.all true in
#check @ZhangLS.Spec.actualGramFirstBoundaryBudget
set_option pp.all true in
#check @ZhangLS.Spec.actualGramSecondBoundaryBudget
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_first_small_error
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_second_small_error
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_smoothing_errors_uniform
