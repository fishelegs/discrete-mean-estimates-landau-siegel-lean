import ZhangLS.Spec.ActualPhaseSafeSeries
import ZhangLS.Spec.ActualPhaseArchBounds
set_option autoImplicit false
set_option maxHeartbeats 24000000
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let owners : Array Name := #[`ZhangLS.Spec.ActualPhaseArchBounds, `ZhangLS.Spec.ActualPhaseSafeSeries]
  let expected : Array (Name × Name) := #[(`ZhangLS.Spec.ActualPhaseSafeSeries, `ZhangLS.Spec.actualPhaseKappa), (`ZhangLS.Spec.ActualPhaseSafeSeries, `ZhangLS.Spec.actualPhaseStrictIndices), (`ZhangLS.Spec.ActualPhaseSafeSeries, `ZhangLS.Spec.actualPhase_mem_strict_indices), (`ZhangLS.Spec.ActualPhaseSafeSeries, `ZhangLS.Spec.actualPhaseCRightCutoff), (`ZhangLS.Spec.ActualPhaseSafeSeries, `ZhangLS.Spec.actualPhaseLongCutoff), (`ZhangLS.Spec.ActualPhaseSafeSeries, `ZhangLS.Spec.actualPhaseKappaPolynomial), (`ZhangLS.Spec.ActualPhaseSafeSeries, `ZhangLS.Spec.actualPhaseKappaTail), (`ZhangLS.Spec.ActualPhaseSafeSeries, `ZhangLS.Spec.actualPhase_kappa_polynomial_eq_exp_sum), (`ZhangLS.Spec.ActualPhaseSafeSeries, `ZhangLS.Spec.actualPhase_kappa_polynomial_analytic), (`ZhangLS.Spec.ActualPhaseSafeSeries, `ZhangLS.Spec.actualPhase_kappa_series_analytic), (`ZhangLS.Spec.ActualPhaseSafeSeries, `ZhangLS.Spec.actualPhase_actual_kappa_series), (`ZhangLS.Spec.ActualPhaseSafeSeries, `ZhangLS.Spec.actualPhase_actual_kappa_split), (`ZhangLS.Spec.ActualPhaseSafeSeries, `ZhangLS.Spec.actualPhase_kappa_polynomial_units), (`ZhangLS.Spec.ActualPhaseSafeSeries, `ZhangLS.Spec.actualPhase_power_coefficient_conj), (`ZhangLS.Spec.ActualPhaseSafeSeries, `ZhangLS.Spec.actualPhase_kappa_conj), (`ZhangLS.Spec.ActualPhaseSafeSeries, `ZhangLS.Spec.actualPhase_negative_shift_kappa), (`ZhangLS.Spec.ActualPhaseSafeSeries, `ZhangLS.Spec.actualPhase_actual_dual_kappa_series), (`ZhangLS.Spec.ActualPhaseSafeSeries, `ZhangLS.Spec.actualPhaseDualKappaPolynomial), (`ZhangLS.Spec.ActualPhaseSafeSeries, `ZhangLS.Spec.actualPhaseDualKappaTail), (`ZhangLS.Spec.ActualPhaseSafeSeries, `ZhangLS.Spec.actualPhase_actual_dual_kappa_split), (`ZhangLS.Spec.ActualPhaseSafeSeries, `ZhangLS.Spec.actualPhase_dual_kappa_polynomial_units), (`ZhangLS.Spec.ActualPhaseSafeSeries, `ZhangLS.Spec.actualPhase_regression_kappa_endpoint), (`ZhangLS.Spec.ActualPhaseSafeSeries, `ZhangLS.Spec.actualPhase_dual_polynomial_on_critical_line), (`ZhangLS.Spec.ActualPhaseArchBounds, `ZhangLS.Spec.actualPhaseGammaError), (`ZhangLS.Spec.ActualPhaseArchBounds, `ZhangLS.Spec.actualPhase_source_gamma_error_le), (`ZhangLS.Spec.ActualPhaseArchBounds, `ZhangLS.Spec.actualPhase_Z_horizontal_envelope), (`ZhangLS.Spec.ActualPhaseArchBounds, `ZhangLS.Spec.actualPhase_branch_norm_one), (`ZhangLS.Spec.ActualPhaseArchBounds, `ZhangLS.Spec.actualPhase_source_far_rectangle_geometry), (`ZhangLS.Spec.ActualPhaseArchBounds, `ZhangLS.Spec.actualPhase_arch_norm_one)]
  let expectedOwned : Array (Name × Name) := #[(`ZhangLS.Spec.ActualPhaseSafeSeries, `ZhangLS.Spec.actualPhase_power_coefficient_conj), (`ZhangLS.Spec.ActualPhaseSafeSeries, `ZhangLS.Spec.actualPhaseKappa.eq_1), (`ZhangLS.Spec.ActualPhaseSafeSeries, `ZhangLS.Spec.actualPhase_kappa_series_analytic), (`ZhangLS.Spec.ActualPhaseSafeSeries, `ZhangLS.Spec.actualPhaseLongCutoff), (`ZhangLS.Spec.ActualPhaseSafeSeries, `ZhangLS.Spec.actualPhase_negative_shift_kappa), (`ZhangLS.Spec.ActualPhaseSafeSeries, `ZhangLS.Spec.actualPhase_kappa_conj), (`ZhangLS.Spec.ActualPhaseArchBounds, `ZhangLS.Spec.actualPhaseGammaError._proof_3), (`ZhangLS.Spec.ActualPhaseSafeSeries, `ZhangLS.Spec.actualPhaseLongCutoff._proof_2), (`ZhangLS.Spec.ActualPhaseSafeSeries, `ZhangLS.Spec.actualPhaseKappaPolynomial.eq_1), (`ZhangLS.Spec.ActualPhaseArchBounds, `ZhangLS.Spec.actualPhaseGammaError._proof_1), (`ZhangLS.Spec.ActualPhaseArchBounds, `ZhangLS.Spec.actualPhase_branch_norm_one), (`ZhangLS.Spec.ActualPhaseSafeSeries, `ZhangLS.Spec.actualPhaseStrictIndices.eq_1), (`ZhangLS.Spec.ActualPhaseSafeSeries, `ZhangLS.Spec.actualPhase_mem_strict_indices._simp_1_2), (`ZhangLS.Spec.ActualPhaseSafeSeries, `ZhangLS.Spec.actualPhase_dual_polynomial_on_critical_line), (`ZhangLS.Spec.ActualPhaseSafeSeries, `ZhangLS.Spec.actualPhaseCRightCutoff), (`ZhangLS.Spec.ActualPhaseSafeSeries, `ZhangLS.Spec.actualPhase_kappa_polynomial_eq_exp_sum), (`ZhangLS.Spec.ActualPhaseArchBounds, `ZhangLS.Spec.actualPhaseGammaError._proof_2), (`ZhangLS.Spec.ActualPhaseArchBounds, `ZhangLS.Spec.actualPhase_source_gamma_error_le), (`ZhangLS.Spec.ActualPhaseSafeSeries, `ZhangLS.Spec.actualPhase_kappa_polynomial_units), (`ZhangLS.Spec.ActualPhaseSafeSeries, `ZhangLS.Spec.actualPhase_mem_strict_indices._simp_1_3), (`ZhangLS.Spec.ActualPhaseSafeSeries, `ZhangLS.Spec.actualPhaseDualKappaPolynomial.eq_1), (`ZhangLS.Spec.ActualPhaseSafeSeries, `ZhangLS.Spec.actualPhase_actual_kappa_split), (`ZhangLS.Spec.ActualPhaseSafeSeries, `ZhangLS.Spec.actualPhaseKappaTail), (`ZhangLS.Spec.ActualPhaseSafeSeries, `ZhangLS.Spec.actualPhase_regression_kappa_endpoint), (`ZhangLS.Spec.ActualPhaseArchBounds, `ZhangLS.Spec.actualPhase_Z_horizontal_envelope._simp_1_2), (`ZhangLS.Spec.ActualPhaseSafeSeries, `ZhangLS.Spec.actualPhase_mem_strict_indices), (`ZhangLS.Spec.ActualPhaseSafeSeries, `ZhangLS.Spec.actualPhaseCRightCutoff._proof_2), (`ZhangLS.Spec.ActualPhaseSafeSeries, `ZhangLS.Spec.actualPhaseKappaPolynomial), (`ZhangLS.Spec.ActualPhaseArchBounds, `ZhangLS.Spec.actualPhaseGammaError._proof_4), (`ZhangLS.Spec.ActualPhaseArchBounds, `ZhangLS.Spec.actualPhaseGammaError.eq_1), (`ZhangLS.Spec.ActualPhaseSafeSeries, `ZhangLS.Spec.actualPhase_actual_dual_kappa_split), (`ZhangLS.Spec.ActualPhaseSafeSeries, `ZhangLS.Spec.actualPhase_actual_dual_kappa_series), (`ZhangLS.Spec.ActualPhaseArchBounds, `ZhangLS.Spec.actualPhaseGammaError), (`ZhangLS.Spec.ActualPhaseSafeSeries, `ZhangLS.Spec.actualPhaseDualKappaPolynomial), (`ZhangLS.Spec.ActualPhaseSafeSeries, `ZhangLS.Spec.actualPhase_dual_kappa_polynomial_units), (`ZhangLS.Spec.ActualPhaseArchBounds, `ZhangLS.Spec.actualPhase_Z_horizontal_envelope), (`ZhangLS.Spec.ActualPhaseSafeSeries, `ZhangLS.Spec.actualPhaseStrictIndices), (`ZhangLS.Spec.ActualPhaseSafeSeries, `ZhangLS.Spec.actualPhase_kappa_polynomial_analytic), (`ZhangLS.Spec.ActualPhaseSafeSeries, `ZhangLS.Spec.actualPhaseDualKappaTail), (`ZhangLS.Spec.ActualPhaseSafeSeries, `ZhangLS.Spec.actualPhase_actual_kappa_series), (`ZhangLS.Spec.ActualPhaseSafeSeries, `ZhangLS.Spec.actualPhaseLongCutoff._proof_1), (`ZhangLS.Spec.ActualPhaseArchBounds, `ZhangLS.Spec.actualPhase_source_far_rectangle_geometry), (`ZhangLS.Spec.ActualPhaseSafeSeries, `ZhangLS.Spec.actualPhaseCRightCutoff._proof_1), (`ZhangLS.Spec.ActualPhaseSafeSeries, `ZhangLS.Spec.actualPhaseKappa), (`ZhangLS.Spec.ActualPhaseArchBounds, `ZhangLS.Spec.actualPhase_arch_norm_one)]
  let expectedCounts : Array (Name × Nat) := #[(`ZhangLS.Spec.ActualPhaseArchBounds, 12), (`ZhangLS.Spec.ActualPhaseSafeSeries, 33)]
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
  unless seen.size == 45 && expectedOwned.size == 45 && expected.size == 29 do
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
#check @ZhangLS.Spec.actualPhaseKappa
set_option pp.all true in
#check @ZhangLS.Spec.actualPhaseStrictIndices
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_mem_strict_indices
set_option pp.all true in
#check @ZhangLS.Spec.actualPhaseCRightCutoff
set_option pp.all true in
#check @ZhangLS.Spec.actualPhaseLongCutoff
set_option pp.all true in
#check @ZhangLS.Spec.actualPhaseKappaPolynomial
set_option pp.all true in
#check @ZhangLS.Spec.actualPhaseKappaTail
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_kappa_polynomial_eq_exp_sum
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_kappa_polynomial_analytic
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_kappa_series_analytic
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_actual_kappa_series
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_actual_kappa_split
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_kappa_polynomial_units
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_power_coefficient_conj
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_kappa_conj
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_negative_shift_kappa
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_actual_dual_kappa_series
set_option pp.all true in
#check @ZhangLS.Spec.actualPhaseDualKappaPolynomial
set_option pp.all true in
#check @ZhangLS.Spec.actualPhaseDualKappaTail
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_actual_dual_kappa_split
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_dual_kappa_polynomial_units
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_regression_kappa_endpoint
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_dual_polynomial_on_critical_line
set_option pp.all true in
#check @ZhangLS.Spec.actualPhaseGammaError
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_source_gamma_error_le
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_Z_horizontal_envelope
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_branch_norm_one
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_source_far_rectangle_geometry
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_arch_norm_one
