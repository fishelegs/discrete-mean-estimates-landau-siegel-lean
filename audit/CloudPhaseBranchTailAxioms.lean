import ZhangLS.Spec.ActualPhaseBranchBounds
import ZhangLS.Spec.ActualPhaseKappaTailBounds
set_option autoImplicit false
set_option maxHeartbeats 24000000
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let owners : Array Name := #[`ZhangLS.Spec.ActualPhaseBranchBounds, `ZhangLS.Spec.ActualPhaseKappaTailBounds]
  let expected : Array (Name × Name) := #[(`ZhangLS.Spec.ActualPhaseBranchBounds, `ZhangLS.Spec.actualPhaseShiftPoints), (`ZhangLS.Spec.ActualPhaseBranchBounds, `ZhangLS.Spec.ActualPhaseShiftGeometry), (`ZhangLS.Spec.ActualPhaseBranchBounds, `ZhangLS.Spec.actualPhase_shift_point_real), (`ZhangLS.Spec.ActualPhaseBranchBounds, `ZhangLS.Spec.actualPhase_branch_norm_envelope), (`ZhangLS.Spec.ActualPhaseBranchBounds, `ZhangLS.Spec.actualPhase_source_shift_geometry), (`ZhangLS.Spec.ActualPhaseBranchBounds, `ZhangLS.Spec.actualPhase_source_branch_envelope), (`ZhangLS.Spec.ActualPhaseKappaTailBounds, `ZhangLS.Spec.actualPhaseTauFourThreeHalvesMass), (`ZhangLS.Spec.ActualPhaseKappaTailBounds, `ZhangLS.Spec.actualPhase_tau_four_three_halves_summable), (`ZhangLS.Spec.ActualPhaseKappaTailBounds, `ZhangLS.Spec.actualPhase_tau_four_three_halves_mass_pos), (`ZhangLS.Spec.ActualPhaseKappaTailBounds, `ZhangLS.Spec.actualPhase_imaginary_kappa_tail_term_bound), (`ZhangLS.Spec.ActualPhaseKappaTailBounds, `ZhangLS.Spec.actualPhase_imaginary_kappa_tail_norm_bound), (`ZhangLS.Spec.ActualPhaseKappaTailBounds, `ZhangLS.Spec.actualPhase_kappa_tail_norm_bound), (`ZhangLS.Spec.ActualPhaseKappaTailBounds, `ZhangLS.Spec.actualPhase_dual_kappa_tail_norm_bound)]
  let expectedOwned : Array (Name × Name) := #[(`ZhangLS.Spec.ActualPhaseBranchBounds, `ZhangLS.Spec.actualPhase_shift_point_real), (`ZhangLS.Spec.ActualPhaseBranchBounds, `ZhangLS.Spec.actualPhase_branch_norm_envelope._simp_1_3), (`ZhangLS.Spec.ActualPhaseBranchBounds, `ZhangLS.Spec.ActualPhaseShiftGeometry._proof_1), (`ZhangLS.Spec.ActualPhaseBranchBounds, `ZhangLS.Spec.actualPhase_branch_norm_envelope._simp_1_6), (`ZhangLS.Spec.ActualPhaseBranchBounds, `ZhangLS.Spec.actualPhase_branch_norm_envelope._simp_1_4), (`ZhangLS.Spec.ActualPhaseKappaTailBounds, `ZhangLS.Spec.actualPhase_kappa_tail_norm_bound), (`ZhangLS.Spec.ActualPhaseKappaTailBounds, `ZhangLS.Spec.actualPhaseTauFourThreeHalvesMass._proof_2), (`ZhangLS.Spec.ActualPhaseBranchBounds, `ZhangLS.Spec.actualPhaseShiftPoints), (`ZhangLS.Spec.ActualPhaseKappaTailBounds, `ZhangLS.Spec.actualPhase_dual_kappa_tail_norm_bound), (`ZhangLS.Spec.ActualPhaseBranchBounds, `ZhangLS.Spec.ActualPhaseShiftGeometry), (`ZhangLS.Spec.ActualPhaseBranchBounds, `ZhangLS.Spec.actualPhase_branch_norm_envelope), (`ZhangLS.Spec.ActualPhaseKappaTailBounds, `ZhangLS.Spec.actualPhaseDualKappaTail.eq_1), (`ZhangLS.Spec.ActualPhaseBranchBounds, `ZhangLS.Spec.actualPhase_branch_norm_envelope._simp_1_8), (`ZhangLS.Spec.ActualPhaseBranchBounds, `ZhangLS.Spec.ActualPhaseShiftGeometry._proof_2), (`ZhangLS.Spec.ActualPhaseBranchBounds, `ZhangLS.Spec.actualPhase_source_branch_envelope), (`ZhangLS.Spec.ActualPhaseBranchBounds, `ZhangLS.Spec.actualPhase_branch_norm_envelope._simp_1_7), (`ZhangLS.Spec.ActualPhaseBranchBounds, `ZhangLS.Spec.actualPhase_branch_norm_envelope._simp_1_5), (`ZhangLS.Spec.ActualPhaseBranchBounds, `ZhangLS.Spec.actualPhase_shift_point_real._simp_1_2), (`ZhangLS.Spec.ActualPhaseKappaTailBounds, `ZhangLS.Spec.actualPhase_imaginary_kappa_tail_term_bound), (`ZhangLS.Spec.ActualPhaseKappaTailBounds, `ZhangLS.Spec.actualPhase_imaginary_kappa_tail_norm_bound), (`ZhangLS.Spec.ActualPhaseBranchBounds, `ZhangLS.Spec.actualPhase_source_shift_geometry._simp_1_2), (`ZhangLS.Spec.ActualPhaseKappaTailBounds, `ZhangLS.Spec.actualPhaseTauFourThreeHalvesMass.eq_1), (`ZhangLS.Spec.ActualPhaseBranchBounds, `ZhangLS.Spec.actualPhase_source_shift_geometry), (`ZhangLS.Spec.ActualPhaseKappaTailBounds, `ZhangLS.Spec.actualPhaseTauFourThreeHalvesMass._proof_1), (`ZhangLS.Spec.ActualPhaseBranchBounds, `ZhangLS.Spec.ActualPhaseShiftGeometry._proof_3), (`ZhangLS.Spec.ActualPhaseBranchBounds, `ZhangLS.Spec.actualPhaseShiftPoints.eq_1), (`ZhangLS.Spec.ActualPhaseBranchBounds, `ZhangLS.Spec.actualPhase_branch_norm_envelope._simp_1_2), (`ZhangLS.Spec.ActualPhaseKappaTailBounds, `ZhangLS.Spec.actualPhase_tau_four_three_halves_mass_pos), (`ZhangLS.Spec.ActualPhaseBranchBounds, `ZhangLS.Spec.actualPhase_shift_point_real._simp_1_3), (`ZhangLS.Spec.ActualPhaseKappaTailBounds, `ZhangLS.Spec.actualPhase_tau_four_three_halves_summable), (`ZhangLS.Spec.ActualPhaseKappaTailBounds, `ZhangLS.Spec.actualPhaseTauFourThreeHalvesMass), (`ZhangLS.Spec.ActualPhaseBranchBounds, `ZhangLS.Spec.actualPhase_source_shift_geometry._simp_1_3)]
  let expectedCounts : Array (Name × Nat) := #[(`ZhangLS.Spec.ActualPhaseBranchBounds, 21), (`ZhangLS.Spec.ActualPhaseKappaTailBounds, 11)]
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
  unless seen.size == 32 && expectedOwned.size == 32 && expected.size == 13 do
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
#check @ZhangLS.Spec.actualPhaseShiftPoints
set_option pp.all true in
#check @ZhangLS.Spec.ActualPhaseShiftGeometry
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_shift_point_real
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_branch_norm_envelope
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_source_shift_geometry
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_source_branch_envelope
set_option pp.all true in
#check @ZhangLS.Spec.actualPhaseTauFourThreeHalvesMass
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_tau_four_three_halves_summable
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_tau_four_three_halves_mass_pos
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_imaginary_kappa_tail_term_bound
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_imaginary_kappa_tail_norm_bound
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_kappa_tail_norm_bound
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_dual_kappa_tail_norm_bound
