import ZhangLS.Spec.FiniteMobius
set_option maxHeartbeats 10000000
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `ZhangLS.Spec.FiniteMobius
  let expected : Array Name := #[`ZhangLS.Spec.FiniteMobius.truncated, `ZhangLS.Spec.FiniteMobius.truncated_apply, `ZhangLS.Spec.FiniteMobius.truncated_apply_of_le, `ZhangLS.Spec.FiniteMobius.truncated_apply_of_lt, `ZhangLS.Spec.FiniteMobius.truncated_intCast, `ZhangLS.Spec.FiniteMobius.defect, `ZhangLS.Spec.FiniteMobius.truncated_mul_zeta_eq_one, `ZhangLS.Spec.FiniteMobius.defect_eq_zero, `ZhangLS.Spec.FiniteMobius.mul_eq_zero_of_le, `ZhangLS.Spec.FiniteMobius.pow_eq_zero_of_le, `ZhangLS.Spec.FiniteMobius.mul_eq_zero_of_right, `ZhangLS.Spec.FiniteMobius.defect_pow_eq_zero, `ZhangLS.Spec.FiniteMobius.moebius_mul_defect_pow_eq_zero, `ZhangLS.Spec.FiniteMobius.binomial_inverse_identity, `ZhangLS.Spec.FiniteMobius.eval, `ZhangLS.Spec.FiniteMobius.finite_moebius_identity, `ZhangLS.Spec.FiniteMobius.finite_moebius_identity_four, `ZhangLS.Spec.FiniteMobius.finite_moebius_identity_endpoint, `ZhangLS.Spec.FiniteMobius.finite_moebius_identity_one]
  for n in expected do
    unless env.contains n do throwError "Missing public {n}"
    let some i := env.getModuleIdxFor? n | throwError "Missing owner {n}"
    unless env.header.moduleNames[i]! == owner do throwError "Wrong owner {n}"
  let expectedOwned : Array Name := #[`ZhangLS.Spec.FiniteMobius.truncated_mul_zeta_eq_one, `ZhangLS.Spec.FiniteMobius.eval._proof_1, `ZhangLS.Spec.FiniteMobius.finite_moebius_identity, `ZhangLS.Spec.FiniteMobius.moebius_mul_defect_pow_eq_zero, `ZhangLS.Spec.FiniteMobius.truncated_intCast, `ZhangLS.Spec.FiniteMobius.defect_pow_eq_zero, `ZhangLS.Spec.FiniteMobius.mul_eq_zero_of_right, `ZhangLS.Spec.FiniteMobius.truncated_apply_of_le, `ZhangLS.Spec.FiniteMobius.defect, `ZhangLS.Spec.FiniteMobius.truncated, `ZhangLS.Spec.FiniteMobius.truncated_apply, `ZhangLS.Spec.FiniteMobius.pow_eq_zero_of_le, `ZhangLS.Spec.FiniteMobius.mul_eq_zero_of_le, `ZhangLS.Spec.FiniteMobius.eval._proof_2, `ZhangLS.Spec.FiniteMobius.defect_eq_zero, `ZhangLS.Spec.FiniteMobius.finite_moebius_identity_one, `ZhangLS.Spec.FiniteMobius.eval, `ZhangLS.Spec.FiniteMobius.truncated._proof_1, `ZhangLS.Spec.FiniteMobius.binomial_inverse_identity, `ZhangLS.Spec.FiniteMobius.finite_moebius_identity_endpoint, `ZhangLS.Spec.FiniteMobius.finite_moebius_identity_four, `ZhangLS.Spec.FiniteMobius.defect.eq_1, `ZhangLS.Spec.FiniteMobius.truncated_apply_of_lt]
  let mut count := 0
  for (n,ci) in env.constants do
    if let some i := env.getModuleIdxFor? n then
      if env.header.moduleNames[i]! == owner then
        unless expectedOwned.contains n do throwError "Unexpected owned declaration {n}"
        let axs ← collectAxioms n
        unless axs.all (fun a => a == ``propext || a == ``Classical.choice || a == ``Quot.sound) do
          throwError "Nonstandard axioms {n}: {axs}"
        logInfo m!"OWNER {owner} DECL {n} AXIOMS {axs}"
        for dep in ci.getUsedConstantsAsSet do
          logInfo m!"DECL_REF {n} {dep}"
        count := count+1
  unless count == 23 && expected.size == 19 do throwError "Ownership/public count changed"
  for m in env.header.moduleNames do logInfo m!"LOADED_MODULE {m}"
  logInfo m!"OWNERSHIP_PASS {count} PUBLIC {expected.size}"
set_option pp.all true in
#check @ZhangLS.Spec.FiniteMobius.truncated
set_option pp.all true in
#check @ZhangLS.Spec.FiniteMobius.truncated_apply
set_option pp.all true in
#check @ZhangLS.Spec.FiniteMobius.truncated_apply_of_le
set_option pp.all true in
#check @ZhangLS.Spec.FiniteMobius.truncated_apply_of_lt
set_option pp.all true in
#check @ZhangLS.Spec.FiniteMobius.truncated_intCast
set_option pp.all true in
#check @ZhangLS.Spec.FiniteMobius.defect
set_option pp.all true in
#check @ZhangLS.Spec.FiniteMobius.truncated_mul_zeta_eq_one
set_option pp.all true in
#check @ZhangLS.Spec.FiniteMobius.defect_eq_zero
set_option pp.all true in
#check @ZhangLS.Spec.FiniteMobius.mul_eq_zero_of_le
set_option pp.all true in
#check @ZhangLS.Spec.FiniteMobius.pow_eq_zero_of_le
set_option pp.all true in
#check @ZhangLS.Spec.FiniteMobius.mul_eq_zero_of_right
set_option pp.all true in
#check @ZhangLS.Spec.FiniteMobius.defect_pow_eq_zero
set_option pp.all true in
#check @ZhangLS.Spec.FiniteMobius.moebius_mul_defect_pow_eq_zero
set_option pp.all true in
#check @ZhangLS.Spec.FiniteMobius.binomial_inverse_identity
set_option pp.all true in
#check @ZhangLS.Spec.FiniteMobius.eval
set_option pp.all true in
#check @ZhangLS.Spec.FiniteMobius.finite_moebius_identity
set_option pp.all true in
#check @ZhangLS.Spec.FiniteMobius.finite_moebius_identity_four
set_option pp.all true in
#check @ZhangLS.Spec.FiniteMobius.finite_moebius_identity_endpoint
set_option pp.all true in
#check @ZhangLS.Spec.FiniteMobius.finite_moebius_identity_one
