import audit.FixedHLambdaReplacementRegression
import audit.FixedHLambdaReplacementOuterRegression
set_option autoImplicit false
set_option maxHeartbeats 24000000
set_option maxRecDepth 10000
set_option pp.all true
set_option pp.privateNames true
set_option pp.proofs true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let out ← IO.getStdout
  let owners : Array Name := #[
    `ZhangLS.Spec.FixedHLambdaReplacement,
    `ZhangLS.Spec.FixedHLambdaReplacementLocal,
    `audit.FixedHLambdaReplacementRegression,
    `ZhangLS.Spec.FixedHLambdaReplacementOuter,
    `audit.FixedHLambdaReplacementOuterRegression
  ]
  let expectedPublic : Array (Name × Name) := #[
    (`ZhangLS.Spec.FixedHLambdaReplacement, `ZhangLS.Spec.FixedHLambdaReplacement.exp_error_linear),
    (`ZhangLS.Spec.FixedHLambdaReplacement, `ZhangLS.Spec.FixedHLambdaReplacement.paper_relative_error),
    (`ZhangLS.Spec.FixedHLambdaReplacement, `ZhangLS.Spec.FixedHLambdaReplacement.paper_relative_error_uniform),
    (`ZhangLS.Spec.FixedHLambdaReplacement, `ZhangLS.Spec.FixedHLambdaReplacement.relative_to_absolute),
    (`ZhangLS.Spec.FixedHLambdaReplacement, `ZhangLS.Spec.FixedHLambdaReplacement.paper_absolute_error_uniform),
    (`ZhangLS.Spec.FixedHLambdaReplacementLocal, `ZhangLS.Spec.FixedHLambdaReplacement.prime_baseline_pos),
    (`ZhangLS.Spec.FixedHLambdaReplacementLocal, `ZhangLS.Spec.FixedHLambdaReplacement.prime_baseline_ne_zero),
    (`ZhangLS.Spec.FixedHLambdaReplacementLocal, `ZhangLS.Spec.FixedHLambdaReplacement.normalizedFactor),
    (`ZhangLS.Spec.FixedHLambdaReplacementLocal, `ZhangLS.Spec.FixedHLambdaReplacement.normalizedFactor_error),
    (`ZhangLS.Spec.FixedHLambdaReplacementLocal, `ZhangLS.Spec.FixedHLambdaReplacement.totient_baseline_product),
    (`ZhangLS.Spec.FixedHLambdaReplacementLocal, `ZhangLS.Spec.FixedHLambdaReplacement.totient_baseline_ne_zero),
    (`ZhangLS.Spec.FixedHLambdaReplacementLocal, `ZhangLS.Spec.FixedHLambdaReplacement.normalized_product),
    (`ZhangLS.Spec.FixedHLambdaReplacementLocal, `ZhangLS.Spec.FixedHLambdaReplacement.relative_error_exp),
    (`audit.FixedHLambdaReplacementRegression, `ZhangLS.Spec.FixedHLambdaReplacement.regression_one),
    (`audit.FixedHLambdaReplacementRegression, `ZhangLS.Spec.FixedHLambdaReplacement.regression_prime_two),
    (`audit.FixedHLambdaReplacementRegression, `ZhangLS.Spec.FixedHLambdaReplacement.regression_two_factor),
    (`audit.FixedHLambdaReplacementRegression, `ZhangLS.Spec.FixedHLambdaReplacement.regression_three_shifts),
    (`audit.FixedHLambdaReplacementRegression, `ZhangLS.Spec.FixedHLambdaReplacement.regression_exact_product),
    (`audit.FixedHLambdaReplacementRegression, `ZhangLS.Spec.FixedHLambdaReplacement.regression_window),
    (`audit.FixedHLambdaReplacementRegression, `ZhangLS.Spec.FixedHLambdaReplacement.regression_uniform_actual),
    (`ZhangLS.Spec.FixedHLambdaReplacementOuter, `ZhangLS.Spec.FixedHLambdaReplacement.outerSum),
    (`ZhangLS.Spec.FixedHLambdaReplacementOuter, `ZhangLS.Spec.FixedHLambdaReplacement.baselineOuterSum),
    (`ZhangLS.Spec.FixedHLambdaReplacementOuter, `ZhangLS.Spec.FixedHLambdaReplacement.compact_norm_bound),
    (`ZhangLS.Spec.FixedHLambdaReplacementOuter, `ZhangLS.Spec.FixedHLambdaReplacement.cutoff_log),
    (`ZhangLS.Spec.FixedHLambdaReplacementOuter, `ZhangLS.Spec.FixedHLambdaReplacement.cutoff_harmonic),
    (`ZhangLS.Spec.FixedHLambdaReplacementOuter, `ZhangLS.Spec.FixedHLambdaReplacement.weighted_factor_error),
    (`ZhangLS.Spec.FixedHLambdaReplacementOuter, `ZhangLS.Spec.FixedHLambdaReplacement.finite_weighted_error),
    (`ZhangLS.Spec.FixedHLambdaReplacementOuter, `ZhangLS.Spec.FixedHLambdaReplacement.scalar_bound),
    (`ZhangLS.Spec.FixedHLambdaReplacementOuter, `ZhangLS.Spec.FixedHLambdaReplacement.outer_error_uniform),
    (`audit.FixedHLambdaReplacementOuterRegression, `ZhangLS.Spec.FixedHLambdaReplacement.outer_regression_zero_profile),
    (`audit.FixedHLambdaReplacementOuterRegression, `ZhangLS.Spec.FixedHLambdaReplacement.outer_regression_n_one),
    (`audit.FixedHLambdaReplacementOuterRegression, `ZhangLS.Spec.FixedHLambdaReplacement.outer_regression_harmonic),
    (`audit.FixedHLambdaReplacementOuterRegression, `ZhangLS.Spec.FixedHLambdaReplacement.outer_regression_scalar),
    (`audit.FixedHLambdaReplacementOuterRegression, `ZhangLS.Spec.FixedHLambdaReplacement.outer_regression_actual_uniform)
  ]
  let expectedOwned : Array (Name × Name × UInt64 × String) := #[
    (`ZhangLS.Spec.FixedHLambdaReplacement, `ZhangLS.Spec.FixedHLambdaReplacement.exp_error_linear, 7050130510082566029, "[]"),
    (`ZhangLS.Spec.FixedHLambdaReplacement, `ZhangLS.Spec.FixedHLambdaReplacement.paper_absolute_error_uniform, 5283271891632584369, "[]"),
    (`ZhangLS.Spec.FixedHLambdaReplacement, `ZhangLS.Spec.FixedHLambdaReplacement.paper_relative_error, 1390818518197302447, "[]"),
    (`ZhangLS.Spec.FixedHLambdaReplacement, `ZhangLS.Spec.FixedHLambdaReplacement.paper_relative_error_uniform, 15097743755722262120, "[]"),
    (`ZhangLS.Spec.FixedHLambdaReplacement, `ZhangLS.Spec.FixedHLambdaReplacement.relative_to_absolute, 5558933696164542093, "[]"),
    (`ZhangLS.Spec.FixedHLambdaReplacement, `ZhangLS.Spec.FixedHLambdaReplacement.relative_to_absolute._simp_1_1, 6033590925971773593, "[`u_2]"),
    (`ZhangLS.Spec.FixedHLambdaReplacement, `ZhangLS.Spec.FixedHLambdaReplacement.relative_to_absolute._simp_1_2, 13972439555833037651, "[`u_2]"),
    (`ZhangLS.Spec.FixedHLambdaReplacement, `ZhangLS.Spec.FixedHLambdaReplacement.relative_to_absolute._simp_1_3, 16412815542536123252, "[`u_2]"),
    (`ZhangLS.Spec.FixedHLambdaReplacement, `ZhangLS.Spec.FixedHLambdaReplacement.relative_to_absolute._simp_1_4, 2173808416608830180, "[`u_1]"),
    (`ZhangLS.Spec.FixedHLambdaReplacement, `ZhangLS.Spec.FixedHLambdaReplacement.relative_to_absolute._simp_1_5, 7579211897750796183, "[`u_1]"),
    (`ZhangLS.Spec.FixedHLambdaReplacement, `ZhangLS.Spec.FixedHLambdaReplacement.relative_to_absolute._simp_1_6, 5885927816594865294, "[`u_3]"),
    (`ZhangLS.Spec.FixedHLambdaReplacement, `ZhangLS.Spec.FixedHLambdaReplacement.relative_to_absolute._simp_1_7, 9303903170692057158, "[`u_1]"),
    (`ZhangLS.Spec.FixedHLambdaReplacementLocal, `ZhangLS.Spec.FixedHLambdaReplacement.normalizedFactor, 12492396891122923587, "[]"),
    (`ZhangLS.Spec.FixedHLambdaReplacementLocal, `ZhangLS.Spec.FixedHLambdaReplacement.normalizedFactor_error, 10523572856249488094, "[]"),
    (`ZhangLS.Spec.FixedHLambdaReplacementLocal, `ZhangLS.Spec.FixedHLambdaReplacement.normalized_product, 11236780218527028875, "[]"),
    (`ZhangLS.Spec.FixedHLambdaReplacementLocal, `ZhangLS.Spec.FixedHLambdaReplacement.prime_baseline_ne_zero, 8483941286143457791, "[]"),
    (`ZhangLS.Spec.FixedHLambdaReplacementLocal, `ZhangLS.Spec.FixedHLambdaReplacement.prime_baseline_pos, 3625950410434302711, "[]"),
    (`ZhangLS.Spec.FixedHLambdaReplacementLocal, `ZhangLS.Spec.FixedHLambdaReplacement.relative_error_exp, 7065069747542549613, "[]"),
    (`ZhangLS.Spec.FixedHLambdaReplacementLocal, `ZhangLS.Spec.FixedHLambdaReplacement.totient_baseline_ne_zero, 7386873316938677840, "[]"),
    (`ZhangLS.Spec.FixedHLambdaReplacementLocal, `ZhangLS.Spec.FixedHLambdaReplacement.totient_baseline_product, 2527572391818235200, "[]"),
    (`ZhangLS.Spec.FixedHLambdaReplacementLocal, `ZhangLS.Spec.FixedHLambdaReplacement.totient_baseline_product._simp_1_1, 6033590925971773593, "[`u_2]"),
    (`ZhangLS.Spec.FixedHLambdaReplacementLocal, `ZhangLS.Spec.FixedHLambdaReplacement.totient_baseline_product._simp_1_2, 13972439555833037651, "[`u_2]"),
    (`ZhangLS.Spec.FixedHLambdaReplacementLocal, `ZhangLS.Spec.FixedHLambdaReplacement.totient_baseline_product._simp_1_3, 16412815542536123252, "[`u_2]"),
    (`ZhangLS.Spec.FixedHLambdaReplacementLocal, `ZhangLS.Spec.FixedHLambdaReplacement.totient_baseline_product._simp_1_4, 2173808416608830180, "[`u_1]"),
    (`ZhangLS.Spec.FixedHLambdaReplacementLocal, `ZhangLS.Spec.FixedHLambdaReplacement.totient_baseline_product._simp_1_5, 7579211897750796183, "[`u_1]"),
    (`ZhangLS.Spec.FixedHLambdaReplacementLocal, `ZhangLS.Spec.FixedHLambdaReplacement.totient_baseline_product._simp_1_6, 5885927816594865294, "[`u_3]"),
    (`ZhangLS.Spec.FixedHLambdaReplacementLocal, `ZhangLS.Spec.FixedHLambdaReplacement.totient_baseline_product._simp_1_7, 9303903170692057158, "[`u_1]"),
    (`ZhangLS.Spec.FixedHLambdaReplacementOuter, `ZhangLS.Spec.FixedHLambdaReplacement.baselineOuterSum, 2696389773245719619, "[]"),
    (`ZhangLS.Spec.FixedHLambdaReplacementOuter, `ZhangLS.Spec.FixedHLambdaReplacement.compact_norm_bound, 951801835533173426, "[]"),
    (`ZhangLS.Spec.FixedHLambdaReplacementOuter, `ZhangLS.Spec.FixedHLambdaReplacement.cutoff_harmonic, 6626527819680878619, "[]"),
    (`ZhangLS.Spec.FixedHLambdaReplacementOuter, `ZhangLS.Spec.FixedHLambdaReplacement.cutoff_log, 3388770308504834535, "[]"),
    (`ZhangLS.Spec.FixedHLambdaReplacementOuter, `ZhangLS.Spec.FixedHLambdaReplacement.finite_weighted_error, 11938492019345824790, "[]"),
    (`ZhangLS.Spec.FixedHLambdaReplacementOuter, `ZhangLS.Spec.FixedHLambdaReplacement.outerSum, 10223136960935775, "[]"),
    (`ZhangLS.Spec.FixedHLambdaReplacementOuter, `ZhangLS.Spec.FixedHLambdaReplacement.outerSum._proof_1, 13939071296269336568, "[]"),
    (`ZhangLS.Spec.FixedHLambdaReplacementOuter, `ZhangLS.Spec.FixedHLambdaReplacement.outerSum._proof_2, 13161352971066462142, "[]"),
    (`ZhangLS.Spec.FixedHLambdaReplacementOuter, `ZhangLS.Spec.FixedHLambdaReplacement.outer_error_uniform, 15172635717273548372, "[]"),
    (`ZhangLS.Spec.FixedHLambdaReplacementOuter, `ZhangLS.Spec.FixedHLambdaReplacement.outer_error_uniform._proof_1_1, 14563404226154616004, "[]"),
    (`ZhangLS.Spec.FixedHLambdaReplacementOuter, `ZhangLS.Spec.FixedHLambdaReplacement.outer_error_uniform._simp_1_2, 6033590925971773593, "[`u_2]"),
    (`ZhangLS.Spec.FixedHLambdaReplacementOuter, `ZhangLS.Spec.FixedHLambdaReplacement.outer_error_uniform._simp_1_3, 13972439555833037651, "[`u_2]"),
    (`ZhangLS.Spec.FixedHLambdaReplacementOuter, `ZhangLS.Spec.FixedHLambdaReplacement.outer_error_uniform._simp_1_4, 16412815542536123252, "[`u_2]"),
    (`ZhangLS.Spec.FixedHLambdaReplacementOuter, `ZhangLS.Spec.FixedHLambdaReplacement.outer_error_uniform._simp_1_5, 2173808416608830180, "[`u_1]"),
    (`ZhangLS.Spec.FixedHLambdaReplacementOuter, `ZhangLS.Spec.FixedHLambdaReplacement.outer_error_uniform._simp_1_6, 7579211897750796183, "[`u_1]"),
    (`ZhangLS.Spec.FixedHLambdaReplacementOuter, `ZhangLS.Spec.FixedHLambdaReplacement.outer_error_uniform._simp_1_7, 5885927816594865294, "[`u_3]"),
    (`ZhangLS.Spec.FixedHLambdaReplacementOuter, `ZhangLS.Spec.FixedHLambdaReplacement.outer_error_uniform._simp_1_8, 9303903170692057158, "[`u_1]"),
    (`ZhangLS.Spec.FixedHLambdaReplacementOuter, `ZhangLS.Spec.FixedHLambdaReplacement.scalar_bound, 7475237315585688848, "[]"),
    (`ZhangLS.Spec.FixedHLambdaReplacementOuter, `ZhangLS.Spec.FixedHLambdaReplacement.weighted_factor_error, 6664195579694570045, "[]"),
    (`ZhangLS.Spec.FixedHLambdaReplacementOuter, `ZhangLS.Spec.FixedHLambdaReplacement.weighted_factor_error._simp_1_1, 6033590925971773593, "[`u_2]"),
    (`ZhangLS.Spec.FixedHLambdaReplacementOuter, `ZhangLS.Spec.FixedHLambdaReplacement.weighted_factor_error._simp_1_2, 13972439555833037651, "[`u_2]"),
    (`ZhangLS.Spec.FixedHLambdaReplacementOuter, `ZhangLS.Spec.FixedHLambdaReplacement.weighted_factor_error._simp_1_3, 16412815542536123252, "[`u_2]"),
    (`ZhangLS.Spec.FixedHLambdaReplacementOuter, `ZhangLS.Spec.FixedHLambdaReplacement.weighted_factor_error._simp_1_4, 2173808416608830180, "[`u_1]"),
    (`ZhangLS.Spec.FixedHLambdaReplacementOuter, `ZhangLS.Spec.FixedHLambdaReplacement.weighted_factor_error._simp_1_5, 7579211897750796183, "[`u_1]"),
    (`ZhangLS.Spec.FixedHLambdaReplacementOuter, `ZhangLS.Spec.FixedHLambdaReplacement.weighted_factor_error._simp_1_6, 5885927816594865294, "[`u_3]"),
    (`ZhangLS.Spec.FixedHLambdaReplacementOuter, `ZhangLS.Spec.FixedHLambdaReplacement.weighted_factor_error._simp_1_7, 9303903170692057158, "[`u_1]"),
    (`audit.FixedHLambdaReplacementOuterRegression, `ZhangLS.Spec.FixedHLambdaReplacement.baselineOuterSum.eq_1, 16104095950138588451, "[]"),
    (`audit.FixedHLambdaReplacementOuterRegression, `ZhangLS.Spec.FixedHLambdaReplacement.outerSum.eq_1, 13341168463637488612, "[]"),
    (`audit.FixedHLambdaReplacementOuterRegression, `ZhangLS.Spec.FixedHLambdaReplacement.outer_regression_actual_uniform, 15172635717273548372, "[]"),
    (`audit.FixedHLambdaReplacementOuterRegression, `ZhangLS.Spec.FixedHLambdaReplacement.outer_regression_harmonic, 6626527819680878619, "[]"),
    (`audit.FixedHLambdaReplacementOuterRegression, `ZhangLS.Spec.FixedHLambdaReplacement.outer_regression_n_one, 15250457565563154819, "[]"),
    (`audit.FixedHLambdaReplacementOuterRegression, `ZhangLS.Spec.FixedHLambdaReplacement.outer_regression_scalar, 7475237315585688848, "[]"),
    (`audit.FixedHLambdaReplacementOuterRegression, `ZhangLS.Spec.FixedHLambdaReplacement.outer_regression_zero_profile, 6949361644048481769, "[]"),
    (`audit.FixedHLambdaReplacementRegression, `ZhangLS.Spec.FixedHLambdaReplacement.normalizedFactor.eq_1, 6642453743604083527, "[]"),
    (`audit.FixedHLambdaReplacementRegression, `ZhangLS.Spec.FixedHLambdaReplacement.regression_exact_product, 11236780218527028875, "[]"),
    (`audit.FixedHLambdaReplacementRegression, `ZhangLS.Spec.FixedHLambdaReplacement.regression_one, 7083781848874614551, "[]"),
    (`audit.FixedHLambdaReplacementRegression, `ZhangLS.Spec.FixedHLambdaReplacement.regression_prime_two, 2594906992412556009, "[]"),
    (`audit.FixedHLambdaReplacementRegression, `ZhangLS.Spec.FixedHLambdaReplacement.regression_three_shifts, 18169577438003922552, "[]"),
    (`audit.FixedHLambdaReplacementRegression, `ZhangLS.Spec.FixedHLambdaReplacement.regression_two_factor, 16297206738810453453, "[]"),
    (`audit.FixedHLambdaReplacementRegression, `ZhangLS.Spec.FixedHLambdaReplacement.regression_uniform_actual, 15097743755722262120, "[]"),
    (`audit.FixedHLambdaReplacementRegression, `ZhangLS.Spec.FixedHLambdaReplacement.regression_window, 2626426576796535537, "[]")
  ]
  let mut seen : Array (Name × Name) := #[]
  for (name, ci) in env.constants do
    if let some idx := env.getModuleIdxFor? name then
      let owner := moduleNames[idx]!
      if owners.contains owner then
        if seen.contains (owner,name) then throwError "Duplicate declaration {name}"
        if ci.isAxiom then throwError "Owned axiom {name}"
        let axs ← collectAxioms name
        unless axs.all (fun a => a == ``propext || a == ``Classical.choice || a == ``Quot.sound) do
          throwError "Nonstandard transitive axiom at {name}: {axs}"
        let typePretty ← liftTermElabM <| Meta.ppExpr ci.type
        let some pin := expectedOwned.find? (fun p => p.1 == owner && p.2.1 == name)
          | throwError "Unexpected defining-module/name pair {owner} {name}"
        unless hash typePretty.pretty == pin.2.2.1 do
          throwError "Full elaborated type fingerprint drift {name}"
        unless reprStr ci.levelParams == pin.2.2.2 do
          throwError "Universe parameter drift {name}"
        let row := Json.mkObj [
          ("owner", toJson owner.toString),
          ("name", toJson name.toString),
          ("public", toJson (expectedPublic.contains (owner,name))),
          ("type_repr", toJson (reprStr ci.type)),
          ("type_lean_hash64", toJson (toString (hash typePretty.pretty))),
          ("type_pretty", toJson typePretty.pretty),
          ("universe_parameters_repr", toJson (reprStr ci.levelParams)),
          ("axioms", toJson (axs.map Name.toString)),
          ("used_constants", toJson (ci.getUsedConstantsAsSet.toArray.map Name.toString))]
        out.putStrLn s!"DECLARATION_JSON {row.compress}"
        out.flush
        seen := seen.push (owner,name)
  unless seen.size == 68 do throwError "Owned declaration count drift: {seen.size}"
  unless expectedOwned.size == 68 do throwError "Wrong pinned inventory count"
  for pin in expectedOwned do
    unless seen.contains (pin.1,pin.2.1) do throwError "Missing owned declaration {pin.2.1}"
  for pair in expectedPublic do
    unless seen.contains pair do throwError "Missing explicit declaration {pair.2}"
  for owner in owners do
    out.putStrLn s!"OWNER_COUNT {owner} {(seen.filter (fun p => p.1 == owner)).size}"
  for mod in moduleNames do
    out.putStrLn s!"LOADED_MODULE {mod}"
  out.putStrLn s!"OWNERSHIP_TYPE_AXIOM_PASS {seen.size} PUBLIC {expectedPublic.size}"
  out.flush
