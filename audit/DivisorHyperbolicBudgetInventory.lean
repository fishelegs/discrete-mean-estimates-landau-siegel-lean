import audit.DivisorHyperbolicBudgetRegression

/-! Defining-module ownership covers public declarations, generated helpers,
and every endpoint regression. Full elaborated types and transitive axioms
are exported for inspection; the final inventory pins all names and types. -/
set_option autoImplicit false
set_option maxHeartbeats 24000000
set_option maxRecDepth 10000
set_option pp.all true
set_option pp.privateNames true
set_option pp.proofs true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option pp.universes true

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let out ← IO.getStdout
  let owners : Array Name := #[
    `ZhangLS.Spec.DivisorHyperbolicBudgetSmallPower,
    `ZhangLS.Spec.DivisorHyperbolicBudgetWeights,
    `ZhangLS.Spec.DivisorHyperbolicBudgetGeometry,
    `ZhangLS.Spec.DivisorHyperbolicBudgetBound,
    `audit.DivisorHyperbolicBudgetRegression
  ]
  -- BEGIN PINS
  let expectedOwned : Array (Name × Name) := #[
    (`ZhangLS.Spec.DivisorHyperbolicBudgetBound, `ZhangLS.Spec.DivisorHyperbolicBudget.budget_le_floor_log),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetBound, `ZhangLS.Spec.DivisorHyperbolicBudget.budget_le_harmonic_product),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetBound, `ZhangLS.Spec.DivisorHyperbolicBudget.budget_le_harmonic_product._simp_1_1),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetBound, `ZhangLS.Spec.DivisorHyperbolicBudget.budget_le_harmonic_product._simp_1_2),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetBound, `ZhangLS.Spec.DivisorHyperbolicBudget.budget_le_log),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetBound, `ZhangLS.Spec.DivisorHyperbolicBudget.budget_le_log._proof_1_1),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetBound, `ZhangLS.Spec.DivisorHyperbolicBudget.nested_budget_le_log),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetGeometry, `ZhangLS.Spec.DivisorHyperbolicBudget.budget_eq_nested),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetGeometry, `ZhangLS.Spec.DivisorHyperbolicBudget.positive_floor),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetGeometry, `ZhangLS.Spec.DivisorHyperbolicBudget.row_eq),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetGeometry, `ZhangLS.Spec.DivisorHyperbolicBudget.weight.eq_1),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetGeometry, `ZhangLS.Spec.DivisorHyperbolicBudget.weight_one_left),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetGeometry, `ZhangLS.Spec.DivisorHyperbolicBudget.weight_one_right),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetSmallPower, `ZhangLS.Spec.DivisorHyperbolicBudget.smallPowerConstant),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetSmallPower, `ZhangLS.Spec.DivisorHyperbolicBudget.smallPowerConstant._proof_1),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetSmallPower, `ZhangLS.Spec.DivisorHyperbolicBudget.smallPowerConstant.eq_1),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetSmallPower, `ZhangLS.Spec.DivisorHyperbolicBudget.smallPowerConstant_pos),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetSmallPower, `ZhangLS.Spec.DivisorHyperbolicBudget.tau_five_sixteenth),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetSmallPower, `ZhangLS.Spec.DivisorHyperbolicBudget.tau_five_sixteenth._proof_1_1),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetWeights, `ZhangLS.Spec.DivisorHyperbolicBudget.budget),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetWeights, `ZhangLS.Spec.DivisorHyperbolicBudget.mem_pairs),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetWeights, `ZhangLS.Spec.DivisorHyperbolicBudget.mem_pairs_one_right),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetWeights, `ZhangLS.Spec.DivisorHyperbolicBudget.mem_pairs_one_right._proof_1_2),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetWeights, `ZhangLS.Spec.DivisorHyperbolicBudget.mem_pairs_one_right._simp_1_1),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetWeights, `ZhangLS.Spec.DivisorHyperbolicBudget.pairs),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetWeights, `ZhangLS.Spec.DivisorHyperbolicBudget.pairs_subset_rectangle),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetWeights, `ZhangLS.Spec.DivisorHyperbolicBudget.weight),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetWeights, `ZhangLS.Spec.DivisorHyperbolicBudget.weight_le),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetWeights, `ZhangLS.Spec.DivisorHyperbolicBudget.weight_nonneg),
    (`audit.DivisorHyperbolicBudgetRegression, `ZhangLS.Spec.DivisorHyperbolicBudget.budget.eq_1),
    (`audit.DivisorHyperbolicBudgetRegression, `ZhangLS.Spec.DivisorHyperbolicBudgetRegression.budget_at_one),
    (`audit.DivisorHyperbolicBudgetRegression, `ZhangLS.Spec.DivisorHyperbolicBudgetRegression.budget_at_two),
    (`audit.DivisorHyperbolicBudgetRegression, `ZhangLS.Spec.DivisorHyperbolicBudgetRegression.exact_fractional_row),
    (`audit.DivisorHyperbolicBudgetRegression, `ZhangLS.Spec.DivisorHyperbolicBudgetRegression.fractional_product_below_included),
    (`audit.DivisorHyperbolicBudgetRegression, `ZhangLS.Spec.DivisorHyperbolicBudgetRegression.fractional_product_boundary_excluded),
    (`audit.DivisorHyperbolicBudgetRegression, `ZhangLS.Spec.DivisorHyperbolicBudgetRegression.one_right_endpoint),
    (`audit.DivisorHyperbolicBudgetRegression, `ZhangLS.Spec.DivisorHyperbolicBudgetRegression.one_right_next_excluded),
    (`audit.DivisorHyperbolicBudgetRegression, `ZhangLS.Spec.DivisorHyperbolicBudgetRegression.pairs_at_one),
    (`audit.DivisorHyperbolicBudgetRegression, `ZhangLS.Spec.DivisorHyperbolicBudgetRegression.pairs_at_two),
    (`audit.DivisorHyperbolicBudgetRegression, `ZhangLS.Spec.DivisorHyperbolicBudgetRegression.pairs_at_two._simp_1_1),
    (`audit.DivisorHyperbolicBudgetRegression, `ZhangLS.Spec.DivisorHyperbolicBudgetRegression.pairs_at_two._simp_1_2),
    (`audit.DivisorHyperbolicBudgetRegression, `ZhangLS.Spec.DivisorHyperbolicBudgetRegression.product_boundary_included),
    (`audit.DivisorHyperbolicBudgetRegression, `ZhangLS.Spec.DivisorHyperbolicBudgetRegression.real_floor_budget),
    (`audit.DivisorHyperbolicBudgetRegression, `ZhangLS.Spec.DivisorHyperbolicBudgetRegression.rectangle_corner_excluded),
    (`audit.DivisorHyperbolicBudgetRegression, `ZhangLS.Spec.DivisorHyperbolicBudgetRegression.sharp_one_endpoint),
    (`audit.DivisorHyperbolicBudgetRegression, `ZhangLS.Spec.DivisorHyperbolicBudgetRegression.small_power_one),
    (`audit.DivisorHyperbolicBudgetRegression, `ZhangLS.Spec.DivisorHyperbolicBudgetRegression.small_power_prime_power),
    (`audit.DivisorHyperbolicBudgetRegression, `ZhangLS.Spec.DivisorHyperbolicBudgetRegression.tau_at_one),
    (`audit.DivisorHyperbolicBudgetRegression, `ZhangLS.Spec.DivisorHyperbolicBudgetRegression.tau_at_two),
    (`audit.DivisorHyperbolicBudgetRegression, `ZhangLS.Spec.DivisorHyperbolicBudgetRegression.zero_left_excluded),
    (`audit.DivisorHyperbolicBudgetRegression, `ZhangLS.Spec.DivisorHyperbolicBudgetRegression.zero_left_excluded._simp_1_1),
    (`audit.DivisorHyperbolicBudgetRegression, `ZhangLS.Spec.DivisorHyperbolicBudgetRegression.zero_left_excluded._simp_1_2),
    (`audit.DivisorHyperbolicBudgetRegression, `ZhangLS.Spec.DivisorHyperbolicBudgetRegression.zero_right_excluded),
    (`audit.DivisorHyperbolicBudgetRegression, `ZhangLS.Spec.DivisorHyperbolicBudgetRegression.zero_right_excluded._simp_1_1),
    (`audit.DivisorHyperbolicBudgetRegression, `ZhangLS.Spec.DivisorHyperbolicBudgetRegression.zero_right_excluded._simp_1_2)
  ]
  let expectedTypes : Array (Name × UInt64 × String) := #[
    (`ZhangLS.Spec.DivisorHyperbolicBudget.budget_le_floor_log, 636862864316683972, "[]"),
    (`ZhangLS.Spec.DivisorHyperbolicBudget.budget_le_harmonic_product, 4600260198521927738, "[]"),
    (`ZhangLS.Spec.DivisorHyperbolicBudget.budget_le_harmonic_product._simp_1_1, 16894297925195833955, "[`u_1, `u_4]"),
    (`ZhangLS.Spec.DivisorHyperbolicBudget.budget_le_harmonic_product._simp_1_2, 5656187468516604041, "[`u_1, `u_4]"),
    (`ZhangLS.Spec.DivisorHyperbolicBudget.budget_le_log, 3991746315551727971, "[]"),
    (`ZhangLS.Spec.DivisorHyperbolicBudget.budget_le_log._proof_1_1, 561581394585304039, "[]"),
    (`ZhangLS.Spec.DivisorHyperbolicBudget.nested_budget_le_log, 17775219898382058706, "[]"),
    (`ZhangLS.Spec.DivisorHyperbolicBudget.budget_eq_nested, 17900426353454907225, "[]"),
    (`ZhangLS.Spec.DivisorHyperbolicBudget.positive_floor, 14868682000377174882, "[]"),
    (`ZhangLS.Spec.DivisorHyperbolicBudget.row_eq, 9763112467926315167, "[]"),
    (`ZhangLS.Spec.DivisorHyperbolicBudget.weight.eq_1, 12975476866123624968, "[]"),
    (`ZhangLS.Spec.DivisorHyperbolicBudget.weight_one_left, 10596716731175059956, "[]"),
    (`ZhangLS.Spec.DivisorHyperbolicBudget.weight_one_right, 11343223962294035587, "[]"),
    (`ZhangLS.Spec.DivisorHyperbolicBudget.smallPowerConstant, 9035701922190319447, "[]"),
    (`ZhangLS.Spec.DivisorHyperbolicBudget.smallPowerConstant._proof_1, 8609675347731722958, "[]"),
    (`ZhangLS.Spec.DivisorHyperbolicBudget.smallPowerConstant.eq_1, 2873596108141561573, "[]"),
    (`ZhangLS.Spec.DivisorHyperbolicBudget.smallPowerConstant_pos, 13476300080343964158, "[]"),
    (`ZhangLS.Spec.DivisorHyperbolicBudget.tau_five_sixteenth, 16835259519951450494, "[]"),
    (`ZhangLS.Spec.DivisorHyperbolicBudget.tau_five_sixteenth._proof_1_1, 2367116725291308003, "[]"),
    (`ZhangLS.Spec.DivisorHyperbolicBudget.budget, 17116254445268886208, "[]"),
    (`ZhangLS.Spec.DivisorHyperbolicBudget.mem_pairs, 18388559656033575744, "[]"),
    (`ZhangLS.Spec.DivisorHyperbolicBudget.mem_pairs_one_right, 416336212126008, "[]"),
    (`ZhangLS.Spec.DivisorHyperbolicBudget.mem_pairs_one_right._proof_1_2, 16425412677689121956, "[]"),
    (`ZhangLS.Spec.DivisorHyperbolicBudget.mem_pairs_one_right._simp_1_1, 11962153716898683518, "[]"),
    (`ZhangLS.Spec.DivisorHyperbolicBudget.pairs, 14140341385002758897, "[]"),
    (`ZhangLS.Spec.DivisorHyperbolicBudget.pairs_subset_rectangle, 9254212348456393510, "[]"),
    (`ZhangLS.Spec.DivisorHyperbolicBudget.weight, 13537011181827974671, "[]"),
    (`ZhangLS.Spec.DivisorHyperbolicBudget.weight_le, 42185605430208541, "[]"),
    (`ZhangLS.Spec.DivisorHyperbolicBudget.weight_nonneg, 3344464989120326699, "[]"),
    (`ZhangLS.Spec.DivisorHyperbolicBudget.budget.eq_1, 2124162273881920273, "[]"),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetRegression.budget_at_one, 2910580004775895566, "[]"),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetRegression.budget_at_two, 4053417464298285711, "[]"),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetRegression.exact_fractional_row, 17167904484341268220, "[]"),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetRegression.fractional_product_below_included, 3156749166818392265, "[]"),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetRegression.fractional_product_boundary_excluded, 2602393218342905080, "[]"),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetRegression.one_right_endpoint, 8523640989052439450, "[]"),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetRegression.one_right_next_excluded, 18431940749868562202, "[]"),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetRegression.pairs_at_one, 17410376578551170436, "[]"),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetRegression.pairs_at_two, 387064691485829945, "[]"),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetRegression.pairs_at_two._simp_1_1, 16280161512472886946, "[`u_1]"),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetRegression.pairs_at_two._simp_1_2, 6974893438119822849, "[`u_1]"),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetRegression.product_boundary_included, 11248590211173954845, "[]"),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetRegression.real_floor_budget, 17775219898382058706, "[]"),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetRegression.rectangle_corner_excluded, 13766897431490420977, "[]"),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetRegression.sharp_one_endpoint, 4661041127815230032, "[]"),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetRegression.small_power_one, 13945007226346917955, "[]"),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetRegression.small_power_prime_power, 10101151039024025080, "[]"),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetRegression.tau_at_one, 4402612644995041977, "[]"),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetRegression.tau_at_two, 17466979618966494052, "[]"),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetRegression.zero_left_excluded, 7532642524464035412, "[]"),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetRegression.zero_left_excluded._simp_1_1, 16887500431887211030, "[]"),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetRegression.zero_left_excluded._simp_1_2, 6123147540510870229, "[]"),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetRegression.zero_right_excluded, 14328601767609073923, "[]"),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetRegression.zero_right_excluded._simp_1_1, 16887500431887211030, "[]"),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetRegression.zero_right_excluded._simp_1_2, 6123147540510870229, "[]")
  ]
  let expectedPublic : Array (Name × Name) := #[
    (`ZhangLS.Spec.DivisorHyperbolicBudgetBound, `ZhangLS.Spec.DivisorHyperbolicBudget.budget_le_floor_log),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetBound, `ZhangLS.Spec.DivisorHyperbolicBudget.budget_le_harmonic_product),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetBound, `ZhangLS.Spec.DivisorHyperbolicBudget.budget_le_log),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetBound, `ZhangLS.Spec.DivisorHyperbolicBudget.nested_budget_le_log),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetGeometry, `ZhangLS.Spec.DivisorHyperbolicBudget.budget_eq_nested),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetGeometry, `ZhangLS.Spec.DivisorHyperbolicBudget.positive_floor),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetGeometry, `ZhangLS.Spec.DivisorHyperbolicBudget.row_eq),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetGeometry, `ZhangLS.Spec.DivisorHyperbolicBudget.weight_one_left),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetGeometry, `ZhangLS.Spec.DivisorHyperbolicBudget.weight_one_right),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetSmallPower, `ZhangLS.Spec.DivisorHyperbolicBudget.smallPowerConstant),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetSmallPower, `ZhangLS.Spec.DivisorHyperbolicBudget.smallPowerConstant_pos),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetSmallPower, `ZhangLS.Spec.DivisorHyperbolicBudget.tau_five_sixteenth),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetWeights, `ZhangLS.Spec.DivisorHyperbolicBudget.budget),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetWeights, `ZhangLS.Spec.DivisorHyperbolicBudget.mem_pairs),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetWeights, `ZhangLS.Spec.DivisorHyperbolicBudget.mem_pairs_one_right),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetWeights, `ZhangLS.Spec.DivisorHyperbolicBudget.pairs),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetWeights, `ZhangLS.Spec.DivisorHyperbolicBudget.pairs_subset_rectangle),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetWeights, `ZhangLS.Spec.DivisorHyperbolicBudget.weight),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetWeights, `ZhangLS.Spec.DivisorHyperbolicBudget.weight_le),
    (`ZhangLS.Spec.DivisorHyperbolicBudgetWeights, `ZhangLS.Spec.DivisorHyperbolicBudget.weight_nonneg),
    (`audit.DivisorHyperbolicBudgetRegression, `ZhangLS.Spec.DivisorHyperbolicBudgetRegression.budget_at_one),
    (`audit.DivisorHyperbolicBudgetRegression, `ZhangLS.Spec.DivisorHyperbolicBudgetRegression.budget_at_two),
    (`audit.DivisorHyperbolicBudgetRegression, `ZhangLS.Spec.DivisorHyperbolicBudgetRegression.exact_fractional_row),
    (`audit.DivisorHyperbolicBudgetRegression, `ZhangLS.Spec.DivisorHyperbolicBudgetRegression.fractional_product_below_included),
    (`audit.DivisorHyperbolicBudgetRegression, `ZhangLS.Spec.DivisorHyperbolicBudgetRegression.fractional_product_boundary_excluded),
    (`audit.DivisorHyperbolicBudgetRegression, `ZhangLS.Spec.DivisorHyperbolicBudgetRegression.one_right_endpoint),
    (`audit.DivisorHyperbolicBudgetRegression, `ZhangLS.Spec.DivisorHyperbolicBudgetRegression.one_right_next_excluded),
    (`audit.DivisorHyperbolicBudgetRegression, `ZhangLS.Spec.DivisorHyperbolicBudgetRegression.pairs_at_one),
    (`audit.DivisorHyperbolicBudgetRegression, `ZhangLS.Spec.DivisorHyperbolicBudgetRegression.pairs_at_two),
    (`audit.DivisorHyperbolicBudgetRegression, `ZhangLS.Spec.DivisorHyperbolicBudgetRegression.product_boundary_included),
    (`audit.DivisorHyperbolicBudgetRegression, `ZhangLS.Spec.DivisorHyperbolicBudgetRegression.real_floor_budget),
    (`audit.DivisorHyperbolicBudgetRegression, `ZhangLS.Spec.DivisorHyperbolicBudgetRegression.rectangle_corner_excluded),
    (`audit.DivisorHyperbolicBudgetRegression, `ZhangLS.Spec.DivisorHyperbolicBudgetRegression.sharp_one_endpoint),
    (`audit.DivisorHyperbolicBudgetRegression, `ZhangLS.Spec.DivisorHyperbolicBudgetRegression.small_power_one),
    (`audit.DivisorHyperbolicBudgetRegression, `ZhangLS.Spec.DivisorHyperbolicBudgetRegression.small_power_prime_power),
    (`audit.DivisorHyperbolicBudgetRegression, `ZhangLS.Spec.DivisorHyperbolicBudgetRegression.tau_at_one),
    (`audit.DivisorHyperbolicBudgetRegression, `ZhangLS.Spec.DivisorHyperbolicBudgetRegression.tau_at_two),
    (`audit.DivisorHyperbolicBudgetRegression, `ZhangLS.Spec.DivisorHyperbolicBudgetRegression.zero_left_excluded),
    (`audit.DivisorHyperbolicBudgetRegression, `ZhangLS.Spec.DivisorHyperbolicBudgetRegression.zero_right_excluded)
  ]
  -- END PINS
  let mut seen : Array (Name × Name) := #[]
  for (name, ci) in env.constants do
    if let some idx := env.getModuleIdxFor? name then
      let owner := moduleNames[idx]!
      if owners.contains owner then
        if seen.contains (owner, name) then throwError "Duplicate owned declaration {name}"
        if ci.isAxiom then throwError "Owned axiom {name}"
        let axs ← collectAxioms name
        unless axs.all (fun a => a == ``propext || a == ``Classical.choice || a == ``Quot.sound) do
          throwError "Nonstandard transitive axiom {name}: {axs}"
        let typePretty ← liftTermElabM <| Meta.ppExpr ci.type
        unless expectedOwned.isEmpty do
          unless expectedOwned.contains (owner, name) do
            throwError "Unexpected defining-module/name pair {owner} {name}"
          let some (_, pinnedType, pinnedUniverses) := expectedTypes.find? (fun p => p.1 == name)
            | throwError "Missing type pin {name}"
          unless hash typePretty.pretty == pinnedType do
            throwError "Full elaborated type fingerprint drift {name}"
          unless reprStr ci.levelParams == pinnedUniverses do
            throwError "Universe parameter drift {name}"
        let row := Json.mkObj [
          ("owner", toJson owner.toString),
          ("name", toJson name.toString),
          ("public", toJson (expectedPublic.contains (owner, name))),
          ("type_repr", toJson (reprStr ci.type)),
          ("type_lean_hash64", toJson (toString (hash typePretty.pretty))),
          ("type_pretty", toJson typePretty.pretty),
          ("universe_parameters_repr", toJson (reprStr ci.levelParams)),
          ("axioms", toJson (axs.map Name.toString)),
          ("used_constants", toJson (ci.getUsedConstantsAsSet.toArray.map Name.toString))]
        out.putStrLn s!"DECLARATION_JSON {row.compress}"
        out.flush
        seen := seen.push (owner, name)
  unless expectedOwned.isEmpty do
    unless seen.size == expectedOwned.size && seen.size == expectedTypes.size do
      throwError "Owned declaration count drift: {seen.size}"
    for pair in expectedOwned do
      unless seen.contains pair do throwError "Missing owned declaration {pair.2}"
    for pair in expectedPublic do
      unless seen.contains pair do throwError "Missing explicit declaration {pair.2}"
  for owner in owners do
    out.putStrLn s!"OWNER_COUNT {owner} {(seen.filter (fun p => p.1 == owner)).size}"
  for mod in moduleNames do
    out.putStrLn s!"LOADED_MODULE {mod}"
  out.putStrLn s!"OWNERSHIP_TYPE_AXIOM_PASS {seen.size} PUBLIC {expectedPublic.size}"
  out.flush
