import audit.RamifiedHeadHarmonicRegression
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
  let modules := env.header.moduleNames
  let out ← IO.getStdout
  for m in modules do out.putStrLn s!"LOADED_MODULE {m}"
  let owners : Array Name := #[
    `ZhangLS.Spec.RamifiedHeadHarmonicTau,
    `ZhangLS.Spec.RamifiedHeadHarmonicCharacter,
    `ZhangLS.Spec.RamifiedHeadHarmonicMajorants,
    `ZhangLS.Spec.RamifiedHeadHarmonicReindex,
    `ZhangLS.Spec.RamifiedHeadHarmonicBound,
    `audit.RamifiedHeadHarmonicRegression
  ]
  let expectedPublic : Array (Name × Name) := #[
    (`ZhangLS.Spec.RamifiedHeadHarmonicTau, `ZhangLS.Spec.ramified_tau_mul_le),
    (`ZhangLS.Spec.RamifiedHeadHarmonicTau, `ZhangLS.Spec.ramified_tau_mul_le_real),
    (`ZhangLS.Spec.RamifiedHeadHarmonicTau, `ZhangLS.Spec.ramified_tau_convolution),
    (`ZhangLS.Spec.RamifiedHeadHarmonicTau, `ZhangLS.Spec.ramified_tau_convolution_real),
    (`ZhangLS.Spec.RamifiedHeadHarmonicTau, `ZhangLS.Spec.ramified_tau_four_convolution),
    (`ZhangLS.Spec.RamifiedHeadHarmonicCharacter, `ZhangLS.Spec.ramifiedHead_nu_prime_power),
    (`ZhangLS.Spec.RamifiedHeadHarmonicCharacter, `ZhangLS.Spec.ramifiedHead_nu_mul_divisor),
    (`ZhangLS.Spec.RamifiedHeadHarmonicMajorants, `ZhangLS.Spec.ramifiedHead_upsilon_norm_le_nu),
    (`ZhangLS.Spec.RamifiedHeadHarmonicMajorants, `ZhangLS.Spec.ramifiedHead_nu_norm_le_tau_two),
    (`ZhangLS.Spec.RamifiedHeadHarmonicMajorants, `ZhangLS.Spec.ramifiedHeadNuWeight),
    (`ZhangLS.Spec.RamifiedHeadHarmonicMajorants, `ZhangLS.Spec.ramifiedHead_nu_weight_nonneg),
    (`ZhangLS.Spec.RamifiedHeadHarmonicMajorants, `ZhangLS.Spec.ramifiedHead_nu_weight_le_tau_product),
    (`ZhangLS.Spec.RamifiedHeadHarmonicMajorants, `ZhangLS.Spec.ramifiedHead_nu_weight_harmonic_le),
    (`ZhangLS.Spec.RamifiedHeadHarmonicMajorants, `ZhangLS.Spec.ramifiedHead_nu_weight_log_le),
    (`ZhangLS.Spec.RamifiedHeadHarmonicReindex, `ZhangLS.Spec.ramifiedHeadPairs),
    (`ZhangLS.Spec.RamifiedHeadHarmonicReindex, `ZhangLS.Spec.ramifiedHeadSplit),
    (`ZhangLS.Spec.RamifiedHeadHarmonicReindex, `ZhangLS.Spec.ramifiedHead_split_data),
    (`ZhangLS.Spec.RamifiedHeadHarmonicReindex, `ZhangLS.Spec.ramifiedHead_split_injective),
    (`ZhangLS.Spec.RamifiedHeadHarmonicReindex, `ZhangLS.Spec.ramifiedHead_reindex_le),
    (`ZhangLS.Spec.RamifiedHeadHarmonicBound, `ZhangLS.Spec.ramifiedHead_nu_weight_mul),
    (`ZhangLS.Spec.RamifiedHeadHarmonicBound, `ZhangLS.Spec.ramifiedHead_nu_pair_fibre_le),
    (`ZhangLS.Spec.RamifiedHeadHarmonicBound, `ZhangLS.Spec.ramifiedHead_nu_pair_harmonic_le),
    (`ZhangLS.Spec.RamifiedHeadHarmonicBound, `ZhangLS.Spec.ramifiedHead_actual_pair_le),
    (`ZhangLS.Spec.RamifiedHeadHarmonicBound, `ZhangLS.Spec.ramifiedHead_actual_harmonic_le),
    (`ZhangLS.Spec.RamifiedHeadHarmonicBound, `ZhangLS.Spec.ramifiedHead_actual_log_le),
    (`audit.RamifiedHeadHarmonicRegression, `ZhangLS.Spec.ramifiedHeadUnitCharacter),
    (`audit.RamifiedHeadHarmonicRegression, `ZhangLS.Spec.ramifiedHead_unit_endpoint),
    (`audit.RamifiedHeadHarmonicRegression, `ZhangLS.Spec.ramifiedHead_one_cutoff_empty),
    (`audit.RamifiedHeadHarmonicRegression, `ZhangLS.Spec.ramifiedHead_composite_overlap),
    (`audit.RamifiedHeadHarmonicRegression, `ZhangLS.Spec.ramifiedHead_prime_power_overlap),
    (`audit.RamifiedHeadHarmonicRegression, `ZhangLS.Spec.ramifiedHead_zero_argument),
    (`audit.RamifiedHeadHarmonicRegression, `ZhangLS.Spec.ramifiedHead_composite_split),
    (`audit.RamifiedHeadHarmonicRegression, `ZhangLS.Spec.ramifiedHead_composite_pair_retained),
    (`audit.RamifiedHeadHarmonicRegression, `ZhangLS.Spec.ramifiedHead_zero_index_excluded)
  ]
  let expectedOwned : Array (Name × Name × UInt64 × String) := #[
    (`ZhangLS.Spec.RamifiedHeadHarmonicBound, `ZhangLS.Spec.ramifiedHeadNuWeight.eq_1, 13968736512271538568, "[]"),
    (`ZhangLS.Spec.RamifiedHeadHarmonicBound, `ZhangLS.Spec.ramifiedHeadPairs.eq_1, 16346591885540175632, "[]"),
    (`ZhangLS.Spec.RamifiedHeadHarmonicBound, `ZhangLS.Spec.ramifiedHead_actual_harmonic_le, 8953126496155536046, "[]"),
    (`ZhangLS.Spec.RamifiedHeadHarmonicBound, `ZhangLS.Spec.ramifiedHead_actual_log_le, 7966152018007316202, "[]"),
    (`ZhangLS.Spec.RamifiedHeadHarmonicBound, `ZhangLS.Spec.ramifiedHead_actual_pair_le, 16673654593345909236, "[]"),
    (`ZhangLS.Spec.RamifiedHeadHarmonicBound, `ZhangLS.Spec.ramifiedHead_nu_pair_fibre_le, 466121866633716584, "[]"),
    (`ZhangLS.Spec.RamifiedHeadHarmonicBound, `ZhangLS.Spec.ramifiedHead_nu_pair_harmonic_le, 1929895778057853188, "[]"),
    (`ZhangLS.Spec.RamifiedHeadHarmonicBound, `ZhangLS.Spec.ramifiedHead_nu_pair_harmonic_le._simp_1_1, 16894297925195833955, "[`u_1, `u_4]"),
    (`ZhangLS.Spec.RamifiedHeadHarmonicBound, `ZhangLS.Spec.ramifiedHead_nu_pair_harmonic_le._simp_1_2, 5656187468516604041, "[`u_1, `u_4]"),
    (`ZhangLS.Spec.RamifiedHeadHarmonicBound, `ZhangLS.Spec.ramifiedHead_nu_weight_mul, 13672105960202189776, "[]"),
    (`ZhangLS.Spec.RamifiedHeadHarmonicBound, `ZhangLS.Spec.ramifiedHead_nu_weight_mul._proof_1_1, 11829166964669741541, "[]"),
    (`ZhangLS.Spec.RamifiedHeadHarmonicCharacter, `ZhangLS.Spec.ramifiedHead_nu_mul_divisor, 619019638551790705, "[]"),
    (`ZhangLS.Spec.RamifiedHeadHarmonicCharacter, `ZhangLS.Spec.ramifiedHead_nu_prime_power, 16409338302339993492, "[]"),
    (`ZhangLS.Spec.RamifiedHeadHarmonicMajorants, `ZhangLS.Spec.ramifiedHeadNuWeight, 3975182968500249942, "[]"),
    (`ZhangLS.Spec.RamifiedHeadHarmonicMajorants, `ZhangLS.Spec.ramifiedHead_nu_norm_le_tau_two, 10602607274744673679, "[]"),
    (`ZhangLS.Spec.RamifiedHeadHarmonicMajorants, `ZhangLS.Spec.ramifiedHead_nu_weight_harmonic_le, 11473233400191425845, "[]"),
    (`ZhangLS.Spec.RamifiedHeadHarmonicMajorants, `ZhangLS.Spec.ramifiedHead_nu_weight_harmonic_le._proof_1_1, 15569380487145854131, "[]"),
    (`ZhangLS.Spec.RamifiedHeadHarmonicMajorants, `ZhangLS.Spec.ramifiedHead_nu_weight_harmonic_le._proof_1_2, 13292249257920414825, "[]"),
    (`ZhangLS.Spec.RamifiedHeadHarmonicMajorants, `ZhangLS.Spec.ramifiedHead_nu_weight_le_tau_product, 1444324286456255838, "[]"),
    (`ZhangLS.Spec.RamifiedHeadHarmonicMajorants, `ZhangLS.Spec.ramifiedHead_nu_weight_log_le, 2067920346411890467, "[]"),
    (`ZhangLS.Spec.RamifiedHeadHarmonicMajorants, `ZhangLS.Spec.ramifiedHead_nu_weight_log_le._proof_1_1, 15569380487145854131, "[]"),
    (`ZhangLS.Spec.RamifiedHeadHarmonicMajorants, `ZhangLS.Spec.ramifiedHead_nu_weight_log_le._proof_1_2, 13292249257920414825, "[]"),
    (`ZhangLS.Spec.RamifiedHeadHarmonicMajorants, `ZhangLS.Spec.ramifiedHead_nu_weight_nonneg, 17148273411145345325, "[]"),
    (`ZhangLS.Spec.RamifiedHeadHarmonicMajorants, `ZhangLS.Spec.ramifiedHead_upsilon_norm_le_nu, 14345485099920820467, "[]"),
    (`audit.RamifiedHeadHarmonicRegression, `ZhangLS.Spec.ramifiedHeadSplit.eq_1, 6414528823276886621, "[]"),
    (`audit.RamifiedHeadHarmonicRegression, `ZhangLS.Spec.ramifiedHeadUnitCharacter, 12748878753455877914, "[]"),
    (`audit.RamifiedHeadHarmonicRegression, `ZhangLS.Spec.ramifiedHeadUnitCharacter._proof_1, 2676763558076001517, "[]"),
    (`audit.RamifiedHeadHarmonicRegression, `ZhangLS.Spec.ramifiedHeadUnitCharacter._proof_2, 11876626948914792030, "[]"),
    (`audit.RamifiedHeadHarmonicRegression, `ZhangLS.Spec.ramifiedHeadUnitCharacter._proof_3, 8560371134890902648, "[]"),
    (`audit.RamifiedHeadHarmonicRegression, `ZhangLS.Spec.ramifiedHeadUnitCharacter._proof_4, 15064167362310750461, "[]"),
    (`audit.RamifiedHeadHarmonicRegression, `ZhangLS.Spec.ramifiedHead_composite_overlap, 17967183904810749301, "[]"),
    (`audit.RamifiedHeadHarmonicRegression, `ZhangLS.Spec.ramifiedHead_composite_overlap._proof_1_1, 8396299506257400546, "[]"),
    (`audit.RamifiedHeadHarmonicRegression, `ZhangLS.Spec.ramifiedHead_composite_pair_retained, 8685315539882036317, "[]"),
    (`audit.RamifiedHeadHarmonicRegression, `ZhangLS.Spec.ramifiedHead_composite_pair_retained._simp_1_1, 1988649516832762782, "[`u_1]"),
    (`audit.RamifiedHeadHarmonicRegression, `ZhangLS.Spec.ramifiedHead_composite_pair_retained._simp_1_2, 13318128363268500191, "[`u_1, `u_2]"),
    (`audit.RamifiedHeadHarmonicRegression, `ZhangLS.Spec.ramifiedHead_composite_pair_retained._simp_1_3, 10178972178374386679, "[`u_1]"),
    (`audit.RamifiedHeadHarmonicRegression, `ZhangLS.Spec.ramifiedHead_composite_split, 9437067546013088103, "[]"),
    (`audit.RamifiedHeadHarmonicRegression, `ZhangLS.Spec.ramifiedHead_one_cutoff_empty, 10716887276431324160, "[]"),
    (`audit.RamifiedHeadHarmonicRegression, `ZhangLS.Spec.ramifiedHead_one_cutoff_empty._proof_1_1, 11722099740780654278, "[]"),
    (`audit.RamifiedHeadHarmonicRegression, `ZhangLS.Spec.ramifiedHead_one_cutoff_empty._proof_1_2, 7660840203808675752, "[]"),
    (`audit.RamifiedHeadHarmonicRegression, `ZhangLS.Spec.ramifiedHead_prime_power_overlap, 7464073553808669369, "[]"),
    (`audit.RamifiedHeadHarmonicRegression, `ZhangLS.Spec.ramifiedHead_prime_power_overlap._proof_1_1, 5763804066660766121, "[]"),
    (`audit.RamifiedHeadHarmonicRegression, `ZhangLS.Spec.ramifiedHead_unit_endpoint, 11523813084435840905, "[]"),
    (`audit.RamifiedHeadHarmonicRegression, `ZhangLS.Spec.ramifiedHead_zero_argument, 7346046089047494441, "[]"),
    (`audit.RamifiedHeadHarmonicRegression, `ZhangLS.Spec.ramifiedHead_zero_argument._proof_1_1, 8396299506257400546, "[]"),
    (`audit.RamifiedHeadHarmonicRegression, `ZhangLS.Spec.ramifiedHead_zero_index_excluded, 5446191839253268411, "[]"),
    (`ZhangLS.Spec.RamifiedHeadHarmonicReindex, `ZhangLS.Spec.ramifiedHeadPairs, 11733851934634403370, "[]"),
    (`ZhangLS.Spec.RamifiedHeadHarmonicReindex, `ZhangLS.Spec.ramifiedHeadSplit, 5661767426013873714, "[]"),
    (`ZhangLS.Spec.RamifiedHeadHarmonicReindex, `ZhangLS.Spec.ramifiedHead_reindex_le, 4258328052669683407, "[]"),
    (`ZhangLS.Spec.RamifiedHeadHarmonicReindex, `ZhangLS.Spec.ramifiedHead_split_data, 4102721236436226711, "[]"),
    (`ZhangLS.Spec.RamifiedHeadHarmonicReindex, `ZhangLS.Spec.ramifiedHead_split_injective, 15292438701863315005, "[]"),
    (`ZhangLS.Spec.RamifiedHeadHarmonicTau, `ZhangLS.Spec.ramified_tau_convolution, 3992895295399433516, "[]"),
    (`ZhangLS.Spec.RamifiedHeadHarmonicTau, `ZhangLS.Spec.ramified_tau_convolution_real, 17438836315137034276, "[]"),
    (`ZhangLS.Spec.RamifiedHeadHarmonicTau, `ZhangLS.Spec.ramified_tau_four_convolution, 12486380682595316181, "[]"),
    (`ZhangLS.Spec.RamifiedHeadHarmonicTau, `ZhangLS.Spec.ramified_tau_mul_le, 3680060442039885318, "[]"),
    (`ZhangLS.Spec.RamifiedHeadHarmonicTau, `ZhangLS.Spec.ramified_tau_mul_le_real, 18264581411717334723, "[]")
  ]
  let mut keys : Array (Name × Name) := #[]
  for (name, _) in env.constants do
    if let some idx := env.getModuleIdxFor? name then
      let owner := modules[idx]!
      if owners.contains owner then
        if !keys.contains (owner,name) then keys := keys.push (owner,name)
  for idx in [:modules.size] do
    let owner := modules[idx]!
    if owners.contains owner then
      let data := env.header.moduleData[idx]!
      out.putStrLn s!"MODULE_DATA {owner} CONSTANTS {data.constNames.size} EXTRAS {data.extraConstNames.size}"
      for name in data.constNames ++ data.extraConstNames do
        if !keys.contains (owner,name) then keys := keys.push (owner,name)
  unless keys.size == 56 && expectedOwned.size == 56 && expectedPublic.size == 34 do
    throwError "Inventory cardinality drift: {keys.size}"
  for (owner,name) in keys do
    unless expectedOwned.any (fun p => p.1 == owner && p.2.1 == name) do
      throwError "Unexpected owner/name pair {owner} {name}"
  for p in expectedOwned do
    unless keys.contains (p.1,p.2.1) do
      throwError "Missing owner/name pair {p.1} {p.2.1}"
  let mut seen : Array (Name × Name) := #[]
  for (owner,name) in keys do
    let ci ← getConstInfo name
    if ci.isAxiom then throwError "Owned axiom {name}"
    let axs ← collectAxioms name
    unless axs.all (fun a => a == ``propext || a == ``Classical.choice || a == ``Quot.sound) do
      throwError "Nonstandard transitive axiom at {name}: {axs}"
    let typePretty ← liftTermElabM <| Meta.ppExpr ci.type
    let some pin := expectedOwned.find? (fun p => p.1 == owner && p.2.1 == name)
      | throwError "Missing owner/type pin {owner} {name}"
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
    seen := seen.push (owner,name)
  for pair in expectedPublic do
    unless seen.contains pair do throwError "Missing explicit declaration {pair.2}"
  for owner in owners do
    let actual := (seen.filter (fun p => p.1 == owner)).size
    out.putStrLn s!"OWNER_COUNT {owner} {actual}"
  out.putStrLn s!"OWNERSHIP_TYPE_AXIOM_EXACT_PASS {seen.size} PUBLIC {expectedPublic.size}"
  out.flush
