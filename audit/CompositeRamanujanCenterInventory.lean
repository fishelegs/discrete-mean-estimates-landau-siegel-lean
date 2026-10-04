import audit.CompositeRamanujanCenterRegression

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
    `ZhangLS.Spec.CompositeRamanujanCenterArithmetic,
    `ZhangLS.Spec.CompositeRamanujanCenterReduction,
    `ZhangLS.Spec.CompositeRamanujanCenterExpansion,
    `ZhangLS.Spec.CompositeRamanujanCenterPrimePowers,
    `audit.CompositeRamanujanCenterRegression
  ]
  -- BEGIN PINS
  let expectedOwned : Array (Name × Name) := #[
    (`ZhangLS.Spec.CompositeRamanujanCenterArithmetic, `ZhangLS.Spec.CompositeRamanujanCenter.additive_full_sum),
    (`ZhangLS.Spec.CompositeRamanujanCenterArithmetic, `ZhangLS.Spec.CompositeRamanujanCenter.additive_full_sum._simp_1_1),
    (`ZhangLS.Spec.CompositeRamanujanCenterArithmetic, `ZhangLS.Spec.CompositeRamanujanCenter.divisor_inner),
    (`ZhangLS.Spec.CompositeRamanujanCenterArithmetic, `ZhangLS.Spec.CompositeRamanujanCenter.divisor_inner._simp_1_1),
    (`ZhangLS.Spec.CompositeRamanujanCenterArithmetic, `ZhangLS.Spec.CompositeRamanujanCenter.divisor_inner._simp_1_2),
    (`ZhangLS.Spec.CompositeRamanujanCenterArithmetic, `ZhangLS.Spec.CompositeRamanujanCenter.divisor_inner._simp_1_3),
    (`ZhangLS.Spec.CompositeRamanujanCenterArithmetic, `ZhangLS.Spec.CompositeRamanujanCenter.divisor_inner._simp_1_4),
    (`ZhangLS.Spec.CompositeRamanujanCenterArithmetic, `ZhangLS.Spec.CompositeRamanujanCenter.divisor_inner._simp_1_5),
    (`ZhangLS.Spec.CompositeRamanujanCenterArithmetic, `ZhangLS.Spec.CompositeRamanujanCenter.divisor_inner._simp_1_6),
    (`ZhangLS.Spec.CompositeRamanujanCenterArithmetic, `ZhangLS.Spec.CompositeRamanujanCenter.divisor_inner._simp_1_7),
    (`ZhangLS.Spec.CompositeRamanujanCenterArithmetic, `ZhangLS.Spec.CompositeRamanujanCenter.ramanujanSum),
    (`ZhangLS.Spec.CompositeRamanujanCenterArithmetic, `ZhangLS.Spec.CompositeRamanujanCenter.ramanujanSum.eq_1),
    (`ZhangLS.Spec.CompositeRamanujanCenterArithmetic, `ZhangLS.Spec.CompositeRamanujanCenter.ramanujanSum_divisor_formula),
    (`ZhangLS.Spec.CompositeRamanujanCenterArithmetic, `ZhangLS.Spec.CompositeRamanujanCenter.ramanujanSum_divisor_formula._simp_1_1),
    (`ZhangLS.Spec.CompositeRamanujanCenterArithmetic, `ZhangLS.Spec.CompositeRamanujanCenter.ramanujanSum_divisor_formula._simp_1_2),
    (`ZhangLS.Spec.CompositeRamanujanCenterArithmetic, `ZhangLS.Spec.CompositeRamanujanCenter.ramanujanSum_one),
    (`ZhangLS.Spec.CompositeRamanujanCenterArithmetic, `ZhangLS.Spec.CompositeRamanujanCenter.ramanujanSum_range),
    (`ZhangLS.Spec.CompositeRamanujanCenterArithmetic, `ZhangLS.Spec.CompositeRamanujanCenter.ramanujanSum_range._simp_1_1),
    (`ZhangLS.Spec.CompositeRamanujanCenterArithmetic, `ZhangLS.Spec.CompositeRamanujanCenter.ramanujanSum_residues),
    (`ZhangLS.Spec.CompositeRamanujanCenterArithmetic, `ZhangLS.Spec.CompositeRamanujanCenter.ramanujanSum_unit),
    (`ZhangLS.Spec.CompositeRamanujanCenterArithmetic, `ZhangLS.Spec.CompositeRamanujanCenter.ramanujanSum_zero),
    (`ZhangLS.Spec.CompositeRamanujanCenterExpansion, `ZhangLS.Spec.CompositeRamanujanCenter.centered_character_expansion),
    (`ZhangLS.Spec.CompositeRamanujanCenterExpansion, `ZhangLS.Spec.CompositeRamanujanCenter.divisible_centered_zero),
    (`ZhangLS.Spec.CompositeRamanujanCenterExpansion, `ZhangLS.Spec.CompositeRamanujanCenter.gcd_centered_identity),
    (`ZhangLS.Spec.CompositeRamanujanCenterExpansion, `ZhangLS.Spec.CompositeRamanujanCenter.gcd_nonprincipal_expansion),
    (`ZhangLS.Spec.CompositeRamanujanCenterExpansion, `ZhangLS.Spec.CompositeRamanujanCenter.inverse_character_is_conjugate),
    (`ZhangLS.Spec.CompositeRamanujanCenterExpansion, `ZhangLS.Spec.CompositeRamanujanCenter.level_one_centered),
    (`ZhangLS.Spec.CompositeRamanujanCenterExpansion, `ZhangLS.Spec.CompositeRamanujanCenter.level_one_characters),
    (`ZhangLS.Spec.CompositeRamanujanCenterExpansion, `ZhangLS.Spec.CompositeRamanujanCenter.level_one_expansion),
    (`ZhangLS.Spec.CompositeRamanujanCenterExpansion, `ZhangLS.Spec.CompositeRamanujanCenter.level_one_phase),
    (`ZhangLS.Spec.CompositeRamanujanCenterExpansion, `ZhangLS.Spec.CompositeRamanujanCenter.nonprincipalCharacters),
    (`ZhangLS.Spec.CompositeRamanujanCenterExpansion, `ZhangLS.Spec.CompositeRamanujanCenter.nonprincipalCharacters._proof_1),
    (`ZhangLS.Spec.CompositeRamanujanCenterExpansion, `ZhangLS.Spec.CompositeRamanujanCenter.nonprincipalCharacters.congr_simp),
    (`ZhangLS.Spec.CompositeRamanujanCenterExpansion, `ZhangLS.Spec.CompositeRamanujanCenter.nonprincipalCharacters.eq_1),
    (`ZhangLS.Spec.CompositeRamanujanCenterExpansion, `ZhangLS.Spec.CompositeRamanujanCenter.nonprincipalCharacters_eq_conductor_filter),
    (`ZhangLS.Spec.CompositeRamanujanCenterExpansion, `ZhangLS.Spec.CompositeRamanujanCenter.nonprincipalCharacters_eq_conductor_filter._simp_1_2),
    (`ZhangLS.Spec.CompositeRamanujanCenterExpansion, `ZhangLS.Spec.CompositeRamanujanCenter.nonprincipalCharacters_eq_conductor_filter._simp_1_3),
    (`ZhangLS.Spec.CompositeRamanujanCenterExpansion, `ZhangLS.Spec.CompositeRamanujanCenter.nonprincipalExpansion),
    (`ZhangLS.Spec.CompositeRamanujanCenterExpansion, `ZhangLS.Spec.CompositeRamanujanCenter.nonprincipalExpansion.eq_1),
    (`ZhangLS.Spec.CompositeRamanujanCenterExpansion, `ZhangLS.Spec.CompositeRamanujanCenter.nonprincipalExpansion_conductor_sum),
    (`ZhangLS.Spec.CompositeRamanujanCenterExpansion, `ZhangLS.Spec.CompositeRamanujanCenter.nonprincipal_conductor_gt_one),
    (`ZhangLS.Spec.CompositeRamanujanCenterExpansion, `ZhangLS.Spec.CompositeRamanujanCenter.positive_character_expansion),
    (`ZhangLS.Spec.CompositeRamanujanCenterExpansion, `ZhangLS.Spec.CompositeRamanujanCenter.positive_character_expansion._simp_1_1),
    (`ZhangLS.Spec.CompositeRamanujanCenterExpansion, `ZhangLS.Spec.CompositeRamanujanCenter.principal_partition),
    (`ZhangLS.Spec.CompositeRamanujanCenterExpansion, `ZhangLS.Spec.CompositeRamanujanCenter.quotient_one_centered_zero),
    (`ZhangLS.Spec.CompositeRamanujanCenterExpansion, `ZhangLS.Spec.CompositeRamanujanCenter.reciprocalPhase),
    (`ZhangLS.Spec.CompositeRamanujanCenterExpansion, `ZhangLS.Spec.CompositeRamanujanCenter.reciprocalPhase.congr_simp),
    (`ZhangLS.Spec.CompositeRamanujanCenterExpansion, `ZhangLS.Spec.CompositeRamanujanCenter.reciprocalPhase.eq_1),
    (`ZhangLS.Spec.CompositeRamanujanCenterExpansion, `ZhangLS.Spec.CompositeRamanujanCenter.scaled_reciprocal_phase),
    (`ZhangLS.Spec.CompositeRamanujanCenterPrimePowers, `ZhangLS.Spec.CompositeRamanujanCenter.prime_power_coprime_zero),
    (`ZhangLS.Spec.CompositeRamanujanCenterPrimePowers, `ZhangLS.Spec.CompositeRamanujanCenter.prime_power_coprime_zero._proof_1_1),
    (`ZhangLS.Spec.CompositeRamanujanCenterPrimePowers, `ZhangLS.Spec.CompositeRamanujanCenter.prime_power_coprime_zero._proof_1_2),
    (`ZhangLS.Spec.CompositeRamanujanCenterPrimePowers, `ZhangLS.Spec.CompositeRamanujanCenter.prime_power_middle),
    (`ZhangLS.Spec.CompositeRamanujanCenterPrimePowers, `ZhangLS.Spec.CompositeRamanujanCenter.ramanujanSum_divisible),
    (`ZhangLS.Spec.CompositeRamanujanCenterReduction, `ZhangLS.Spec.CompositeRamanujanCenter.average_surjective),
    (`ZhangLS.Spec.CompositeRamanujanCenterReduction, `ZhangLS.Spec.CompositeRamanujanCenter.normalized_gcd),
    (`ZhangLS.Spec.CompositeRamanujanCenterReduction, `ZhangLS.Spec.CompositeRamanujanCenter.ramanujanSum.congr_simp),
    (`ZhangLS.Spec.CompositeRamanujanCenterReduction, `ZhangLS.Spec.CompositeRamanujanCenter.ramanujanSum_coprime),
    (`ZhangLS.Spec.CompositeRamanujanCenterReduction, `ZhangLS.Spec.CompositeRamanujanCenter.scaled_normalized_sum),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenter.nonprincipalExpansion.congr_simp),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenterRegression.actual_inverse_residue),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenterRegression.composite_centered_expansion),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenterRegression.composite_gcd_middle),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenterRegression.composite_gcd_three),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenterRegression.composite_squarefree_quotient),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenterRegression.divisor_formula_composite),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenterRegression.imprimitive_member),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenterRegression.imprimitive_member._simp_1_1),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenterRegression.imprimitive_member._simp_1_2),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenterRegression.imprimitive_member_conductor),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenterRegression.level_nine_no_conductor_one),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenterRegression.level_one_empty),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenterRegression.level_one_zero),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenterRegression.modulus_one_seven),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenterRegression.modulus_one_zero),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenterRegression.numerator_zero_centered),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenterRegression.original_inverse_descends),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenterRegression.positive_phase_differs_from_negative),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenterRegression.prime_power_coprime),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenterRegression.prime_power_divisible),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenterRegression.prime_power_middle_three),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenterRegression.prime_power_middle_two),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenterRegression.quotient_one_zero),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenterRegression.totient_eight),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenterRegression.totient_six),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenterRegression.totient_three),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenterRegression.totient_twelve),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenterRegression.totient_two),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenterRegression.zero_composite)
  ]
  let expectedTypes : Array (Name × UInt64 × String) := #[
    (`ZhangLS.Spec.CompositeRamanujanCenter.additive_full_sum, 3246200138043126019, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.additive_full_sum._simp_1_1, 4968480684667976741, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.divisor_inner, 2780786066586477690, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.divisor_inner._simp_1_1, 6033590925971773593, "[`u_2]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.divisor_inner._simp_1_2, 13972439555833037651, "[`u_2]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.divisor_inner._simp_1_3, 16412815542536123252, "[`u_2]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.divisor_inner._simp_1_4, 2173808416608830180, "[`u_1]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.divisor_inner._simp_1_5, 7579211897750796183, "[`u_1]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.divisor_inner._simp_1_6, 5885927816594865294, "[`u_3]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.divisor_inner._simp_1_7, 9303903170692057158, "[`u_1]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.ramanujanSum, 11926552585477799947, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.ramanujanSum.eq_1, 15432445765902292697, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.ramanujanSum_divisor_formula, 1524653010285342997, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.ramanujanSum_divisor_formula._simp_1_1, 7944629515112915904, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.ramanujanSum_divisor_formula._simp_1_2, 7073196793349487485, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.ramanujanSum_one, 1758984689265448964, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.ramanujanSum_range, 11481373384263334171, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.ramanujanSum_range._simp_1_1, 14099781613356095600, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.ramanujanSum_residues, 9844064609688932365, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.ramanujanSum_unit, 7052453024148375871, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.ramanujanSum_zero, 12124036704851450344, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.centered_character_expansion, 6725791605660088734, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.divisible_centered_zero, 5969425138440787795, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.gcd_centered_identity, 14062131770343639393, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.gcd_nonprincipal_expansion, 11167712329031683621, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.inverse_character_is_conjugate, 703603746123159525, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.level_one_centered, 16006728137329509545, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.level_one_characters, 1228860768518350582, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.level_one_expansion, 9016429420950872769, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.level_one_phase, 6468827583347125163, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.nonprincipalCharacters, 10018238634630973477, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.nonprincipalCharacters._proof_1, 1388598209486740759, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.nonprincipalCharacters.congr_simp, 11986622846733457551, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.nonprincipalCharacters.eq_1, 10382739473691490997, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.nonprincipalCharacters_eq_conductor_filter, 627176316522639039, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.nonprincipalCharacters_eq_conductor_filter._simp_1_2, 1988649516832762782, "[`u_1]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.nonprincipalCharacters_eq_conductor_filter._simp_1_3, 5581755817566308493, "[`u_1]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.nonprincipalExpansion, 4883092189590113328, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.nonprincipalExpansion.eq_1, 2086560674368070167, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.nonprincipalExpansion_conductor_sum, 1725261372256340269, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.nonprincipal_conductor_gt_one, 1715786170810059939, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.positive_character_expansion, 8797255574662533851, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.positive_character_expansion._simp_1_1, 10944153567445236411, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.principal_partition, 11036976257371661483, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.quotient_one_centered_zero, 741047766570337344, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.reciprocalPhase, 10094483094304018850, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.reciprocalPhase.congr_simp, 13202303326384637744, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.reciprocalPhase.eq_1, 5785933935813463892, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.scaled_reciprocal_phase, 1545260201408879054, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.prime_power_coprime_zero, 10723402007307067176, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.prime_power_coprime_zero._proof_1_1, 14680093999044704001, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.prime_power_coprime_zero._proof_1_2, 2950093057530431349, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.prime_power_middle, 15398410458950980850, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.ramanujanSum_divisible, 7607677189345367476, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.average_surjective, 12412464409998970928, "[`u_1, `u_2]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.normalized_gcd, 2356918301523196039, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.ramanujanSum.congr_simp, 1721319736575109425, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.ramanujanSum_coprime, 8534736212972833773, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.scaled_normalized_sum, 12339832341035889668, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenter.nonprincipalExpansion.congr_simp, 2955587864652151162, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenterRegression.actual_inverse_residue, 1525740137436396126, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenterRegression.composite_centered_expansion, 7335561712879548960, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenterRegression.composite_gcd_middle, 11813250299883312634, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenterRegression.composite_gcd_three, 9177963296948309675, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenterRegression.composite_squarefree_quotient, 14155113965453645033, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenterRegression.divisor_formula_composite, 3879947785521785394, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenterRegression.imprimitive_member, 6575674061687972367, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenterRegression.imprimitive_member._simp_1_1, 1988649516832762782, "[`u_1]"),
    (`ZhangLS.Spec.CompositeRamanujanCenterRegression.imprimitive_member._simp_1_2, 5581755817566308493, "[`u_1]"),
    (`ZhangLS.Spec.CompositeRamanujanCenterRegression.imprimitive_member_conductor, 14280544693009053578, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenterRegression.level_nine_no_conductor_one, 15133855273721536955, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenterRegression.level_one_empty, 1228860768518350582, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenterRegression.level_one_zero, 6239085864267570213, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenterRegression.modulus_one_seven, 1694299531341130308, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenterRegression.modulus_one_zero, 17902091536235907697, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenterRegression.numerator_zero_centered, 16519506747204785926, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenterRegression.original_inverse_descends, 7331253607063912217, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenterRegression.positive_phase_differs_from_negative, 16419227662555148722, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenterRegression.prime_power_coprime, 13345366201795610343, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenterRegression.prime_power_divisible, 15011341646004713121, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenterRegression.prime_power_middle_three, 18180871135960456633, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenterRegression.prime_power_middle_two, 5791233547972531461, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenterRegression.quotient_one_zero, 5119615587829816073, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenterRegression.totient_eight, 2379541597529760174, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenterRegression.totient_six, 14997762204680513483, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenterRegression.totient_three, 4923969098164764219, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenterRegression.totient_twelve, 12858941461980702798, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenterRegression.totient_two, 1726508619362687562, "[]"),
    (`ZhangLS.Spec.CompositeRamanujanCenterRegression.zero_composite, 18086157608510635453, "[]")
  ]
  let expectedPublic : Array (Name × Name) := #[
    (`ZhangLS.Spec.CompositeRamanujanCenterArithmetic, `ZhangLS.Spec.CompositeRamanujanCenter.additive_full_sum),
    (`ZhangLS.Spec.CompositeRamanujanCenterArithmetic, `ZhangLS.Spec.CompositeRamanujanCenter.divisor_inner),
    (`ZhangLS.Spec.CompositeRamanujanCenterArithmetic, `ZhangLS.Spec.CompositeRamanujanCenter.ramanujanSum),
    (`ZhangLS.Spec.CompositeRamanujanCenterArithmetic, `ZhangLS.Spec.CompositeRamanujanCenter.ramanujanSum_divisor_formula),
    (`ZhangLS.Spec.CompositeRamanujanCenterArithmetic, `ZhangLS.Spec.CompositeRamanujanCenter.ramanujanSum_one),
    (`ZhangLS.Spec.CompositeRamanujanCenterArithmetic, `ZhangLS.Spec.CompositeRamanujanCenter.ramanujanSum_range),
    (`ZhangLS.Spec.CompositeRamanujanCenterArithmetic, `ZhangLS.Spec.CompositeRamanujanCenter.ramanujanSum_residues),
    (`ZhangLS.Spec.CompositeRamanujanCenterArithmetic, `ZhangLS.Spec.CompositeRamanujanCenter.ramanujanSum_unit),
    (`ZhangLS.Spec.CompositeRamanujanCenterArithmetic, `ZhangLS.Spec.CompositeRamanujanCenter.ramanujanSum_zero),
    (`ZhangLS.Spec.CompositeRamanujanCenterExpansion, `ZhangLS.Spec.CompositeRamanujanCenter.centered_character_expansion),
    (`ZhangLS.Spec.CompositeRamanujanCenterExpansion, `ZhangLS.Spec.CompositeRamanujanCenter.divisible_centered_zero),
    (`ZhangLS.Spec.CompositeRamanujanCenterExpansion, `ZhangLS.Spec.CompositeRamanujanCenter.gcd_centered_identity),
    (`ZhangLS.Spec.CompositeRamanujanCenterExpansion, `ZhangLS.Spec.CompositeRamanujanCenter.gcd_nonprincipal_expansion),
    (`ZhangLS.Spec.CompositeRamanujanCenterExpansion, `ZhangLS.Spec.CompositeRamanujanCenter.inverse_character_is_conjugate),
    (`ZhangLS.Spec.CompositeRamanujanCenterExpansion, `ZhangLS.Spec.CompositeRamanujanCenter.level_one_centered),
    (`ZhangLS.Spec.CompositeRamanujanCenterExpansion, `ZhangLS.Spec.CompositeRamanujanCenter.level_one_characters),
    (`ZhangLS.Spec.CompositeRamanujanCenterExpansion, `ZhangLS.Spec.CompositeRamanujanCenter.level_one_expansion),
    (`ZhangLS.Spec.CompositeRamanujanCenterExpansion, `ZhangLS.Spec.CompositeRamanujanCenter.level_one_phase),
    (`ZhangLS.Spec.CompositeRamanujanCenterExpansion, `ZhangLS.Spec.CompositeRamanujanCenter.nonprincipalCharacters),
    (`ZhangLS.Spec.CompositeRamanujanCenterExpansion, `ZhangLS.Spec.CompositeRamanujanCenter.nonprincipalCharacters_eq_conductor_filter),
    (`ZhangLS.Spec.CompositeRamanujanCenterExpansion, `ZhangLS.Spec.CompositeRamanujanCenter.nonprincipalExpansion),
    (`ZhangLS.Spec.CompositeRamanujanCenterExpansion, `ZhangLS.Spec.CompositeRamanujanCenter.nonprincipalExpansion_conductor_sum),
    (`ZhangLS.Spec.CompositeRamanujanCenterExpansion, `ZhangLS.Spec.CompositeRamanujanCenter.nonprincipal_conductor_gt_one),
    (`ZhangLS.Spec.CompositeRamanujanCenterExpansion, `ZhangLS.Spec.CompositeRamanujanCenter.positive_character_expansion),
    (`ZhangLS.Spec.CompositeRamanujanCenterExpansion, `ZhangLS.Spec.CompositeRamanujanCenter.principal_partition),
    (`ZhangLS.Spec.CompositeRamanujanCenterExpansion, `ZhangLS.Spec.CompositeRamanujanCenter.quotient_one_centered_zero),
    (`ZhangLS.Spec.CompositeRamanujanCenterExpansion, `ZhangLS.Spec.CompositeRamanujanCenter.reciprocalPhase),
    (`ZhangLS.Spec.CompositeRamanujanCenterExpansion, `ZhangLS.Spec.CompositeRamanujanCenter.scaled_reciprocal_phase),
    (`ZhangLS.Spec.CompositeRamanujanCenterPrimePowers, `ZhangLS.Spec.CompositeRamanujanCenter.prime_power_coprime_zero),
    (`ZhangLS.Spec.CompositeRamanujanCenterPrimePowers, `ZhangLS.Spec.CompositeRamanujanCenter.prime_power_middle),
    (`ZhangLS.Spec.CompositeRamanujanCenterPrimePowers, `ZhangLS.Spec.CompositeRamanujanCenter.ramanujanSum_divisible),
    (`ZhangLS.Spec.CompositeRamanujanCenterReduction, `ZhangLS.Spec.CompositeRamanujanCenter.average_surjective),
    (`ZhangLS.Spec.CompositeRamanujanCenterReduction, `ZhangLS.Spec.CompositeRamanujanCenter.normalized_gcd),
    (`ZhangLS.Spec.CompositeRamanujanCenterReduction, `ZhangLS.Spec.CompositeRamanujanCenter.ramanujanSum_coprime),
    (`ZhangLS.Spec.CompositeRamanujanCenterReduction, `ZhangLS.Spec.CompositeRamanujanCenter.scaled_normalized_sum),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenterRegression.actual_inverse_residue),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenterRegression.composite_centered_expansion),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenterRegression.composite_gcd_middle),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenterRegression.composite_gcd_three),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenterRegression.composite_squarefree_quotient),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenterRegression.divisor_formula_composite),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenterRegression.imprimitive_member),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenterRegression.imprimitive_member_conductor),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenterRegression.level_nine_no_conductor_one),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenterRegression.level_one_empty),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenterRegression.level_one_zero),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenterRegression.modulus_one_seven),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenterRegression.modulus_one_zero),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenterRegression.numerator_zero_centered),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenterRegression.original_inverse_descends),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenterRegression.positive_phase_differs_from_negative),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenterRegression.prime_power_coprime),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenterRegression.prime_power_divisible),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenterRegression.prime_power_middle_three),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenterRegression.prime_power_middle_two),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenterRegression.quotient_one_zero),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenterRegression.totient_eight),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenterRegression.totient_six),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenterRegression.totient_three),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenterRegression.totient_twelve),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenterRegression.totient_two),
    (`audit.CompositeRamanujanCenterRegression, `ZhangLS.Spec.CompositeRamanujanCenterRegression.zero_composite)
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
