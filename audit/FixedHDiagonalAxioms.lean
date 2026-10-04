import ZhangLS.Spec.FixedHDiagonal
set_option autoImplicit false
set_option maxHeartbeats 24000000
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let owners : Array Name := #[`ZhangLS.Spec.FixedHDiagonalIBP,
    `ZhangLS.Spec.FixedHDiagonalAlgebra, `ZhangLS.Spec.FixedHDiagonal]
  let expected : Array (Name × Name) := #[
    (`ZhangLS.Spec.FixedHDiagonalIBP, `ZhangLS.Spec.FixedHDiagonal.tail),
    (`ZhangLS.Spec.FixedHDiagonalIBP, `ZhangLS.Spec.FixedHDiagonal.tail_hasDerivAt),
    (`ZhangLS.Spec.FixedHDiagonalIBP, `ZhangLS.Spec.FixedHDiagonal.tail_continuous),
    (`ZhangLS.Spec.FixedHDiagonalIBP, `ZhangLS.Spec.FixedHDiagonal.integral_deriv_tail),
    (`ZhangLS.Spec.FixedHDiagonalIBP, `ZhangLS.Spec.FixedHDiagonal.integral_deriv_tail_c2),
    (`ZhangLS.Spec.FixedHDiagonalAlgebra, `ZhangLS.Spec.FixedHDiagonal.scaledShift),
    (`ZhangLS.Spec.FixedHDiagonalAlgebra, `ZhangLS.Spec.FixedHDiagonal.firstKernel),
    (`ZhangLS.Spec.FixedHDiagonalAlgebra, `ZhangLS.Spec.FixedHDiagonal.secondKernel),
    (`ZhangLS.Spec.FixedHDiagonalAlgebra, `ZhangLS.Spec.FixedHDiagonal.pure_imaginary_product),
    (`ZhangLS.Spec.FixedHDiagonalAlgebra, `ZhangLS.Spec.FixedHDiagonal.cyclic_coefficient),
    (`ZhangLS.Spec.FixedHDiagonalAlgebra, `ZhangLS.Spec.FixedHDiagonal.scaled_diagonal),
    (`ZhangLS.Spec.FixedHDiagonal, `ZhangLS.Spec.FixedHDiagonal.B),
    (`ZhangLS.Spec.FixedHDiagonal, `ZhangLS.Spec.FixedHDiagonal.delta),
    (`ZhangLS.Spec.FixedHDiagonal, `ZhangLS.Spec.FixedHDiagonal.B_pos),
    (`ZhangLS.Spec.FixedHDiagonal, `ZhangLS.Spec.FixedHDiagonal.B_mul_alpha),
    (`ZhangLS.Spec.FixedHDiagonal, `ZhangLS.Spec.FixedHDiagonal.delta_eq),
    (`ZhangLS.Spec.FixedHDiagonal, `ZhangLS.Spec.FixedHDiagonal.paper_scaled_shift),
    (`ZhangLS.Spec.FixedHDiagonal, `ZhangLS.Spec.FixedHDiagonal.F),
    (`ZhangLS.Spec.FixedHDiagonal, `ZhangLS.Spec.FixedHDiagonal.G),
    (`ZhangLS.Spec.FixedHDiagonal, `ZhangLS.Spec.FixedHDiagonal.paper_diagonal),
    (`ZhangLS.Spec.FixedHDiagonal, `ZhangLS.Spec.FixedHDiagonal.paper_diagonal_c2)]
  for (owner, name) in expected do
    unless env.contains name do throwError "Missing public declaration {name}"
    let some idx := env.getModuleIdxFor? name | throwError "Missing owner {name}"
    unless moduleNames[idx]! == owner do throwError "Owner mismatch {name}"
  for (name, owner) in #[(`ZhangLS.Spec.lemma83PaperBeta, `ZhangLS.Spec.Lemma83Definitions),
      (`ZhangLS.Spec.lemma44PaperAlpha, `ZhangLS.Spec.Lemma44LongSum),
      (`ZhangLS.Spec.lemma23PaperP, `ZhangLS.Spec.Lemma23GoodSet)] do
    let some idx := env.getModuleIdxFor? name | throwError "Missing published definition {name}"
    unless moduleNames[idx]! == owner do throwError "Published definition owner drift {name}"
    logInfo m!"PUBLISHED_OWNER {name} {owner}"
  let expectedOwned : Array (Name × Name) := #[
    (`ZhangLS.Spec.FixedHDiagonal, `ZhangLS.Spec.FixedHDiagonal.B),
    (`ZhangLS.Spec.FixedHDiagonal, `ZhangLS.Spec.FixedHDiagonal.B.eq_1),
    (`ZhangLS.Spec.FixedHDiagonal, `ZhangLS.Spec.FixedHDiagonal.B_mul_alpha),
    (`ZhangLS.Spec.FixedHDiagonal, `ZhangLS.Spec.FixedHDiagonal.B_pos),
    (`ZhangLS.Spec.FixedHDiagonal, `ZhangLS.Spec.FixedHDiagonal.B_pos._proof_1_1),
    (`ZhangLS.Spec.FixedHDiagonal, `ZhangLS.Spec.FixedHDiagonal.F),
    (`ZhangLS.Spec.FixedHDiagonal, `ZhangLS.Spec.FixedHDiagonal.F.eq_1),
    (`ZhangLS.Spec.FixedHDiagonal, `ZhangLS.Spec.FixedHDiagonal.G),
    (`ZhangLS.Spec.FixedHDiagonal, `ZhangLS.Spec.FixedHDiagonal.G._proof_1),
    (`ZhangLS.Spec.FixedHDiagonal, `ZhangLS.Spec.FixedHDiagonal.G.eq_1),
    (`ZhangLS.Spec.FixedHDiagonal, `ZhangLS.Spec.FixedHDiagonal.delta),
    (`ZhangLS.Spec.FixedHDiagonal, `ZhangLS.Spec.FixedHDiagonal.delta.eq_1),
    (`ZhangLS.Spec.FixedHDiagonal, `ZhangLS.Spec.FixedHDiagonal.delta_eq),
    (`ZhangLS.Spec.FixedHDiagonal, `ZhangLS.Spec.FixedHDiagonal.delta_eq._proof_1_1),
    (`ZhangLS.Spec.FixedHDiagonal, `ZhangLS.Spec.FixedHDiagonal.delta_eq._simp_1_3),
    (`ZhangLS.Spec.FixedHDiagonal, `ZhangLS.Spec.FixedHDiagonal.delta_eq._simp_1_4),
    (`ZhangLS.Spec.FixedHDiagonal, `ZhangLS.Spec.FixedHDiagonal.delta_eq._simp_1_5),
    (`ZhangLS.Spec.FixedHDiagonal, `ZhangLS.Spec.FixedHDiagonal.delta_eq._simp_1_6),
    (`ZhangLS.Spec.FixedHDiagonal, `ZhangLS.Spec.FixedHDiagonal.delta_eq._simp_1_7),
    (`ZhangLS.Spec.FixedHDiagonal, `ZhangLS.Spec.FixedHDiagonal.delta_eq._simp_1_8),
    (`ZhangLS.Spec.FixedHDiagonal, `ZhangLS.Spec.FixedHDiagonal.delta_eq._simp_1_9),
    (`ZhangLS.Spec.FixedHDiagonal, `ZhangLS.Spec.FixedHDiagonal.paper_diagonal),
    (`ZhangLS.Spec.FixedHDiagonal, `ZhangLS.Spec.FixedHDiagonal.paper_diagonal_c2),
    (`ZhangLS.Spec.FixedHDiagonal, `ZhangLS.Spec.FixedHDiagonal.paper_scaled_shift),
    (`ZhangLS.Spec.FixedHDiagonal, `ZhangLS.Spec.FixedHDiagonal.paper_scaled_shift._simp_1_2),
    (`ZhangLS.Spec.FixedHDiagonal, `ZhangLS.Spec.lemma83PaperBeta.eq_1),
    (`ZhangLS.Spec.FixedHDiagonalAlgebra, `ZhangLS.Spec.FixedHDiagonal.cyclic_coefficient),
    (`ZhangLS.Spec.FixedHDiagonalAlgebra, `ZhangLS.Spec.FixedHDiagonal.cyclic_coefficient._simp_1_1),
    (`ZhangLS.Spec.FixedHDiagonalAlgebra, `ZhangLS.Spec.FixedHDiagonal.firstKernel),
    (`ZhangLS.Spec.FixedHDiagonalAlgebra, `ZhangLS.Spec.FixedHDiagonal.firstKernel.eq_1),
    (`ZhangLS.Spec.FixedHDiagonalAlgebra, `ZhangLS.Spec.FixedHDiagonal.pure_imaginary_product),
    (`ZhangLS.Spec.FixedHDiagonalAlgebra, `ZhangLS.Spec.FixedHDiagonal.scaledShift),
    (`ZhangLS.Spec.FixedHDiagonalAlgebra, `ZhangLS.Spec.FixedHDiagonal.scaledShift._proof_1),
    (`ZhangLS.Spec.FixedHDiagonalAlgebra, `ZhangLS.Spec.FixedHDiagonal.scaledShift._proof_2),
    (`ZhangLS.Spec.FixedHDiagonalAlgebra, `ZhangLS.Spec.FixedHDiagonal.scaledShift._proof_3),
    (`ZhangLS.Spec.FixedHDiagonalAlgebra, `ZhangLS.Spec.FixedHDiagonal.scaledShift._proof_4),
    (`ZhangLS.Spec.FixedHDiagonalAlgebra, `ZhangLS.Spec.FixedHDiagonal.scaledShift.eq_1),
    (`ZhangLS.Spec.FixedHDiagonalAlgebra, `ZhangLS.Spec.FixedHDiagonal.scaled_diagonal),
    (`ZhangLS.Spec.FixedHDiagonalAlgebra, `ZhangLS.Spec.FixedHDiagonal.secondKernel),
    (`ZhangLS.Spec.FixedHDiagonalAlgebra, `ZhangLS.Spec.FixedHDiagonal.secondKernel.eq_1),
    (`ZhangLS.Spec.FixedHDiagonalIBP, `ZhangLS.Spec.FixedHDiagonal.integral_deriv_tail),
    (`ZhangLS.Spec.FixedHDiagonalIBP, `ZhangLS.Spec.FixedHDiagonal.integral_deriv_tail._simp_1_1),
    (`ZhangLS.Spec.FixedHDiagonalIBP, `ZhangLS.Spec.FixedHDiagonal.integral_deriv_tail_c2),
    (`ZhangLS.Spec.FixedHDiagonalIBP, `ZhangLS.Spec.FixedHDiagonal.tail),
    (`ZhangLS.Spec.FixedHDiagonalIBP, `ZhangLS.Spec.FixedHDiagonal.tail.eq_1),
    (`ZhangLS.Spec.FixedHDiagonalIBP, `ZhangLS.Spec.FixedHDiagonal.tail_continuous),
    (`ZhangLS.Spec.FixedHDiagonalIBP, `ZhangLS.Spec.FixedHDiagonal.tail_hasDerivAt)]
  let mut count := 0
  for (name, ci) in env.constants do
    if let some idx := env.getModuleIdxFor? name then
      let owner := moduleNames[idx]!
      if owners.contains owner then
        unless expectedOwned.contains (owner, name) do
          throwError "Unexpected owned declaration {owner} {name}"
        if ci.isAxiom then throwError "New owned axiom {name}"
        let axs ← collectAxioms name
        unless axs.all (fun a => a == ``propext || a == ``Classical.choice || a == ``Quot.sound) do
          throwError "Nonstandard axiom at {name}: {axs}"
        logInfo m!"OWNER {owner} DECL {name} AXIOMS {axs}"
        for dep in ci.getUsedConstantsAsSet do
          logInfo m!"DECL_REF {name} {dep}"
        count := count + 1
  unless count == expectedOwned.size && count == 47 do
    throwError "Exact owned declaration count drift {count}"
  for mod in moduleNames do
    logInfo m!"LOADED_MODULE {mod}"
    if mod.toString.startsWith "ZhangLS.Spec.FixedHProfile" then
      throwError "Unpublished profile dependency {mod}"
  logInfo m!"OWNERSHIP_PASS {count} PUBLIC {expected.size}"

#print axioms ZhangLS.Spec.FixedHDiagonal.integral_deriv_tail
#print axioms ZhangLS.Spec.FixedHDiagonal.paper_scaled_shift
#print axioms ZhangLS.Spec.FixedHDiagonal.paper_diagonal
#print axioms ZhangLS.Spec.FixedHDiagonal.paper_diagonal_c2

set_option pp.all true in
#check @ZhangLS.Spec.FixedHDiagonal.integral_deriv_tail
set_option pp.all true in
#check @ZhangLS.Spec.FixedHDiagonal.paper_diagonal_c2
