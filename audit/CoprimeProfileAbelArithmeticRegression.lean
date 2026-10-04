import ZhangLS.Spec.CoprimeProfileAbelBound
namespace ZhangLS.Spec.CoprimeProfileAbel
example : summatory 1 1 = 1 := summatory_one 1
example : summatory 2 1 = 1 := summatory_one 2
example : coefficient 2 2 = 0 := by norm_num [coefficient]
example : coefficient 1 2 = 1 / 2 := by norm_num [coefficient, Nat.totient]; decide
example : unitCount 2 4 = 2 := by norm_num [unitCount, Finset.sum_Ioc_succ_top]; norm_cast
example : summatory 2 2 = 1 := by norm_num [summatory, coefficient, Finset.sum_Icc_succ_top]
example : |summatory 1 (1 : ℝ) - mainConstant 1| ≤
    ((1 : ℕ).divisors.card : ℝ) * (1 + Real.log 1) + 2 := by
  simpa using summatory_error (D := 1) (x := 1) (by decide) le_rfl
example : |summatory 2 (3 / 2 : ℝ) - mainConstant 2 * (3 / 2)| ≤
    (((2 : ℕ).divisors.card : ℝ) + 1) * (1 + Real.log (3 / 2)) + 2 :=
  requested_summatory_error (by decide) (by norm_num)
end ZhangLS.Spec.CoprimeProfileAbel
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := env.constants.toList.map Prod.fst
  let names := names.filter fun n => n.toString.startsWith "ZhangLS.Spec.CoprimeProfileAbel." ||
    n.toString.contains "CoprimeProfileAbel"
  for n in names do
    let axioms ← collectAxioms n
    for ax in axioms do
      unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
        throwError "Nonstandard axiom {ax} in {n}"
    logInfo m!"OWNED {n}"
    elabCommand (← `(command| #print axioms $(mkIdent n)))
