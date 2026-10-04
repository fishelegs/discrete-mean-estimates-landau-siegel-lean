import ZhangLS.Spec.FixedHLambdaReplacement
set_option autoImplicit false
namespace ZhangLS.Spec.FixedHLambdaReplacement
open Finset Complex
open scoped Classical

lemma regression_one (β : Fin 3 → ℂ) (j : Fin 3) :
    lemma83Lambda β 1 (1-β j) / (((Nat.totient 1:ℝ)/(1:ℝ))^2 : ℂ)-1=0 := by
  simp [lemma83Lambda]

lemma regression_prime_two : 0<1-(2:ℝ)⁻¹ ∧ 1/4≤(1-(2:ℝ)⁻¹)^2 := prime_baseline_pos Nat.prime_two

lemma regression_two_factor (β : Fin 3 → ℂ) (j : Fin 3) :
    normalizedFactor β j 2=4*lemma83LambdaFactor β 2 (1-β j) := by
  norm_num [normalizedFactor]; ring

lemma regression_three_shifts (β : Fin 3 → ℂ) :
    lemma83Lambda β 1 (1-β 0)=1 ∧ lemma83Lambda β 1 (1-β 1)=1 ∧
    lemma83Lambda β 1 (1-β 2)=1 := by simp [lemma83Lambda]

lemma regression_exact_product (β : Fin 3 → ℂ) (j : Fin 3) {n : ℕ} (hn : 0<n) :
    lemma83Lambda β n (1-β j) / (((Nat.totient n:ℝ)/(n:ℝ))^2 : ℂ)=
      ∏ p ∈ n.primeFactors, normalizedFactor β j p := normalized_product β j hn

lemma regression_window : (201/400:ℝ)<1 := by norm_num

lemma regression_uniform_actual (c : ℝ) (hc : 0<c) :
    ∃ C : ℝ, 0<C ∧ ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D≥D₀, ∀ j : Fin 3, ∀ n : ℕ,
      0<n → Real.log n≤(201/400:ℝ)*Real.log (lemma23PaperP D) →
      ‖lemma83Lambda (lemma83PaperBeta D c) n (1-lemma83PaperBeta D c j) /
        (((Nat.totient n:ℝ)/(n:ℝ))^2 : ℂ)-1‖ ≤
        C*(1+Real.log (Real.log (lemma23PaperP D)))^2/Real.log (lemma23PaperP D) :=
  paper_relative_error_uniform c hc

end ZhangLS.Spec.FixedHLambdaReplacement

set_option pp.all true
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners : Array Name := #[`ZhangLS.Spec.FixedHLambdaReplacementLocal,
    `ZhangLS.Spec.FixedHLambdaReplacement, `audit.FixedHLambdaReplacementRegression]
  let mut counts : Array Nat := #[0,0,0]
  for (n,ci) in env.constants do
    let owner := match env.getModuleIdxFor? n with
      | some idx => env.header.moduleNames[idx]!
      | none => env.mainModule
    for i in [:owners.size] do
      if owner == owners[i]! then
        counts := counts.set! i (counts[i]!+1)
        let axs ← collectAxioms n
        unless axs.all (fun a => a == ``propext || a == ``Classical.choice || a == ``Quot.sound) do
          throwError "Nonstandard axiom {n}: {axs}"
        logInfo m!"OWNER {owner} DECL {n} AXIOMS {axs}"
        logInfo m!"OWNED_TYPE {n} {ci.type}"
  for i in [:owners.size] do
    unless counts[i]! > 0 do throwError "Empty module audit {owners[i]!}"
    logInfo m!"MODULE {owners[i]!} COUNT {counts[i]!}"
