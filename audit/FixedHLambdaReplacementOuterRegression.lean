import ZhangLS.Spec.FixedHLambdaReplacementOuter
set_option autoImplicit false
namespace ZhangLS.Spec.FixedHLambdaReplacement
open Complex Finset

lemma outer_regression_zero_profile {D : ℕ} (χ : RealPrimitiveCharacter D) (c : ℝ) (j : Fin 3) :
    outerSum χ c j (fun _=>0)=0 ∧ baselineOuterSum χ (fun _=>0)=0 := by
  simp [outerSum,baselineOuterSum]

lemma outer_regression_n_one {A : ℂ} {e : ℝ} (he : 0≤e) (h : ‖A-1‖≤e) :
    ‖A/(Nat.totient 1:ℂ)-(Nat.totient 1:ℂ)/(1:ℂ)^2‖≤e*(1:ℝ)⁻¹ := by
  simpa using weighted_factor_error (A := A) (n := 1) (by norm_num) he (by simpa using h)

lemma outer_regression_harmonic {B : ℝ} (hB : 1≤B) :
    (harmonic ⌊Real.exp ((201/400:ℝ)*B)⌋₊:ℝ)≤2*B := cutoff_harmonic hB

lemma outer_regression_scalar {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1<D)
    (hL : 2≤lemma23PaperL D) {B : ℝ} (hB : 0<B) :
    ‖(LDerivAtOne χ)^2/(B:ℂ)^2‖≤(16*Real.exp 1)^2*lemma23PaperL D^4/B^2 :=
  scalar_bound χ hD hL hB

lemma outer_regression_actual_uniform (c M : ℝ) (hc : 0<c) (hM : 0≤M) :
    ∃ C : ℝ, 0<C ∧ ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D≥D₀,
      ∀ χ : RealPrimitiveCharacter D, ∀ j : Fin 3, ∀ K : ℝ → ℂ,
      Function.support K⊆Set.Icc (251/500:ℝ) (201/400:ℝ) →
      (∀ t∈Set.Icc (251/500:ℝ) (201/400:ℝ), ‖K t‖≤M) →
      ‖outerSum χ c j K-baselineOuterSum χ K‖≤
        C*lemma23PaperL D^4*(1+Real.log (Real.log (lemma23PaperP D)))^2 /
          (Real.log (lemma23PaperP D))^2 := outer_error_uniform c M hc hM

end ZhangLS.Spec.FixedHLambdaReplacement

set_option pp.all true
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners : Array Name := #[`ZhangLS.Spec.FixedHLambdaReplacementLocal,
    `ZhangLS.Spec.FixedHLambdaReplacement, `ZhangLS.Spec.FixedHLambdaReplacementOuter,
    `audit.FixedHLambdaReplacementOuterRegression]
  let mut counts : Array Nat := #[0,0,0,0]
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
