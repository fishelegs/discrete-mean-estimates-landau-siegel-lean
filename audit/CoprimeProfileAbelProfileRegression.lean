import ZhangLS.Spec.CoprimeProfileAbelProfile
set_option autoImplicit false
namespace ZhangLS.Spec.CoprimeProfileAbel
open MeasureTheory Set

-- The literal original window is retained, including its width.
example : (201 / 400 : ℝ) - 251 / 500 = 1 / 2000 := by norm_num

-- The actual totient/n² weight is present, with no density substituted into a term.
example (K : ℝ → ℝ) (B : ℝ) :
    (if (2 : ℕ).Coprime 1 then ((2 : ℕ).totient : ℝ) / (2 : ℝ) ^ 2 else 0) *
      K (Real.log 2 / B) = (1 / 4) * K (Real.log 2 / B) := by
  have hp : Nat.totient 2 = 1 := by norm_num [Nat.totient]; decide
  rw [if_pos (by decide), hp]
  norm_num

-- Endpoint logarithms and the exact B normalization.
example (K : ℝ → ℝ) {a B : ℝ} (hB : 0 < B) :
    profileWeight K B (Real.exp (a * B)) = K a / Real.exp (a * B) := by
  unfold profileWeight
  rw [Real.log_exp, mul_div_cancel_right₀ a hB.ne']

example {a b B : ℝ} (hB : 0 < B) (hab : a ≤ b) :
    (∫ t in Real.exp (a * B)..Real.exp (b * B), profileWeight (fun _ => 1) B t) =
      B * (b - a) := by
  have h := profileWeight_integral (fun _ => 1) (fun _ => 0)
    (fun _ => hasDerivAt_const _ _) hB hab
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_one] using h

-- Both inclusive profile boundaries vanish, rather than being omitted.
example (K : ℝ → ℝ) {a b : ℝ} (hc : Continuous K)
    (hs : Function.support K ⊆ Set.Icc a b) : K a = 0 ∧ K b = 0 :=
  continuous_supported_endpoints hc hs

example (K : ℝ → ℝ) (B : ℝ)
    (hs : Function.support K ⊆ Set.Icc (251 / 500 : ℝ) (201 / 400)) :
    profileWeight K B 1 = 0 := by
  have hz : K 0 = 0 := by
    by_contra hne
    have h := (hs hne).1
    norm_num at h
  simp [profileWeight, hz]

-- Weak upper endpoint and strict lower endpoint remain explicit in the actual sum.
example (D : ℕ) (K : ℝ → ℝ) {a b B : ℝ} (hB : 0 < B)
    (hc : Continuous K) (hs : Function.support K ⊆ Set.Icc a b) :
    weightedProfileSum D K B b =
      ∑ n ∈ Finset.Ioc ⌊Real.exp (a * B)⌋₊ ⌊Real.exp (b * B)⌋₊,
        profileWeight K B n * coefficient D n :=
  weightedProfileSum_eq_interval D K hB hs (continuous_supported_endpoints hc hs).1

-- A degenerate profile is accepted at the lowest legal P range.
example {D : ℕ} (hD : 0 < D) {P : ℝ} (hP : 1 < P) :
    |weightedProfileSum D (fun _ => 0) (Real.log P) (201 / 400) -
      mainConstant D * Real.log P *
        (∫ _u in (251 / 500 : ℝ)..(201 / 400), (0 : ℝ))| ≤ 0 := by
  simp [weightedProfileSum]

end ZhangLS.Spec.CoprimeProfileAbel

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := (env.constants.toList.map Prod.fst).filter fun n =>
    n.toString.startsWith "ZhangLS.Spec.CoprimeProfileAbel." ||
      n.toString.contains "CoprimeProfileAbel"
  for n in names do
    let axioms ← collectAxioms n
    for ax in axioms do
      unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
        throwError "Nonstandard axiom {ax} in {n}"
    logInfo m!"OWNED {n}"
    elabCommand (← `(command| #print axioms $(mkIdent n)))
