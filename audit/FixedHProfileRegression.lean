import ZhangLS.Spec.FixedHProfileAdmissible

/-! Literal-object regressions and an active axiom audit of every owned declaration. -/
set_option autoImplicit false
namespace ZhangLS.Spec.FixedHProfile
open Set Function
open scoped ContDiff

example (v : ℝ) : beta v =
    if 0 < v ∧ v < 1 then Real.exp (-1 / (v * (1 - v))) else 0 := rfl

example : beta 0 = 0 ∧ beta 1 = 0 ∧ beta (1 / 2) = Real.exp (-4) := by
  exact ⟨by norm_num [beta], by norm_num [beta], beta_midpoint⟩

example : ContDiff ℝ ∞ beta ∧ HasCompactSupport beta :=
  ⟨beta_contDiff, beta_hasCompactSupport⟩

example (v : ℝ) : F0 v = iteratedDeriv 3 beta v /
    sSup (Set.range (fun u => |iteratedDeriv 3 beta u|)) := rfl

example : 0 < normalization ∧ ∃ v : ℝ, F0 v ≠ 0 := ⟨normalization_pos, F0_not_zero⟩

example (x : ℝ) : f x = F0 (2000 * (x - 251 / 500)) := rfl

example : (201 / 400 : ℝ) - 251 / 500 = 1 / 2000 := by norm_num

example : f (251 / 500) = 0 ∧ f (201 / 400) = 0 := f_endpoints

example (x : ℝ) : |F0 x| ≤ 1 ∧ |f x| ≤ 1 := ⟨F0_abs_le_one x, f_abs_le_one x⟩

example : fixedLambda =
    (16000 / Real.pi) * (∫ v in (0 : ℝ)..1, |deriv F0 v| ^ 2) +
      (11 * Real.pi / 250) * (∫ v in (0 : ℝ)..1, |F0 v| ^ 2) := rfl

example : 0 < fixedLambda := fixedLambda_pos

example {D : ℕ} (χ : RealPrimitiveCharacter D) (P : ℝ) :
    h χ P 0 = 0 ∧ ∀ n : ℕ, ‖h χ P n‖ ≤ 1 := ⟨h_zero χ P, h_norm_le_one χ P⟩

example {D n : ℕ} (χ : RealPrimitiveCharacter D) {P : ℝ} (hP : 1 < P)
    (hn : h χ P n ≠ 0) :
    Real.exp ((251 / 500) * Real.log P) < (n : ℝ) ∧
      (n : ℝ) < Real.exp ((201 / 400) * Real.log P) :=
  (h_support_window χ hP hn).2

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hL : 3 ≤ lemma23PaperL D) :
    (∀ n : ℕ, ‖h χ (lemma23PaperP D) n‖ ≤ 1) ∧
      ∀ n : ℕ, lemma23PaperP D * lemma56PaperT D ^ (-2 : ℤ) ≤ (n : ℝ) →
        h χ (lemma23PaperP D) n = 0 := h_paper_admissible χ hL

example : ∃ D₀ : ℕ, 2 ≤ D₀ ∧ ∀ D : ℕ, D₀ ≤ D →
    ∀ χ : RealPrimitiveCharacter D,
      Lemma81AdmissibleSequence D 1 (h χ (lemma23PaperP D)) := h_paper_admissible_eventually

end ZhangLS.Spec.FixedHProfile

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := (env.constants.toList.map Prod.fst).filter fun n =>
    n.toString.startsWith "ZhangLS.Spec.FixedHProfile." || n.toString.contains "FixedHProfile"
  for n in names do
    let axioms ← collectAxioms n
    for ax in axioms do
      unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
        throwError "Nonstandard axiom {ax} in {n}"
    logInfo m!"OWNED {n}"
    elabCommand (← `(command| #print axioms $(mkIdent n)))
  logInfo m!"OWNED_DECLARATION_COUNT {names.length}"
