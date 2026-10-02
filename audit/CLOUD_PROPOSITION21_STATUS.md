# Cloud milestone: original Proposition 2.1

`proposition21_proved : Proposition21Target` proves the paper's original bound for Psi2, the complement of the genuine Psi1 inside Psi, under normalized(A). It uses the separately proved original Lemmas3.4,3.5,3.6 through their actual three-bad-family union estimate. Positive absolute C and natural threshold D0 precede every modulus and character.

Psi1 is defined with actual `Lemma23InPsi1`. Psi2 is represented by filtering the actual ambient family with its negation; `proposition21_psi2_is_complement` explicitly proves equality to the set-theoretic Psi minus Psi1. This avoids a Lean dependent-index DecidableEq mismatch without changing the mathematical set. No zero-location surrogate, weakened condition or extra mean bound is introduced.

Verified2026-10-02, Linux x86_64, pinned Lean4.30.0:
- New module and required dependencies build PASS (4639 jobs)
- Five original-target/complement/membership/union regressions PASS without warnings
- All five theorem interfaces use only propext, Classical.choice, Quot.sound
- Independent paper-to-Lean review accepts the exact complement representation and original uniform bound, paper p6 and pp15–16
- Fresh full lake build PASS (4911 jobs), including Spec and full-project aggregates
- Import coverage659 Spec/924 full-project; source structure and placeholder checks PASS for1019 Lean files
- Strict heuristic audit retains360 reviewed/historical candidates and nonzero exit; no new candidate from this module

Source hashes and complete new axiom output accompany this report. This is not a claim that every old Spec source and old regression has now undergone a separate fresh traversal. Formal extraction of effective constants is a separate global obligation. The ledger is28/51 completed; literal5.6,8.1 and8.3 remain in progress.
